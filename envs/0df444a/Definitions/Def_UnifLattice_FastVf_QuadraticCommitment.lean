-- Prove2me | Definitions.Def_UnifLattice_FastVf_QuadraticCommitment
-- name    : UnifLattice_FastVf_QuadraticCommitment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:19:21.292503+00:00
-- url     : https://prove2.me/theorems/3029e3a9-5016-4631-8df3-bbb7f868dcf3
-- title:
--   Wiring functions (Definition 3.6), the verification matrix V_f = Ver^q(pp, f) of Construction 3.8 and v_g of Eq. (3.10)
-- statement:
--   A function $f=(f_1,\dots,f_L):\{0,1\}^L\to\{0,1\}^L$ is **quadratic with wiring function** $g:[L]^3\to\{-1,0,1\}$ if (Definition 3.6, p. 20)
--   $$f_k(x)=\sum_{i,j\in[L]}g(i,j,k)\,x_ix_j\qquad\text{for all }k\in[L],\ x\in\{0,1\}^L.$$
--   For $L=2^\ell$, commitment parameters $pp$, the blocks $V_i$ of $\mathrm{Ver}^v(pp,1^L)$ and the basis commitments $\widehat W_k$ of Construction 3.4, the **verification matrix** of Construction 3.8 (Eq. (3.3), p. 20; Eq. (3.5), p. 21) is
--   $$V_f=\mathrm{Ver}^q(pp,f)=\sum_{i,j,k\in[L]}g(i,j,k)\,(I_m\otimes\mathrm{vec}(V_i))\,V_j\,\widehat W_k\in\mathbb Z^{m^3\times m}.$$
--   In the proof of Theorem 3.13 (Eq. (3.10), p. 25) the paper also uses
--   $$v_g=\sum_{i,j,k\in[L]}g(i,j,k)\cdot\mathrm{vec}(V_i)\otimes\mathrm{vec}(V_j)\otimes\mathrm{vec}(\widehat W_k)\in\mathbb Z^{m^6}.$$
--
--   $V_f$ is the matrix the verifier needs; computing it from this sum takes time linear in the number $L^3$ of terms.
--
--   **Formalization Note.** $\mathrm{Ver}^q$ takes $f$ together with $g$, and its output depends only on $g$ (a quadratic $f$ can have several wiring functions), so `verQ pp ℓ g` takes the wiring function, as a function `Fin (2^ℓ) → Fin (2^ℓ) → Fin (2^ℓ) → ℤ` (0-based indices); `IsWiringFunction L f g` is Definition 3.6. The sum defining `verQ` is the paper's $L^3$-term sum, not a product formula. Rows of $I_m\otimes\mathrm{vec}(A)$ and of $V_f$ are `Fin m × (Fin m × Fin m)` (block, then the (column, row) index of `vec A`); $\mathbb Z^{m^6}$ is indexed by `K6 m`.
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), p. 20, Definition 3.6 and Construction 3.8 (Eq. (3.3)); p. 21, Eq. (3.5); p. 25, Eq. (3.10)

import Mathlib
import Definitions.Def_UnifLattice_FastVf_Notation
import Definitions.Def_UnifLattice_FastVf_VectorCommitment

open Matrix
open scoped Kronecker

/-!
# Quadratic functions and wiring functions (Definition 3.6), the verification matrix
`V_f = Ver^q(pp, f)` of Construction 3.8 (Eq. (3.3) = Eq. (3.5)), and `v_g` of Eq. (3.10)

Wee, Wichs, Wu, *SNARGs and ABE for Uniform Computations via Lattice Encodings*, STOC 2027
submission (manuscript sha256 fd77662e…), p. 20 (Definition 3.6, Construction 3.8, Eq. (3.3)),
p. 21 (Eq. (3.5)), p. 25 (Eq. (3.10)).

`Ver^q(pp, f)` receives a quadratic function `f` *with* a wiring function `g`, and its output is a
function of `g` only (a quadratic `f` may have several wiring functions). It is therefore defined
as `verQ pp ℓ g`. Indices `i, j, k ∈ [L]` are 0-based (`Fin (2^ℓ)`). The rows of
`I_m ⊗ vec(A) ∈ ℤ^{m³ × m}`, hence of `V_f ∈ ℤ^{m³ × m}`, are `Fin m × (Fin m × Fin m)`
(`vec(A)` is indexed by (column, row)).
-/

namespace UnifLattice.FastVf

/-- Definition 3.6 (p. 20): `g : [L]³ → {−1, 0, 1}` is a wiring function of the quadratic function
`f = (f_1, …, f_L) : {0,1}^L → {0,1}^L` when `f_k(x) = Σ_{i,j ∈ [L]} g(i, j, k) · x_i x_j` for all
`k ∈ [L]` and `x ∈ {0,1}^L`. -/
def IsWiringFunction (L : ℕ) (f : (Fin L → Fin 2) → Fin L → Fin 2)
    (g : Fin L → Fin L → Fin L → ℤ) : Prop :=
  (∀ i j k, g i j k = -1 ∨ g i j k = 0 ∨ g i j k = 1) ∧
    ∀ (x : Fin L → Fin 2) (k : Fin L),
      ((f x k).val : ℤ) = ∑ i, ∑ j, g i j k * (x i).val * (x j).val

/-- `I_m ⊗ vec(A) ∈ ℤ^{m³ × m}` for `A ∈ ℤ^{m×m}`; rows `(a, (c, r))` with `(c, r)` the
(column, row) index of `vec(A)`. -/
def kronVecI {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin m × (Fin m × Fin m)) (Fin m) ℤ :=
  ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ replicateCol Unit (vec A)).submatrix
    id (fun j => (j, ()))

/-- The verification matrix of Construction 3.8 (Eq. (3.3), p. 20; Eq. (3.5), p. 21):
`V_f = Ver^q(pp, f) = Σ_{i,j,k ∈ [L]} g(i, j, k) · (I_m ⊗ vec(V_i)) V_j Ŵ_k ∈ ℤ^{m³ × m}`,
with `V^v_L = Ver^v(pp, 1^L) = [V_1 | ⋯ | V_L]` and `Ŵ_k = Com^v(pp, e_k)`, for `L = 2^ℓ` and a
wiring function `g` of `f`. The sum has `L³` terms. -/
def verQ {m : ℕ} (pp : CommitParams m) (ℓ : ℕ) (g : Fin (2 ^ ℓ) → Fin (2 ^ ℓ) → Fin (2 ^ ℓ) → ℤ) :
    Matrix (Fin m × (Fin m × Fin m)) (Fin m) ℤ :=
  ∑ i, ∑ j, ∑ k, g i j k • (kronVecI (blockV pp ℓ i) * blockV pp ℓ j * basisCom pp ℓ k)

/-- `ℤ^{m⁶}` as an index type: `vec(A) ⊗ vec(B) ⊗ vec(C)` for `A, B, C ∈ ℤ^{m×m}`. -/
abbrev K6 (m : ℕ) : Type := ((Fin m × Fin m) × (Fin m × Fin m)) × (Fin m × Fin m)

/-- Eq. (3.10) (p. 25): `v_g = Σ_{i,j,k ∈ [L]} g(i, j, k) · vec(V_i) ⊗ vec(V_j) ⊗ vec(Ŵ_k) ∈ ℤ^{m⁶}`. -/
def vg {m : ℕ} (pp : CommitParams m) (ℓ : ℕ) (g : Fin (2 ^ ℓ) → Fin (2 ^ ℓ) → Fin (2 ^ ℓ) → ℤ) :
    K6 m → ℤ :=
  ∑ i, ∑ j, ∑ k, g i j k •
    kron (kron (vec (blockV pp ℓ i)) (vec (blockV pp ℓ j))) (vec (basisCom pp ℓ k))

end UnifLattice.FastVf


