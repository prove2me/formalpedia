-- Prove2me | Definitions.Def_UnifLattice_FastVf_ProofMatrices
-- name    : UnifLattice_FastVf_ProofMatrices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:20:07.528461+00:00
-- url     : https://prove2.me/theorems/495c6270-5cc7-41bf-a8ff-44f8d536fe31
-- title:
--   P_b, P̂_b, V_leaf, Ŵ_leaf of Lemma 3.10 and F_{τ,b}, r of Eq. (3.11)
-- statement:
--   For commitment parameters $pp=(W,V)$ (Lemma 3.10, p. 22): $[P_0\mid P_1]=VJ_{2m}\in\mathbb Z^{m\times 2m}$ with $P_0$ the first $m$ columns; $V_{\mathrm{leaf}}=V(e_1\otimes I_m)$ and $\widehat W_{\mathrm{leaf}}=W(e_1\otimes I_m)$ in $\{0,1\}^{m\times m}$; and $[\widehat P_0\mid\widehat P_1]\in\{0,1\}^{m^2\times 2m^2}$ is the matrix whose $t$-th column is $\mathrm{vec}(W(e_t\otimes I_m))$ for $t\in[2m^2]$. For a reading order $\pi$ of $[3\ell]$ (Eq. (3.11), p. 25),
--   $$F_{\tau,b}=\begin{cases}(I_m\otimes P_b)\otimes I_{m^2}\otimes I_{m^2}&\pi(\tau)\le\ell,\\ I_{m^2}\otimes(I_m\otimes P_b)\otimes I_{m^2}&\ell<\pi(\tau)\le2\ell,\\ I_{m^2}\otimes I_{m^2}\otimes\widehat P_b&\pi(\tau)>2\ell,\end{cases}\qquad r=\mathrm{vec}(V_{\mathrm{leaf}})\otimes\mathrm{vec}(V_{\mathrm{leaf}})\otimes\mathrm{vec}(\widehat W_{\mathrm{leaf}}).$$
--
--   These are the factors of the subset products of Lemma 3.10 and of the product formula (3.14).
--
--   **Formalization Note.** $b\in\{0,1\}$ is `Fin 2`; $\widehat P_b$ consists of the columns $t=((b,c),r)$ of block $b$, indexed by $(c,r)$, the (column, row) index of `vec`. With 0-based positions the three cases of $F$ are `π τ < ℓ`, `ℓ ≤ π τ < 2ℓ` and `2ℓ ≤ π τ`. Kronecker products associate to the left (`K6 m`).
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), p. 22, Lemma 3.10; p. 25, Eq. (3.11)

import Mathlib
import Definitions.Def_UnifLattice_FastVf_Notation
import Definitions.Def_UnifLattice_FastVf_VectorCommitment
import Definitions.Def_UnifLattice_FastVf_QuadraticCommitment

open Matrix
open scoped Kronecker

/-!
# The matrices `P_b`, `P̂_b`, `V_leaf`, `Ŵ_leaf` of Lemma 3.10 and `F_{τ,b}`, `r` of Eq. (3.11)

Wee, Wichs, Wu, *SNARGs and ABE for Uniform Computations via Lattice Encodings*, STOC 2027
submission (manuscript sha256 fd77662e…), p. 22 (Lemma 3.10), p. 25 (Eq. (3.11)).

Bits `b ∈ {0, 1}` are `Fin 2`; the reading order `π` of `[3ℓ]` and its positions are 0-based, so
the paper's cases `π(τ) ≤ ℓ`, `ℓ < π(τ) ≤ 2ℓ`, `π(τ) > 2ℓ` are `π τ < ℓ`, `ℓ ≤ π τ < 2ℓ`,
`2ℓ ≤ π τ` here.
-/

namespace UnifLattice.FastVf

/-- `P_b ∈ ℤ^{m×m}` with `[P₀ | P₁] = V J_{2m} ∈ ℤ^{m × 2m}` (Lemma 3.10): `P₀` is the first `m`
columns, `P₁` the last `m`. -/
def P {m : ℕ} (pp : CommitParams m) (b : Fin 2) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun r c => VJ pp r (b, c)

/-- `V_leaf = V(e₁ ⊗ I_m) ∈ {0,1}^{m×m}` (Lemma 3.10). -/
def Vleaf {m : ℕ} (pp : CommitParams m) : Matrix (Fin m) (Fin m) ℤ := mulKronI pp.Vz (e1 m)

/-- `Ŵ_leaf = W(e₁ ⊗ I_m) ∈ {0,1}^{m×m}` (Lemma 3.10). -/
def Wleaf {m : ℕ} (pp : CommitParams m) : Matrix (Fin m) (Fin m) ℤ := mulKronI pp.Wz (e1 m)

/-- `P̂_b ∈ {0,1}^{m² × m²}` (Lemma 3.10): `[P̂₀ | P̂₁] ∈ {0,1}^{m² × 2m²}` is the matrix whose
`t`-th column is `vec(W(e_t ⊗ I_m))` for `t ∈ [2m²]`; `P̂_b` consists of the columns
`t = ((b, c), r)` of block `b`, indexed by `(c, r)`. -/
def Phat {m : ℕ} (pp : CommitParams m) (b : Fin 2) : Matrix (Fin m × Fin m) (Fin m × Fin m) ℤ :=
  Matrix.of fun p q => vec (mulKronI pp.Wz (Pi.single ((b, q.1), q.2) 1)) p

/-- `F_{τ,b} ∈ ℤ^{m⁶ × m⁶}` of Eq. (3.11) (p. 25), for the reading order `π`:
`(I_m ⊗ P_b) ⊗ I_{m²} ⊗ I_{m²}` if step `τ` reads a bit of `i`,
`I_{m²} ⊗ (I_m ⊗ P_b) ⊗ I_{m²}` if it reads a bit of `j`, and
`I_{m²} ⊗ I_{m²} ⊗ P̂_b` if it reads a bit of `k`. -/
def F {m : ℕ} (pp : CommitParams m) (ℓ : ℕ) (π : Equiv.Perm (Fin (3 * ℓ))) (τ : Fin (3 * ℓ))
    (b : Fin 2) : Matrix (K6 m) (K6 m) ℤ :=
  if (π τ).val < ℓ then
    ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ P pp b) ⊗ₖ (1 : Matrix (Fin m × Fin m) (Fin m × Fin m) ℤ)
      ⊗ₖ (1 : Matrix (Fin m × Fin m) (Fin m × Fin m) ℤ)
  else if (π τ).val < 2 * ℓ then
    (1 : Matrix (Fin m × Fin m) (Fin m × Fin m) ℤ) ⊗ₖ ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ P pp b)
      ⊗ₖ (1 : Matrix (Fin m × Fin m) (Fin m × Fin m) ℤ)
  else
    (1 : Matrix (Fin m × Fin m) (Fin m × Fin m) ℤ) ⊗ₖ (1 : Matrix (Fin m × Fin m) (Fin m × Fin m) ℤ)
      ⊗ₖ Phat pp b

/-- `r = vec(V_leaf) ⊗ vec(V_leaf) ⊗ vec(Ŵ_leaf) ∈ {0,1}^{m⁶}` (Eq. (3.11)). -/
def r {m : ℕ} (pp : CommitParams m) : K6 m → ℤ :=
  kron (kron (vec (Vleaf pp)) (vec (Vleaf pp))) (vec (Wleaf pp))

end UnifLattice.FastVf


