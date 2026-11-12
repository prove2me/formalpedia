-- Prove2me | Definitions.Def_UnifLattice_FastVf_VectorCommitment
-- name    : UnifLattice_FastVf_VectorCommitment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:18:35.486783+00:00
-- url     : https://prove2.me/theorems/e760116c-5a24-47fe-ade4-9e7c7c6ee691
-- title:
--   Com^v and Ver^v of Construction 3.4, the blocks V_i of V^v_L and the basis commitments Ŵ_k = Com^v(pp, e_k)
-- statement:
--   Fix $m\in\mathbb N$ and **commitment parameters** $pp=(W,V)$ with $W,V\in\{0,1\}^{m\times 2m^3}$. Let $e_1\in\{0,1\}^{2m^2}$ be the first standard basis vector and $J_{2m}=I_{2m}\otimes\mathrm{vec}(I_m)\in\{0,1\}^{2m^3\times 2m}$. Construction 3.4 (pp. 18–19) defines, for $L=2^\ell$:
--
--   - $\mathrm{Com}^v(pp,x)$ for $x\in\{0,1\}^L$: if $L=1$, $C_x=W(x_1e_1\otimes I_m)\in\mathbb Z^{m\times m}$; if $L\ge2$, parse $x=\binom{x_0}{x_1}$ with $x_0$ the top half, let $C_{x_b}=\mathrm{Com}^v(pp,x_b)$, $\hat c_x=\mathrm{vec}([C_{x_0}\mid C_{x_1}])\in\mathbb Z^{2m^2}$ and output $C_x=W(\hat c_x\otimes I_m)$.
--   - $\mathrm{Ver}^v(pp,1^L)$: if $L=1$, $V^v_1=V(e_1\otimes I_m)$; if $L\ge2$,
--   $$V^v_L=V J_{2m}\,(I_2\otimes V^v_{L/2})\in\mathbb Z^{m\times Lm}.$$
--
--   The blocks of $V^v_L=[V_1\mid\cdots\mid V_L]$ are $V_i\in\mathbb Z^{m\times m}$ (Construction 3.8), and the **basis commitments** are $\widehat W_k=\mathrm{Com}^v(pp,e_k)$ for the standard basis vectors $e_k\in\{0,1\}^L$ (Lemma 3.5). All matrices are integer matrices; nothing is reduced modulo $q$.
--
--   These are the matrices whose $L^3$-fold combination is the verification matrix $V_f$ of the goal.
--
--   **Formalization Note.** `comV pp ℓ x` and `verV pp ℓ` are defined by exactly these recursions on $\ell$ (not by the closed forms of Lemma 3.10). Index sets are product types with the paper's lexicographic flattenings: $[2m^2]$ is `T m = (Fin 2 × Fin m) × Fin m` (block, column, row of $[C_{x_0}\mid C_{x_1}]$), $[2m^3]$ is `Col m = Fin 2 × Fin m × Fin m × Fin m`, read as $[2m^2]\times[m]$ in $W(c\otimes I_m)$ (`mulKronI`) and as $[2m]\times[m^2]$ in $VJ_{2m}$ (`VJ`); both readings are reassociations, which preserve the flattening. The columns of $V^v_L$ are `Fin (2^ℓ) × Fin m` (block $i-1$, column). Binary entries are `Fin 2`, cast to `ℤ` (`Wz`, `Vz`). `blockV pp ℓ i` is $V_{i+1}$ and `basisCom pp ℓ k` is $\widehat W_{k+1}$ for 0-based `i, k`.
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), pp. 18-19, Construction 3.4; p. 19, Lemma 3.5 (Ŵ_k); p. 20, Construction 3.8 (blocks V_i)

import Mathlib
import Definitions.Def_UnifLattice_FastVf_Notation

open Matrix
open scoped Kronecker

/-!
# The vector commitment of Construction 3.4: `Com^v`, `Ver^v`, the blocks `V_i` and the basis
commitments `Ŵ_k`

Wee, Wichs, Wu, *SNARGs and ABE for Uniform Computations via Lattice Encodings*, STOC 2027
submission (manuscript sha256 fd77662e…), pp. 18–19, Construction 3.4; p. 19, Lemma 3.5 (`Ŵ_k`);
p. 20, Construction 3.8 (the parse `V^v_L = [V_1 | ⋯ | V_L]`).

Index types (all flattenings are the lexicographic ones of the paper's Kronecker products):
* `T m = (Fin 2 × Fin m) × Fin m` is `[2m²]`, the index set of `ĉ_x = vec([C_{x₀} | C_{x₁}])`:
  (column of `[C_{x₀} | C_{x₁}]` = (block, column), row).
* `Col m = Fin 2 × Fin m × Fin m × Fin m` is `[2m³]`, the column index of `W` and `V`. It is read
  as `T m × Fin m` in `W(c ⊗ I_m)` and as `(Fin 2 × Fin m) × (Fin m × Fin m)` in `V J_{2m}`; both
  are reassociations, which preserve the lexicographic flattening.
* The columns of `V^v_L ∈ ℤ^{m × Lm}` are `Fin (2^ℓ) × Fin m` (block, column in the block).

All matrices are integer matrices; nothing is reduced mod `q`.
-/

namespace UnifLattice.FastVf

/-- `[2m²]`: the index set of `vec([C₀ | C₁])` for `C₀, C₁ ∈ ℤ^{m×m}`, as
((block `b`, column `c`), row `r`). -/
abbrev T (m : ℕ) : Type := (Fin 2 × Fin m) × Fin m

/-- `[2m³]`: the column index of the commitment parameters `W, V ∈ {0,1}^{m × 2m³}`. -/
abbrev Col (m : ℕ) : Type := Fin 2 × Fin m × Fin m × Fin m

/-- Commitment parameters `pp = (W, V)` with `W, V ∈ {0,1}^{m × 2m³}` (Construction 3.4). -/
structure CommitParams (m : ℕ) where
  /-- `W ∈ {0,1}^{m × 2m³}`. -/
  W : Matrix (Fin m) (Col m) (Fin 2)
  /-- `V ∈ {0,1}^{m × 2m³}`. -/
  V : Matrix (Fin m) (Col m) (Fin 2)

/-- `W` as an integer matrix. -/
def CommitParams.Wz {m : ℕ} (pp : CommitParams m) : Matrix (Fin m) (Col m) ℤ :=
  pp.W.map fun b => (b.val : ℤ)

/-- `V` as an integer matrix. -/
def CommitParams.Vz {m : ℕ} (pp : CommitParams m) : Matrix (Fin m) (Col m) ℤ :=
  pp.V.map fun b => (b.val : ℤ)

/-- The column `[2m³]` read as `[2m²] × [m]` (the rows of `c ⊗ I_m`). -/
def colOfT {m : ℕ} (q : T m × Fin m) : Col m := (q.1.1.1, q.1.1.2, q.1.2, q.2)

/-- The column `[2m³]` read as `[2m] × [m²]` (the rows of `J_{2m} = I_{2m} ⊗ vec(I_m)`). -/
def colOfJ {m : ℕ} (q : (Fin 2 × Fin m) × (Fin m × Fin m)) : Col m :=
  (q.1.1, q.1.2, q.2.1, q.2.2)

/-- `A(c ⊗ I_m) ∈ ℤ^{m×m}` for `A ∈ ℤ^{m × 2m³}` and a column vector `c ∈ ℤ^{2m²}`
(`c ⊗ I_m ∈ ℤ^{2m³ × m}`). -/
def mulKronI {m : ℕ} (A : Matrix (Fin m) (Col m) ℤ) (c : T m → ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  ((A.submatrix id colOfT) * (replicateCol Unit c ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℤ))).submatrix
    id (fun j => ((), j))

/-- The first standard basis vector `e₁ ∈ {0,1}^{2m²}` (the entry at flat position `1`, i.e.
block `0`, column `0`, row `0`). For `m = 0` it is the empty vector. -/
def e1 (m : ℕ) : T m → ℤ :=
  fun t => if t.1.1.val = 0 ∧ t.1.2.val = 0 ∧ t.2.val = 0 then 1 else 0

/-- `[C₀ | C₁] ∈ ℤ^{m × 2m}`, the horizontal concatenation of two `m × m` matrices; its column
`(b, c)` is column `c` of `C_b`. -/
def hcat2 {m : ℕ} (C : Fin 2 → Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin m) (Fin 2 × Fin m) ℤ :=
  Matrix.of fun r q => C q.1 r q.2

/-- The two halves of `x ∈ {0,1}^{2L}` (`L = 2^ℓ`): `x = (x₀; x₁)` with `x₀` the top half. -/
def half {ℓ : ℕ} (x : Fin (2 ^ (ℓ + 1)) → Fin 2) (b : Fin 2) : Fin (2 ^ ℓ) → Fin 2 :=
  fun i => x ((splitMSB ℓ).symm (b, i))

/-- `Com^v(pp, x)` of Construction 3.4 (p. 19), by its recursion, for `x ∈ {0,1}^L`, `L = 2^ℓ`:
* `L = 1`: `C_x = W(x₁ e₁ ⊗ I_m)`;
* `L ≥ 2`: parse `x = (x₀; x₁)`, `C_{x_b} = Com^v(pp, x_b)`, `ĉ_x = vec([C_{x₀} | C_{x₁}])`,
  and `C_x = W(ĉ_x ⊗ I_m)`. -/
def comV {m : ℕ} (pp : CommitParams m) : (ℓ : ℕ) → (Fin (2 ^ ℓ) → Fin 2) → Matrix (Fin m) (Fin m) ℤ
  | 0, x => mulKronI pp.Wz (fun t => ((x ⟨0, by norm_num⟩).val : ℤ) * e1 m t)
  | ℓ + 1, x => mulKronI pp.Wz (vec (hcat2 fun b => comV pp ℓ (half x b)))

/-- `V J_{2m} = [P₀ | P₁] ∈ ℤ^{m × 2m}`, with columns indexed by (block `b`, column). -/
def VJ {m : ℕ} (pp : CommitParams m) : Matrix (Fin m) (Fin 2 × Fin m) ℤ :=
  ((pp.Vz.submatrix id colOfJ) * J (Fin 2 × Fin m) m).submatrix id (fun q => (q, ()))

/-- `Ver^v(pp, 1^L) = V^v_L ∈ ℤ^{m × Lm}` of Construction 3.4 (p. 19), by its recursion:
* `L = 1`: `V^v_1 = V(e₁ ⊗ I_m)`;
* `L ≥ 2`: `V^v_L = V J_{2m} (I₂ ⊗ V^v_{L/2})`.
Columns are (block `i - 1 ∈ Fin (2^ℓ)`, column in the block); the block index of the column
`(b, (i', c))` of `I₂ ⊗ V^v_{L/2}` is `b·L/2 + i'` (most significant bit `b`). -/
def verV {m : ℕ} (pp : CommitParams m) : (ℓ : ℕ) → Matrix (Fin m) (Fin (2 ^ ℓ) × Fin m) ℤ
  | 0 => (mulKronI pp.Vz (e1 m)).submatrix id (fun q => q.2)
  | ℓ + 1 =>
      (VJ pp * ((1 : Matrix (Fin 2) (Fin 2) ℤ) ⊗ₖ verV pp ℓ)).submatrix id
        (fun q => ((splitMSB ℓ q.1).1, ((splitMSB ℓ q.1).2, q.2)))

/-- The block `V_i ∈ ℤ^{m×m}` of `V^v_L = [V_1 | ⋯ | V_L]` (Construction 3.8, p. 20), for the
0-based block index `i`. -/
def blockV {m : ℕ} (pp : CommitParams m) (ℓ : ℕ) (i : Fin (2 ^ ℓ)) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun r c => verV pp ℓ r (i, c)

/-- The `k`-th standard basis vector `e_k ∈ {0,1}^L` (0-based `k`). -/
def basisVec {ℓ : ℕ} (k : Fin (2 ^ ℓ)) : Fin (2 ^ ℓ) → Fin 2 :=
  fun i => if i = k then 1 else 0

/-- The basis commitment `Ŵ_k = Com^v(pp, e_k) ∈ ℤ^{m×m}` (Lemma 3.5, Construction 3.8). -/
def basisCom {m : ℕ} (pp : CommitParams m) (ℓ : ℕ) (k : Fin (2 ^ ℓ)) : Matrix (Fin m) (Fin m) ℤ :=
  comV pp ℓ (basisVec k)

end UnifLattice.FastVf


