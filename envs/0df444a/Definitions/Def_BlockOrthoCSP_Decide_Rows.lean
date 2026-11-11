-- Prove2me | Definitions.Def_BlockOrthoCSP_Decide_Rows
-- name    : BlockOrthoCSP_Decide_Rows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:12:30.713579+00:00
-- url     : https://prove2.me/theorems/5a8c6a55-8407-4e79-b788-7d8a0d726dda
-- title:
--   Rows, row equivalence, block-rank one, block-orthogonal functions (Definition F.2.1), $\Phi_F$, $\Omega_F$ and type-partition maps
-- statement:
--   For $F : D^{r} \to \mathbb C$ with $r = j+1 \ge 2$, the **row** indexed by $x \in D^{j}$ is $F(x,*) = (F(x,z))_{z \in D}$: the column is the last coordinate. Two row indices are **row-equivalent**, $x \sim_F y$, when both rows are nonzero and linearly dependent over $\mathbb C$ (F.6).
--
--   $F$ is **block-rank one** if any two nonzero rows have positively proportional magnitude vectors $|u| = c|v|$, $c>0$, or disjoint supports. Two nonzero rows $u, v$ with proportional magnitudes are **block-orthogonal** if for every level $m>0$ of $|u|$
--   $$\sum_{z : |u_z| = m} u_z\,\overline{v_z} = 0. \qquad (F.7)$$
--   $F$ is **block-orthogonal** (Definition F.2.1) if it is block-rank one and every two nonzero rows with proportional magnitude vectors are linearly dependent or block-orthogonal.
--
--   The **support** is $\Phi_F = \{a : F(a) \ne 0\}$ and the **row-equivalence relation** is the $2(r-1)$-ary relation $\Omega_F = \{(x,y) \in D^{r-1}\times D^{r-1} : x \sim_F y\}$ on concatenated tuples. For $0 \le \ell \le r-1$ and $\alpha \in D^\ell$, $\mathrm{type}_F(\alpha)$ is the set of row classes containing a row index with prefix $\alpha$; the type map is a **type-partition map** if any two types of prefixes of the same length are equal or disjoint.
--
--   **Formalization Note.** Arity $r$ is written $j+1$; a row class is represented by its set of row indices (the paper's indexing of classes by $[s]$ is arbitrary); quantifying (F.7) over all $m > 0$ adds only empty sums.
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), pp. F-7, F-9, §F.2.3, Eqs. (F.6)–(F.7), Definition F.2.1, §F.2.5

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance

set_option autoImplicit false

namespace BlockOrthoCSP.Decide

open ComplexConjugate

/-- The row `F(x, ∗) = (F(x, z))_{z ∈ D}` of a function `F : D^{j+1} → ℂ`, indexed by
`x ∈ D^j`: the column is the LAST coordinate (p. F-7, §F.2.3, with `r = j + 1`). -/
def row {q j : ℕ} (G : (Fin (j + 1) → Fin q) → ℂ) (x : Fin j → Fin q) : Fin q → ℂ :=
  fun z => G (Fin.snoc x z)

/-- Row equivalence `x ∼_F y` (F.6), p. F-7: both rows are nonzero and they are linearly
dependent over `ℂ`. -/
def RowEquiv {q j : ℕ} (G : (Fin (j + 1) → Fin q) → ℂ) (x y : Fin j → Fin q) : Prop :=
  row G x ≠ 0 ∧ row G y ≠ 0 ∧ ¬ LinearIndependent ℂ ![row G x, row G y]

/-- The magnitude vectors `|u|` and `|v|` are positively proportional: `|u| = c |v|`, `c > 0`. -/
def PosProportional {q : ℕ} (u v : Fin q → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ z, ‖u z‖ = c * ‖v z‖

/-- Block-rank one (p. F-7): for every two nonzero rows, their magnitude vectors are positively
proportional or their supports are disjoint. -/
def IsBlockRankOne {q j : ℕ} (G : (Fin (j + 1) → Fin q) → ℂ) : Prop :=
  ∀ x y : Fin j → Fin q, row G x ≠ 0 → row G y ≠ 0 →
    PosProportional (row G x) (row G y) ∨
      Disjoint (Function.support (row G x)) (Function.support (row G y))

/-- Block-orthogonal vectors `u ⊥_B v`, Eq. (F.7), p. F-7: for every level set
`T_i = {z ∈ supp u : |u_z| = m_i}` of `|u|` on its support,
`∑_{z ∈ T_i} u_z · conj(v_z) = 0`. A level `m > 0` that `|u|` does not take gives an empty
sum, so quantifying over all `m > 0` is the same as over the levels `m_1 > ⋯ > m_h > 0`. -/
def BlockOrthVec {q : ℕ} (u v : Fin q → ℂ) : Prop :=
  ∀ m : ℝ, 0 < m → ∑ z ∈ Finset.univ.filter (fun z => ‖u z‖ = m), u z * conj (v z) = 0

/-- Definition F.2.1 (block-orthogonal function), p. F-7, for `F : D^{j+1} → ℂ` (arity `r = j+1`):
`F` is block-rank one and any two nonzero rows with (positively) proportional magnitude vectors
are linearly dependent or block-orthogonal in the sense of (F.7). -/
def IsBlockOrthogonal {q j : ℕ} (G : (Fin (j + 1) → Fin q) → ℂ) : Prop :=
  IsBlockRankOne G ∧
    ∀ x y : Fin j → Fin q, row G x ≠ 0 → row G y ≠ 0 → PosProportional (row G x) (row G y) →
      (¬ LinearIndependent ℂ ![row G x, row G y]) ∨ BlockOrthVec (row G x) (row G y)

/-- The support relation `Φ_F = {a ∈ D^r : F(a) ≠ 0}`, p. F-9. -/
def Phi {q r : ℕ} (G : (Fin r → Fin q) → ℂ) : Set (Fin r → Fin q) :=
  {a | G a ≠ 0}

/-- The `2(r − 1)`-ary row-equivalence relation `Ω_F = {(x, y) : x ∼_F y}`, p. F-9, for
`r = j + 1`: a tuple `w ∈ D^{j + j}` is the concatenation `(x, y)`, `x` its first `j` entries. -/
def Omega {q j : ℕ} (G : (Fin (j + 1) → Fin q) → ℂ) : Set (Fin (j + j) → Fin q) :=
  {w | RowEquiv G (fun i => w (Fin.castAdd j i)) (fun i => w (Fin.natAdd j i))}

/-- The row-equivalence class `S` of a row index `x` (meaningful for a nonzero row). -/
def rowClass {q j : ℕ} (G : (Fin (j + 1) → Fin q) → ℂ) (x : Fin j → Fin q) :
    Set (Fin j → Fin q) :=
  {y | RowEquiv G x y}

/-- `type_F(α)` for a prefix `α ∈ D^ℓ`, `0 ≤ ℓ ≤ r − 1 = j` (p. F-9): the set of row classes
`S_j` containing some row index whose first `ℓ` coordinates are `α`. A class is represented by
the set of its row indices (the paper indexes the classes by `[s]`; the indexing is arbitrary).
For `ℓ = 0` this is the set of all classes, `type_F(ϵ) = [s]`. -/
def typeOf {q j : ℕ} (G : (Fin (j + 1) → Fin q) → ℂ) {l : ℕ} (hl : l ≤ j)
    (α : Fin l → Fin q) : Set (Set (Fin j → Fin q)) :=
  {S | ∃ x, row G x ≠ 0 ∧ S = rowClass G x ∧ ∃ y ∈ S, (fun i => y (Fin.castLE hl i)) = α}

/-- The type map of `F` is a type-partition map (p. F-9): for every `0 ≤ ℓ ≤ r − 1` and all
`α, β ∈ D^ℓ`, the types are equal or disjoint. -/
def IsTypePartition {q j : ℕ} (G : (Fin (j + 1) → Fin q) → ℂ) : Prop :=
  ∀ (l : ℕ) (hl : l ≤ j) (α β : Fin l → Fin q),
    typeOf G hl α = typeOf G hl β ∨ Disjoint (typeOf G hl α) (typeOf G hl β)

end BlockOrthoCSP.Decide


