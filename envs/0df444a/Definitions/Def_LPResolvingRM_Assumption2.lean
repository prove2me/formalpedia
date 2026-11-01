-- Prove2me | Definitions.Def_LPResolvingRM_Assumption2
-- name    : LPResolvingRM_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:40:05.495849+00:00
-- url     : https://prove2.me/theorems/a1d42d3f-f6db-4101-8ecf-c455b54cd7ca
-- title:
--   Assumption 2 (nondegeneracy), the benchmark $\mathrm{OPT}_D$ and the binding set $\mathcal I^*$
-- statement:
--   **Assumption 2 (Nondegeneracy).** The optimal solution $(y^*,s^*,z^*)$ of the standard-form fluid LP
--   $$\max\ \mu^\top y\quad\text{s.t.}\quad Cy+s=b,\quad y+z=\mathbf 1,\quad y,s,z\ge0 \tag{6}$$
--   (normalized data $\mu_j=p_j\mu_j$, $C_{ij}=p_jc_{ij}$) is unique and nondegenerate:
--   $$|\{j:y^*_j\ne0\}|+|\{i:s^*_i\ne0\}|+|\{j:z^*_j\ne0\}|=m+n.$$
--
--   The **fluid benchmark** is $\mathrm{OPT}_D=\max\{\sum_j p_j\mu_jy_j:\ \sum_jp_jc_jy_j\le b,\ 0\le y\le1\}$, the optimal value of the deterministic LP (3). For a solution $y^*$, the **binding constraints** are $\mathcal I^*=\{i: b_i=C_{i,:}^\top y^*\}$ and the non-binding ones $\mathcal I'=\{i:b_i>C_{i,:}^\top y^*\}$.
--
--   **Formalization Note** $\mathrm{OPT}_D$ is the supremum of the objective over the feasible set; under Assumption 1 the set contains $y=0$ and the objective is bounded, so it is a maximum. Uniqueness of $(y^*,s^*,z^*)$ is uniqueness of $y^*$.
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Assumption 2, p.9; (3), p.6; sets I*, I′, p.9

import Definitions.Def_LPResolvingRM_Instance
import Definitions.Def_LPResolvingRM_nonzeroCount
import Definitions.Def_LPAllocRM_IsLPOptimal

open scoped Classical

namespace LPResolvingRM

/-- **Assumption 2 (Nondegeneracy)** (arXiv:2101.11092v3, p.9): "The optimal solution to (6) is
unique and nondegenerate, i.e., |{j : y∗ⱼ ≠ 0}| + |{i : s∗ᵢ ≠ 0}| + |{j : z∗ⱼ ≠ 0}| = m + n."

LP (6) is `max μᵀy s.t. Cy + s = b, y + z = 1, y, s, z ≥ 0` with the normalized data
`μ_j = p_jμ_j`, `C_{ij} = p_jc_{ij}` (`LPResolvingRM.normMu`, `LPResolvingRM.normC`).

**Formalization Note.** LP (6) is written through its `y`-part, as the bounded LP
`max μᵀy s.t. Cy ≤ b, 0 ≤ y ≤ 1` (the published `LPAllocRM.IsLPOptimal` with upper bound `1`):
`s* = b − Cy*` and `z* = 1 − y*`, so uniqueness of `(y*, s*, z*)` is uniqueness of `y*`. -/
def Assumption2 {n m : ℕ} (I : Instance n m) : Prop :=
  ∃ y, LPAllocRM.IsLPOptimal (normC I) I.b 1 (normMu I) y ∧
    (∀ y', LPAllocRM.IsLPOptimal (normC I) I.b 1 (normMu I) y' → y' = y) ∧
    nonzeroCount (normC I) I.b y = m + n

/-- **The fluid benchmark `OPT_D`**, the optimal value of the deterministic LP (3)
(arXiv:2101.11092v3, p.6): `OPT_D := max ∑_j p_jμ_j y_j s.t. ∑_j p_j c_j y_j ≤ b, 0 ≤ y_j ≤ 1`.

**Formalization Note.** Written as the supremum of the objective over the feasible set. Under
Assumption 1 the feasible set contains `y = 0` (as `b > 0`) and the objective is bounded by
`∑_j p_j μ_j`, so the supremum is a maximum and no junk value occurs. -/
noncomputable def optD {n m : ℕ} (I : Instance n m) : ℝ :=
  sSup ((fun y : Fin n → ℝ => ∑ j, I.p j * I.μ j * y j) '' {y | LPAllocRM.LPFeasible (normC I) I.b 1 y})

/-- The **binding constraints** `I* := {i : b_i = C_{i,:}ᵀ y*}` of a solution `y*` of LP (6)
(arXiv:2101.11092v3, p.9); its complement in `Fin m` is the non-binding set
`I' := {i : b_i > C_{i,:}ᵀ y*}` when `y*` is feasible. `C` is the normalized matrix. -/
noncomputable def binding {n m : ℕ} (I : Instance n m) (y : Fin n → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => I.b i = ∑ j, normC I i j * y j

end LPResolvingRM


