-- Prove2me | Definitions.Def_IterRoundKMedian_Main_ClientProfile
-- name    : IterRoundKMedian_Main_ClientProfile
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:25:28.033685+00:00
-- url     : https://prove2.me/theorems/3cfa9879-ed0a-4690-81e0-49fd0fc7a175
-- title:
--   Distance profile of a client: V_j, dispersion D_j, mean absolute deviation M_j, admissible radii, T_j(R) and the assurance radius A_j
-- statement:
--   For a client $j$ of a complete fractional solution, the facilities $i$ carry weights $y_i\ge0$ with $\sum_i y_i=1$ (the support is $F_j$) at distances $d_i=d(i,j)\ge0$. Define
--   $$V_j=\sum_i y_id_i,\qquad D_j=\sum_{i,q}y_iy_q|d_i-d_q|,\qquad M_j=\sum_i y_i|d_i-V_j|.$$
--   A radius $R$ is **admissible** if $y(\{i: d_i\le R\})\ge 1/2$ (84). Let $T_j(R)=\sum_{i: d_i>R}y_id_i$. The **assurance radius** is
--   $$A_j=\min\{R+5e\,T_j(R): R \text{ admissible}\},$$
--   the optimal value defining the threshold radius $R_j$.
--
--   **Formalization Note.** Namespace `ClientProfile`, over a finite type of facilities with weights `y` (zero off the support). `A y d` is the `sInf` of the objective over the admissible radii; when $\sum_i y_i=1$ and $d\ge0$ this set is nonempty and bounded below by $0$, and the infimum is attained, so it is the minimum.
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), pp. 29 and 64–65, §4.2 and §7.1

import Mathlib

namespace IterRoundKMedian.Main
namespace ClientProfile

/-! The distance profile `P_j` of one client `j` in a complete fractional solution
(§4.2, §7.1): facilities `i` (a finite type) carry weights `y_i = x_{ij} ≥ 0` with
`Σ_i y_i = 1` (the support is `F_j`), at distances `d_i = d(i, j) ≥ 0`. -/

variable {ι : Type*} [Fintype ι]

/-- `V_j = Σ_{i∈F_j} y_i d_i`, the fractional cost. -/
def V (y d : ι → ℝ) : ℝ := ∑ i, y i * d i

/-- `D_j = Σ_{i,q∈F_j} y_i y_q |d_i − d_q|`, the dispersion. -/
def D (y d : ι → ℝ) : ℝ := ∑ i, ∑ q, y i * y q * |d i - d q|

/-- `M_j = Σ_{i∈F_j} y_i |d_i − V_j|`, the mean absolute deviation. -/
def M (y d : ι → ℝ) : ℝ := ∑ i, y i * |d i - V y d|

/-- A radius `R` is admissible (84) if `y({i ∈ F_j : d_i ≤ R}) ≥ 1/2`. -/
def Admissible (y d : ι → ℝ) (R : ℝ) : Prop :=
  (1 : ℝ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => d i ≤ R), y i

/-- `T_j(R) = Σ_{i∈F_j : d_i > R} y_i d_i`. -/
noncomputable def T (y d : ι → ℝ) (R : ℝ) : ℝ := ∑ i ∈ Finset.univ.filter (fun i => R < d i), y i * d i

/-- The assurance radius `A_j = min { R + 5e·T_j(R) : R admissible }` (the minimum exists:
the admissible radii form a nonempty closed half-line when `Σ y = 1`, and the objective
attains its infimum at a support distance). -/
noncomputable def A (y d : ι → ℝ) : ℝ :=
  sInf ((fun R => R + 5 * Real.exp 1 * T y d R) '' {R | Admissible y d R})

end ClientProfile
end IterRoundKMedian.Main


