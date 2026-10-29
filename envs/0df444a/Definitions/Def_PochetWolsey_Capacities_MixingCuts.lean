-- Prove2me | Definitions.Def_PochetWolsey_Capacities_MixingCuts
-- name    : PochetWolsey_Capacities_MixingCuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:51.493055+00:00
-- url     : https://prove2.me/theorems/92b98eb0-c17e-49f3-8a95-efeaee7aced1
-- title:
--   The two initial-stock mixing-cut families
-- statement:
--   For $n$ periods, real demand $d$, capacity $C$, and real setup vector $y$, put $b_t=d_{1t}/C$ and $f_t=b_t-\lfloor b_t\rfloor$. For a nonempty subset $T=\{i_1,\ldots,i_r\}$ ordered so that $f_{i_1}\le\cdots\le f_{i_r}$, let $f_{i_0}=0$ and define
--   $$
--   R_T(y)=C\sum_{\tau=1}^r(f_{i_\tau}-f_{i_{\tau-1}})\left(\lfloor b_{i_\tau}\rfloor+1-\sum_{u=1}^{i_\tau}y_u\right).
--   $$
--   The mixing-cut polyhedron consists of $s_0\ge0$, $0\le y\le1$, all original covering inequalities $s_0+C\sum_{u=1}^t y_u\ge d_{1t}$, and, for every such subset and ordering,
--   $$
--   s_0\ge R_T(y),\qquad
--   s_0\ge R_T(y)+C(1-f_{i_r})\left(\lfloor b_{i_1}\rfloor-\sum_{u=1}^{i_1}y_u\right).
--   $$
--   This defines the explicit candidate hull using inequalities, independently of the original binary feasible set.
--
--   **Formalization Note** Nonempty subsets are injective maps from `Fin (m+1)`; `Monotone` orders their fractional parts and permits ties. The first summand is separated to implement $f_{i_0}=0$ without a predecessor index. The singleton case has an empty remaining sum. Empty subsets add only stock nonnegativity and are already covered. The definitions are total, but the hull theorem assumes $C>0$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 280 (PDF 293), Theorem 9.4, inequality families

import Mathlib
import Definitions.Def_PochetWolsey_Capacities_Model

namespace PochetWolsey.Capacities

noncomputable def demandFraction {n : ℕ} (C : ℝ) (d : Fin n → ℝ) (t : Fin n) : ℝ :=
  (∑ u ∈ Finset.Iic t, d u) / C - (⌊(∑ u ∈ Finset.Iic t, d u) / C⌋ : ℤ)

/-- The common first right-hand side in Theorem 9.4, for m+1 selected periods. -/
noncomputable def mixingRHS {n : ℕ} (C : ℝ) (d y : Fin n → ℝ)
    (m : ℕ) (i : Fin (m + 1) → Fin n) : ℝ :=
  let f := demandFraction C d
  let a := fun t => (⌊(∑ u ∈ Finset.Iic t, d u) / C⌋ : ℤ) + 1 -
    (∑ u ∈ Finset.Iic t, y u)
  C * (f (i 0) * a (i 0) +
    ∑ j : Fin m, (f (i j.succ) - f (i j.castSucc)) * a (i j.succ))

/-- Nonnegativity, setup bounds, the original rows, and both mixing-cut families. -/
noncomputable def MixingCuts {n : ℕ} (C : ℝ) (d : Fin n → ℝ) :
    Set (ℝ × (Fin n → ℝ)) :=
  {p | 0 ≤ p.1 ∧ (∀ u, 0 ≤ p.2 u ∧ p.2 u ≤ 1) ∧
    (∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ p.1 + C * ∑ u ∈ Finset.Iic t, p.2 u) ∧
    ∀ (m : ℕ) (i : Fin (m + 1) → Fin n), Function.Injective i →
      Monotone (fun j => demandFraction C d (i j)) →
      mixingRHS C d p.2 m i ≤ p.1 ∧
      mixingRHS C d p.2 m i + C * (1 - demandFraction C d (i (Fin.last m))) *
        ((⌊(∑ u ∈ Finset.Iic (i 0), d u) / C⌋ : ℤ) -
          (∑ u ∈ Finset.Iic (i 0), p.2 u)) ≤ p.1}

end PochetWolsey.Capacities


