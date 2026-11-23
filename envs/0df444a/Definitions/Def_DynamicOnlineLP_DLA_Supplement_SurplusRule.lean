-- Prove2me | Definitions.Def_DynamicOnlineLP_DLA_Supplement_SurplusRule
-- name    : DynamicOnlineLP_DLA_Supplement_SurplusRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:06:12.746172+00:00
-- url     : https://prove2.me/theorems/618ce72f-451f-45f0-9518-7f8af4021019
-- title:
--   Multidimensional allocation rule: reject, or choose an option of largest positive surplus
-- statement:
--   Consider one arrival with rewards $f_{tj}$ and consumptions $g_{itj}$, for options $j=1,\dots,k$ and resources $i=1,\dots,m$. At a resource price $p\in\mathbb R^m$ the **surplus** of option $j$ is $f_{tj}-\sum_ip_ig_{itj}$. The **allocation rule** of §5.1 is
--
--   $$x_t(p)=\begin{cases}0&\text{if } f_{tj}\le\sum_ip_ig_{itj}\text{ for all }j,\\ e_r&\text{otherwise, where } r\in\arg\max_j\Big(f_{tj}-\sum_ip_ig_{itj}\Big),\end{cases}$$
--
--   where $e_r$ is the $r$th unit vector of $\mathbb R^k$.
--
--   The definitions are: the surplus; the predicate saying that a choice (reject, or an option) is allowed by this rule; and the decision vector of a choice. Rejection is the only allowed choice when every surplus is at most zero, including a largest surplus equal to zero. Otherwise every maximizer is allowed, since the paper breaks ties arbitrarily.
--
--   This rule extends the threshold rule (9) of the scalar model to a choice among $k$ options.
--
--   **Formalization Note** A choice is an element of `Option (Fin k)`, with `none` for rejection.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 886, §5.1, definition of x_t(p)

import Mathlib

namespace DynamicOnlineLP.DLA.Supplement

/-- The surplus `f_j - ∑_i p_i g_{ij}` of option `j` of one arrival at resource price `p`. -/
def surplus {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ) (p : Fin m → ℝ) (j : Fin k) : ℝ :=
  f j - ∑ i : Fin m, p i * g i j

/-- `r` is an allowed choice of the allocation rule of §5.1 for one arrival at price `p`:
`none` (reject) exactly when every surplus is at most zero, and otherwise `some j` with `j` a
maximizer of the surplus. Several maximizers may be allowed. -/
def IsSurplusChoice {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ) (p : Fin m → ℝ) :
    Option (Fin k) → Prop
  | none => ∀ j : Fin k, surplus f g p j ≤ 0
  | some r => 0 < surplus f g p r ∧ ∀ j : Fin k, surplus f g p j ≤ surplus f g p r

/-- The decision vector of a choice: the zero vector for `none`, the unit vector `e_r` for
`some r`. -/
def choiceVec {k : ℕ} (c : Option (Fin k)) (j : Fin k) : ℝ :=
  if c = some j then 1 else 0

end DynamicOnlineLP.DLA.Supplement


