-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_TraceDecomposition
-- name    : HamSimTradeoff_AncillaDepth_Supplement_TraceDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:51:14.137198+00:00
-- url     : https://prove2.me/theorems/c9fcc630-ca4f-4014-9acf-c0785f5945da
-- title:
--   The self-contained decomposition assumptions of Proposition 8.9
-- statement:
--   For a continuous bounded real function $f$ and degree $d\ge1$, this predicate records the Jacobi pair, its discriminant $\Delta$, a best polynomial $P$ of degree at most $d-1$, a sign $\sigma\in\{\pm1\}$, and a remainder $r$ with
--   $$E_d\le\eta<E_{d-1},\qquad f=P+\sigma(E_{d-1}-\eta)\Delta+r,\qquad |r|\le\eta\ \text{on }[-1,1].$$
--   Both endpoint matrices have norm at most one. These are the assumptions used by Lemma 8.10, not a claim that the decomposition exists. Theorem 8.12 must establish its needed family rather than assume this predicate.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 38, Proposition 8.9, Lemma 8.10

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Jacobi
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

def TraceDecomposition {d : ℕ} (f : ℝ → ℝ) (J : JacobiData d)
    (Delta P : Polynomial ℝ) (sigma eta : ℝ) (r : ℝ → ℝ) : Prop :=
  JacobiBounded J ∧ IsDiscriminant J Delta ∧
  P.natDegree ≤ d-1 ∧
  (∀ x ∈ Set.Icc (-1:ℝ) 1, |f x - P.eval x| ≤ bestError f (d-1)) ∧
  (sigma = 1 ∨ sigma = -1) ∧ bestError f d ≤ eta ∧ eta < bestError f (d-1) ∧
  (∀ x ∈ Set.Icc (-1:ℝ) 1, |r x| ≤ eta) ∧
  (∀ x ∈ Set.Icc (-1:ℝ) 1,
    f x = P.eval x + sigma*(bestError f (d-1)-eta)*Delta.eval x + r x)

end
end HamSimTradeoff.AncillaDepth.Supplement


