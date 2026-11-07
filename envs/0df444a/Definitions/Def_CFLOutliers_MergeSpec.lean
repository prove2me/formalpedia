-- Prove2me | Definitions.Def_CFLOutliers_MergeSpec
-- name    : CFLOutliers_MergeSpec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:18.138491+00:00
-- url     : https://prove2.me/theorems/073a4493-c038-4e63-b1d9-daed32d437e7
-- title:
--   The merge parameter $\theta$ and the conclusion of Lemma 2.2
-- statement:
--   Let $S^-$, $S^+$ be solutions with $q^-=|C_{S^-}|$, $q^+=|C_{S^+}|$, $a=c(S^-)$, $b=c(S^+)$ and
--
--   $$\theta=\frac{q-q^-}{q^+-q^-}.$$
--
--   A solution $S$ **meets the merge bound** with surcharge $M$ if it is capacity-feasible, serves at least $q$ clients, and
--
--   $$c(S)\le\min\{b,\ a+\theta b+M\}.\tag{3}$$
--
--   This is the conclusion of Lemma 2.2 and the specification of the merge step of the Appendix B procedure.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §2.1 and Lemma 2.2, p.5

import Mathlib
import Definitions.Def_CFLOutliers_Sol

namespace CFLOutliers

/-- **The merge parameter** `θ = (q − q⁻)/(q⁺ − q⁻)` of §2.1, p.5, with `q⁻ = |C_{S⁻}|`,
`q⁺ = |C_{S⁺}|` (computed in ℝ). -/
noncomputable def mergeTheta {I : Inst} (Sm Sp : Sol I) : ℝ :=
  ((I.q : ℝ) - (served Sm).card) / (((served Sp).card : ℝ) - (served Sm).card)

/-- **The conclusion of Lemma 2.2** (p.5): `S` is capacity-feasible, serves at least `q` clients and
costs at most `min{b, a + θ b + M}`, display (3), where `a = c(S⁻)`, `b = c(S⁺)`. -/
def MergeSpec {I : Inst} (Sm Sp : Sol I) (M : ℝ) (S : Sol I) : Prop :=
  S.CapFeasible ∧ I.q ≤ (served S).card ∧
    cost S ≤ min (cost Sp) (cost Sm + mergeTheta Sm Sp * cost Sp + M)

end CFLOutliers


