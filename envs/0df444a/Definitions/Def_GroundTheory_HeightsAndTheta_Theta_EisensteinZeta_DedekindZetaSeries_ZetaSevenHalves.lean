-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:40.6353+00:00
-- url     : https://prove2.me/theorems/96f4c83a-6f5f-4c80-8736-48d4e26a071c
-- title:
--   Zeta Seven Halves
-- statement:
--   Definitions and structural lemmas for Zeta Seven Halves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/ZetaSevenHalves.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open NumberField
noncomputable section
def zetaSevenHalves : ℝ :=
  (riemannZeta (7 / 2 : ℂ)).re
def ZetaSevenHalvesBounds.Value.Statement : Prop :=
  riemannZeta (7 / 2 : ℂ) = (zetaSevenHalves : ℂ) ∧
    (1.1267 : ℝ) ≤ zetaSevenHalves ∧ zetaSevenHalves < (1.1268 : ℝ)
def ZetaSevenHalvesBounds.LogBound.Statement : Prop :=
  Real.log zetaSevenHalves ≤ (0.13 : ℝ)
def ZetaSevenHalvesBounds.TwiceLogBound.Statement : Prop :=
  2 * Real.log zetaSevenHalves ≤ (0.26 : ℝ)
def ZetaSevenHalvesBounds.DedekindBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Real.log (dedekindZeta K (7 / 2 : ℂ)).re ≤
      (Module.finrank ℚ K : ℝ) * Real.log zetaSevenHalves
end
end GroundTheory.Heights₂.Theta


