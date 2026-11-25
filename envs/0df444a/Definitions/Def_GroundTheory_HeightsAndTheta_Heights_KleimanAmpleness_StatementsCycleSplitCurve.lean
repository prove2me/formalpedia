-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:33.813542+00:00
-- url     : https://prove2.me/theorems/355214ca-d046-4ebe-bebb-88e1b4cb51a0
-- title:
--   Statements Cycle Split Curve
-- statement:
--   Definitions and structural lemmas for Statements Cycle Split Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsCycleSplitCurve.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
def CycleSplit.Curve.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ G : Ideal (Poly S N), IsSubvar x G 1 → 𝔪.map (C : S →+* Poly S N) ≤ G →
    ∀ᶠ c : ℕ in atTop, interSum G ![M.toSubSystem] c = interNum G ![M.toSubSystem]
end
end GroundTheory.Heights₂.Heights.Kleiman


