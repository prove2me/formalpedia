-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_EquivLift
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_EquivLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:44.574944+00:00
-- url     : https://prove2.me/theorems/3bbbdd1f-e5c0-45c5-91aa-735d23202376
-- title:
--   Equiv Lift
-- statement:
--   Definitions and structural lemmas for Equiv Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/EquivLift.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
def EquivLift : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (R : Finset (Fin m → ℕ)) (t : Module.End ℂ (PX m n)),
    (∀ f ∈ box ε (R : Set _), t f ∈ box ε (R : Set _)) →
    (∀ i j, ∀ f ∈ box ε (R : Set _), t (KopL ε i j f) = KopL ε i j (t f)) →
    ∃ w ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2), ∀ f ∈ box ε (R : Set _), t f = w f
end PositivityTheory.Rg.Sw.LC


