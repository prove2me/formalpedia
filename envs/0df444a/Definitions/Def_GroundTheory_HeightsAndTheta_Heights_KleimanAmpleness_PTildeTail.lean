-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:28.841082+00:00
-- url     : https://prove2.me/theorems/9f32d586-1a4f-5b68-a541-573894ea379e
-- title:
--   PTilde Tail
-- statement:
--   Definitions and structural lemmas for PTilde Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
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
open MvPolynomial
noncomputable section
universe u w
section Cocycles
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)
def FinGradedSub.cellCone (I : StdCell N) : LocMod S N M.coneSub I.1 →ₗ[Poly S N] ConeLaurent S x :=
  if h : I.1 ⊆ support x then locCone M I.1 h else 0
end Cocycles
end
end GroundTheory.Heights₂.Heights.Kleiman


