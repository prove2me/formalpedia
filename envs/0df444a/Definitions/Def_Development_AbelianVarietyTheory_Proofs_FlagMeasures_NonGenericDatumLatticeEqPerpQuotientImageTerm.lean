-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:00:22.716262+00:00
-- url     : https://prove2.me/theorems/1a036dae-6953-5b46-ae3c-4050bb63f449
-- title:
--   Non Generic Datum Lattice Eq Perp Quotient Image Term
-- statement:
--   Definitions and structural lemmas for Non Generic Datum Lattice Eq Perp Quotient Image Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NonGenericDatumLatticeEqPerpQuotientImageTerm.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
noncomputable section
namespace GlobalTheory.InnerRead
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
def hL (y : V) : V →+ E := ⟨⟨fun x => H.h x y, H.h_zero_left y⟩, fun x x' => H.h_add_left x x' y⟩
def Good (X : Submodule E V) (u : V ≃ₗ[E] V) : Prop :=
  IsUnitary H u ∧ ∀ v ∈ H.perp X, u v - v ∈ X
variable {H} {r : ℕ} (Fr : FrameD H r)
end GlobalTheory.InnerRead


