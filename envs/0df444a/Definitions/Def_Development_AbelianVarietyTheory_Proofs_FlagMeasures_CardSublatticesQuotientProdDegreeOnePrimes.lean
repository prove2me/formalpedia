-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesQuotientProdDegreeOnePrimes
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesQuotientProdDegreeOnePrimes
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:45.953749+00:00
-- url     : https://prove2.me/theorems/763ea1b0-63a0-435c-b9af-4fcec2d0afb2
-- title:
--   Card Sublattices Quotient Prod Degree One Primes
-- statement:
--   Definitions and structural lemmas for Card Sublattices Quotient Prod Degree One Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardSublatticesQuotientProdDegreeOnePrimes.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.SublatCount
section Abstract
variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]
def Ker (I : Ideal O) (N : Type) [AddCommGroup N] [Module O N] : Set (Submodule O N) :=
  {L | ∃ f : N →ₗ[O] O ⧸ I, Function.Surjective f ∧ LinearMap.ker f = L}
noncomputable def crt (I J : Ideal O) (h : IsCoprime I J) :
    (O ⧸ I * J) ≃ₗ[O] (O ⧸ I) × (O ⧸ J) :=
  { Ideal.quotientMulEquivQuotientProd I J h with
    map_smul' := fun c x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl }
end Abstract
end GlobalTheory.SublatCount


