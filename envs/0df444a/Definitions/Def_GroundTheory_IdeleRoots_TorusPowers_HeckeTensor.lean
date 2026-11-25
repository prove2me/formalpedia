-- Prove2me | Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
-- name    : GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:21:32.053037+00:00
-- url     : https://prove2.me/theorems/ab797492-cc2b-5b3a-91e5-70615eaf5730
-- title:
--   Hecke Tensor
-- statement:
--   Definitions and structural lemmas for Hecke Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
namespace GroundTheory.BlockD
namespace ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (F E) in

def adeleEquiv : AE F E ≃ₐ[AF F] 𝔸[E] := adeleTensorAlgEquivLeft F E
instance isModuleTopology_AE : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
variable (F E) in

def ideleEquiv : (AE F E)ˣ ≃* IdeleGroup E :=
  Units.mapEquiv (adeleEquiv F E).toRingEquiv.toMulEquiv
variable (F E) in

def finEquiv : Af F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E :=
  (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv.trans (finiteTensorEquiv F E).toRingEquiv
end ThmBHecke
end GroundTheory.BlockD


