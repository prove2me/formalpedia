-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InclEIntMem
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_InclEIntMem
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:08.070645+00:00
-- url     : https://prove2.me/theorems/eced1ee6-6b51-4693-942c-1b3c72170141
-- title:
--   Incl EInt Mem
-- statement:
--   Definitions and structural lemmas for Incl EInt Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InclEIntMem.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
noncomputable section
open Classical
namespace GlobalTheory.VectorInclusion
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
def vecIncl (x : Fin n → E) : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F :=
  fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (x i)
theorem inclE_int_mem (c : 𝓞 E) :
    Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E) ∈ Formalism.MainNotions.S.IntAf F E := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨(c : E), ⟨c, rfl⟩⟩, ?_⟩
  rfl
end GlobalTheory.VectorInclusion
end


