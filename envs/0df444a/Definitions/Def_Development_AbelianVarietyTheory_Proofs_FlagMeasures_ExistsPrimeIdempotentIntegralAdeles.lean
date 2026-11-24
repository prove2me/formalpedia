-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T13:11:58.9598+00:00
-- url     : https://prove2.me/theorems/109fe347-fcdb-4ef8-81d4-214decbda105
-- title:
--   Exists Prime Idempotent Integral Adeles
-- statement:
--   Definitions and structural lemmas for Exists Prime Idempotent Integral Adeles, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimeIdempotentIntegralAdeles.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Theorems.Thm_Formalism_UG_P_afsplit_eps_int
import Theorems.Thm_Formalism_UG_P_afsplit_prV_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
namespace GlobalTheory.RowLev
namespace PrimeIdem
open Formalism.UG Formalism.UG.P
section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
noncomputable abbrev LocInt (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
noncomputable def epsV (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    IntAf F E := ⟨afsplitEps E v, afsplit_eps_int v⟩
noncomputable def prInt (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    IntAf F E →+* LocInt E v :=
  ((prV (E := E) v).comp (IntAf F E).subtype).codRestrict _ fun y => afsplit_prV_int v y.1 y.2
end Adelic
end PrimeIdem
open PrimeIdem Formalism.UG Formalism.UG.P
end GlobalTheory.RowLev


