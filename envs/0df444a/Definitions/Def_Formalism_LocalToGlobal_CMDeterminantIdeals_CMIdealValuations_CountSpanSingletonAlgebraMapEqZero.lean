-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:20:18.50134+00:00
-- url     : https://prove2.me/theorems/b7ffa84e-df0f-4082-af02-447bbb3035ed
-- title:
--   Count Span Singleton Algebra Map Eq Zero
-- statement:
--   Definitions and structural lemmas for Count Span Singleton Algebra Map Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
section counts
variable {F : Type} [Field F] [NumberField F]
end counts
section bc
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
lemma algebraMap_int_tower (a : 𝓞 K) :
    algebraMap (𝓞 K1) K1 (algebraMap (𝓞 K) (𝓞 K1) a) = algebraMap K K1 (algebraMap (𝓞 K) K a) := by
  first
  | rfl
  | rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
lemma algebraMap_int_injective : Function.Injective (algebraMap (𝓞 K) (𝓞 K1)) := by
  intro a b h
  have h1 := congrArg (algebraMap (𝓞 K1) K1) h
  rw [algebraMap_int_tower, algebraMap_int_tower] at h1
  exact IsFractionRing.injective (𝓞 K) K ((algebraMap K K1).injective h1)
lemma nzd_le : (𝓞 K)⁰ ≤ Submonoid.comap (algebraMap (𝓞 K) (𝓞 K1)) (𝓞 K1)⁰ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Formalism.L2.LamCM.algebraMap_int_injective (K := K) (K1 := K1))
def bcI (I : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K1)⁰ K1 :=
  FractionalIdeal.extended K1 (nzd_le (K := K) (K1 := K1)) I
end bc
end Formalism.L2.LamCM


