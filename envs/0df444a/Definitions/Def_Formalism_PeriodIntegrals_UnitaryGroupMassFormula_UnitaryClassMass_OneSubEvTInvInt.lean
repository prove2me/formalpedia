-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:44.354378+00:00
-- url     : https://prove2.me/theorems/d8e422b4-671e-4986-8ae7-aba48264e00c
-- title:
--   One Sub Ev TInv Int
-- statement:
--   Definitions and structural lemmas for One Sub Ev TInv Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Ad
open Classical
variable {F : Type} [Field F] [NumberField F]
theorem af_ext {a b : Af F} (h : ∀ w, a w = b w) : a = b := Subtype.ext (funext h)
theorem af_mul_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a * b) w = a w * b w := rfl
theorem af_add_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a + b) w = a w + b w := rfl
theorem af_alg_apply (c : F) (w : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (Af F) c) w = algebraMap F (w.adicCompletion F) c := rfl
variable (v : HeightOneSpectrum (𝓞 F))
def sgl (x : Fv F v) : Af F :=
  RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x
theorem sgl_apply (x : Fv F v) (w : HeightOneSpectrum (𝓞 F)) : sgl v x w = Pi.single v x w := rfl
theorem sgl_add (x y : Fv F v) : sgl v (x + y) = sgl v x + sgl v y := af_ext fun w => by
  rw [af_add_apply, sgl_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, add_zero]
theorem sgl_smul (c : F) (x : Fv F v) : c • sgl v x = sgl v (c • x) := af_ext fun w => by
  rw [Algebra.smul_def, Algebra.smul_def, af_mul_apply, af_alg_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, mul_zero]
def ivL : Fv F v →ₗ[F] Af F where
  toFun := sgl v
  map_add' := sgl_add v
  map_smul' c x := (sgl_smul v c x).symm
def evT (T : Set (HeightOneSpectrum (𝓞 F))) : Af F :=
  (⟨fun w => if w ∈ T then (1 : w.adicCompletion F) else 0,
    Filter.Eventually.of_forall fun w => by
      show (if w ∈ T then (1 : w.adicCompletion F) else 0) ∈ w.adicCompletionIntegers F
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩ :
    Πʳ w : HeightOneSpectrum (𝓞 F), [w.adicCompletion F, w.adicCompletionIntegers F])
end Ad
section Tens
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))
def Psi : Af F ⊗[F] E →ₐ[F] E ⊗[F] Fv F v :=
  (Algebra.TensorProduct.comm F (Fv F v) E).toAlgHom.comp
    (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))
def Phi : E ⊗[F] Fv F v →ₗ[F] Af F ⊗[F] E :=
  (TensorProduct.map (ivL v) LinearMap.id) ∘ₗ (TensorProduct.comm F E (Fv F v)).toLinearMap
end Tens
end PI.UnitaryGroupMassFormula.UJClassMass


