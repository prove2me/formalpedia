-- Prove2me | solution 1 for AutomorphicForm.baseChangeGL_toTensorGL_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/08c8b53f-97e1-55d5-a32d-dc5d24628cf2

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_baseChangeGL_toTensorGL_self

set_option autoImplicit false

open NumberField IsDedekindDomain TensorProduct
open scoped TensorProduct.RightActions NumberField.LiesOver

noncomputable section

namespace R4BCSelf

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
theorem under_self (w : HeightOneSpectrum (𝓞 K)) : w.under (𝓞 K) = w := by
  refine HeightOneSpectrum.ext ?_
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id]

theorem adicCompletionSemialgHom_self (v : HeightOneSpectrum (𝓞 K)) (h : v.under (𝓞 K) = v)
    (t : v.adicCompletion K) :
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K K (⟨v, h⟩ : v.Extension (𝓞 K)) t = t := by
  set φ := HeightOneSpectrum.Extension.adicCompletionSemialgHom K K (⟨v, h⟩ : v.Extension (𝓞 K)) with hφ
  have hc : Continuous φ := HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K K _
  have hdense := HeightOneSpectrum.denseRange_algebraMap (K := K) v
  refine hdense.induction_on t (isClosed_eq hc continuous_id) ?_
  intro k
  set x : WithVal (v.valuation K) := (WithVal.equiv (v.valuation K)).symm (algebraMap K K k) with hx
  show φ (x : v.adicCompletion K) = (x : v.adicCompletion K)
  rw [hφ, HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe]
  congr 1

theorem adicCompletionSemialgHom_apply_eq (v w : HeightOneSpectrum (𝓞 K)) (h : w.under (𝓞 K) = v)
    (hvw : v = w) (a : FiniteAdeleRing (𝓞 K) K) :
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K K (⟨w, h⟩ : v.Extension (𝓞 K)) (a v) = a w := by
  subst hvw
  exact adicCompletionSemialgHom_self K v h (a v)

theorem finiteConorm_self (a : FiniteAdeleRing (𝓞 K) K) :
    M4aHerbrand.Bridge.finiteConorm (𝓞 K) K K (𝓞 K) a = a := by
  refine FiniteAdeleRing.ext K fun w => ?_
  rw [M4aHerbrand.Bridge.finiteConorm_apply]
  exact adicCompletionSemialgHom_apply_eq K (w.under (𝓞 K)) w rfl (under_self K w) a

omit [NumberField K] in

theorem algebraMap_completion_apply_eq (v w : InfinitePlace K) [hw : w.1.LiesOver v.1] (hvw : v = w)
    (x : InfiniteAdeleRing K) : algebraMap v.Completion w.Completion (x v) = x w := by
  subst hvw
  show NumberField.LiesOver.completionMap (x v) = x v
  generalize x v = t
  induction t using InfinitePlace.Completion.induction_on with
  | hp =>
    exact isClosed_eq NumberField.LiesOver.continuous_completionMap continuous_id
  | ih a =>
    rw [NumberField.LiesOver.completionMap_coe]
    rfl

theorem conorm_self (x : InfiniteAdeleRing K) :
    (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := K)).conorm x = x := by
  funext w
  haveI : w.1.LiesOver (w.comap (algebraMap K K)).1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq rfl
  have hcomp : (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := K)).conorm x w
      = algebraMap ((w.comap (algebraMap K K)).Completion) w.Completion (x (w.comap (algebraMap K K))) := by
    show M4aHerbrand.ArchSemilocal.psiFactor (w.comap (algebraMap K K)) w
        ((x (w.comap (algebraMap K K))) ⊗ₜ[K] (1 : K)) = _
    rw [M4aHerbrand.ArchSemilocal.psiFactor_tmul, map_one, mul_one]
  rw [hcomp]
  exact algebraMap_completion_apply_eq K (w.comap (algebraMap K K)) w (InfinitePlace.comap_id w) x

theorem genuineβ_self (a : AdeleRing (𝓞 K) K) : M4aHerbrand.Bridge.genuineβ K K a = a :=
  Prod.ext (conorm_self K a.1) (finiteConorm_self K a.2)

theorem baseChangeEquiv_one_tmul_self (a : AdeleRing (𝓞 K) K) :
    AutomorphicForm.baseChangeEquiv K K ((1 : K) ⊗ₜ[K] a) = a := by
  rw [AutomorphicForm.baseChangeEquiv_one_tmul, genuineβ_self]

theorem baseChangeGL_toTensorGL_self (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    AutomorphicForm.baseChangeGL K K (AutomorphicForm.toTensorGL K K (AdeleRing (𝓞 K) K) x) = x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  exact baseChangeEquiv_one_tmul_self K ((x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)

end R4BCSelf

end

theorem solution (K : Type) [Field K] [NumberField K] (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    AutomorphicForm.baseChangeGL K K (AutomorphicForm.toTensorGL K K (AdeleRing (𝓞 K) K) x) = x :=
  R4BCSelf.baseChangeGL_toTensorGL_self K x

end S_AutomorphicForm_baseChangeGL_toTensorGL_self
end P2MW
export P2MW.S_AutomorphicForm_baseChangeGL_toTensorGL_self (solution)
