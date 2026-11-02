-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FiniteSetKernelTranslationCleanV1
-- name    : MarkovProcess_V3HRepair_FiniteSetKernelTranslationCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:02:42.26432+00:00
-- url     : https://prove2.me/theorems/d388f008-d6c0-49fa-a502-11193151b0f2
-- title:
--   Verified MarkovProcess source repair: FiniteSetKernelTranslationCleanV1
-- statement:
--   Time translation of finite-set Markov kernels agrees with the translated coordinate pullback, using finite-time restriction and measurability of translation.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FiniteSetKernelTranslationCleanV1 source SHA-256 72f09416a0db7bfc09d6953c73dbf7bba8466ad9560c651eb41d6f5f1eab612c. Only repaired-module import paths were converted to their new published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Definitions.Def_MarkovProcess_V3HRepair_TranslateMeasurabilityCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_FiniteTimeKernelRestrictionCleanV3
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelShift_4030eb49
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
open MeasureTheory ProbabilityTheory
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
noncomputable section
@[simp]
theorem finiteSetTranslateEquiv_apply (s : NNReal) (I : Finset NNReal) (t : I) :
    (finiteSetTranslateEquiv s I t : NNReal) = s + t :=
  rfl


private def finiteSetTranslateFinOrderIso (s : NNReal) (I : Finset NNReal) :
    Fin I.card ≃o Fin (finiteSetTranslate s I).card :=
  Fin.castOrderIso (by simp only [finiteSetTranslate, Finset.card_map])

private theorem finiteSetTimes_translate (s : NNReal) (I : Finset NNReal) :
    (finiteSetTimes (finiteSetTranslate s I)).restrict
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding =
      (finiteSetTimes I).translate s := by
  let e := (finiteSetTranslateFinOrderIso s I).toOrderEmbedding
  have hcard : (finiteSetTranslate s I).card = I.card := by
    simp only [finiteSetTranslate, Finset.card_map]
  have hleft :
      (fun i : Fin I.card ↦ finiteSetTimes (finiteSetTranslate s I) (e i)) =
        (finiteSetTranslate s I).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      exact Finset.orderEmbOfFin_mem _ rfl (e i)
    · exact (finiteSetTimes (finiteSetTranslate s I)).strictMono.comp e.strictMono
  have hright :
      (fun i : Fin I.card ↦ s + finiteSetTimes I i) =
        (finiteSetTranslate s I).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      exact Finset.mem_map_of_mem (addLeftEmbedding s)
        (Finset.orderEmbOfFin_mem I rfl i)
    · intro i j hij
      simpa only [add_comm] using add_lt_add_left ((finiteSetTimes I).strictMono hij) s
  apply DFunLike.ext _ _
  intro i
  exact congrFun (hleft.trans hright.symm) i

private theorem pullback_orderedPathToFiniteSet {alpha : Type*}
    (s : NNReal) (I : Finset NNReal) :
    pullbackFiniteSetTranslate (alpha := alpha) s I ∘
        orderedPathToFiniteSet (α := alpha) (finiteSetTranslate s I) =
      orderedPathToFiniteSet I ∘ FiniteOrderedTimes.restrictPath
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding := by
  funext path t
  apply congrArg path
  apply (finiteSetTimes (finiteSetTranslate s I)).injective
  have hshifted :
      finiteSetTimes (finiteSetTranslate s I)
          (((finiteSetTranslate s I).orderIsoOfFin rfl).symm
            (finiteSetTranslateEquiv s I t)) =
        s + t := by
    change (((finiteSetTranslate s I).orderIsoOfFin rfl
      (((finiteSetTranslate s I).orderIsoOfFin rfl).symm
        (finiteSetTranslateEquiv s I t)) : finiteSetTranslate s I) : NNReal) = s + t
    rw [OrderIso.apply_symm_apply]
    exact finiteSetTranslateEquiv_apply s I t
  have htimes := congrArg
    (fun times : FiniteOrderedTimes I.card ↦
      times ((I.orderIsoOfFin rfl).symm t))
    (finiteSetTimes_translate s I)
  have horiginal : finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) = t := by
    change (((I.orderIsoOfFin rfl) ((I.orderIsoOfFin rfl).symm t) : I) : NNReal) = t
    exact congrArg Subtype.val ((I.orderIsoOfFin rfl).apply_symm_apply t)
  change finiteSetTimes (finiteSetTranslate s I)
      ((finiteSetTranslateFinOrderIso s I).toOrderEmbedding
        ((I.orderIsoOfFin rfl).symm t)) =
    s + finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) at htimes
  rw [horiginal] at htimes
  rw [hshifted]
  exact htimes.symm

namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]

/-- Translating a finite observation set is the same as evolving first for the translation
amount, after the translated coordinates are reindexed by their original times. -/
theorem finiteSetKernel_map_pullback_translate
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (s : NNReal) (I : Finset NNReal) :
    (finiteSetKernel P (finiteSetTranslate s I)).map
        (pullbackFiniteSetTranslate (alpha := alpha) s I) =
      (finiteSetKernel P I).comp (P s) := by
  rw [finiteSetKernel_eq_map, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [pullback_orderedPathToFiniteSet, Kernel.map_comp_right]
    · rw [hP.finiteTimeKernel_map_restrictPath P
          (finiteSetTimes (finiteSetTranslate s I))
          (finiteSetTranslateFinOrderIso s I).toOrderEmbedding,
        finiteSetTimes_translate, hP.p2m_embedded_0ec3a889487f427f P s,
        Kernel.map_comp]
    · exact FiniteOrderedTimes.measurable_restrictPath
        (finiteSetTranslateFinOrderIso s I).toOrderEmbedding
    · exact measurable_orderedPathToFiniteSet I
  · exact measurable_orderedPathToFiniteSet (finiteSetTranslate s I)
  · exact measurable_pullbackFiniteSetTranslate s I

end IsConservative

end
end SubMarkovKernelSemigroup
end MarkovProcess

#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteSetKernel_map_pullback_translate


