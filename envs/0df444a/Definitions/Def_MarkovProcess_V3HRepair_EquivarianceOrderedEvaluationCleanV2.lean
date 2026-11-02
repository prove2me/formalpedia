-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_EquivarianceOrderedEvaluationCleanV2
-- name    : MarkovProcess_V3HRepair_EquivarianceOrderedEvaluationCleanV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:14:18.340441+00:00
-- url     : https://prove2.me/theorems/7437bc2d-429e-441a-a3aa-b053a2607d08
-- title:
--   Verified MarkovProcess source repair: EquivarianceOrderedEvaluationCleanV2
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess EquivarianceOrderedEvaluationCleanV2 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.EquivarianceOrderedEvaluationCleanV2 source SHA-256 11a8107f272ac8b508842a6dcf86918e84b52d0858fc2e8871479d1b4890c3fd. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets bb9c2e31-1e6a-4ea6-876e-d326a867d1f7; these add no mathematical assumptions.

import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentUniquenessCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_FinsetEvaluationMeasurabilityCleanV1
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
/-- The increasing enumeration of a finite set of times, read at the position of one of its
elements, returns that element. -/
theorem finiteSetTimes_orderIsoOfFin_symm_apply (I : Finset NNReal) (t : I) :
    finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) = (t : NNReal) := by
  show I.orderEmbOfFin rfl ((I.orderIsoOfFin rfl).symm t) = (t : NNReal)
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]


end SubMarkovKernelSemigroup
namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **Marginals at arbitrary ordered times.**  The law of the continuous-path process of a
conservative Feller semigroup, read at a strictly increasing finite family of nonnegative times,
is the finite-time kernel of `P` at those times.  This is the finite-set marginal theorem of
`MarkovProcess/Main.lean` transported to an arbitrary strictly increasing indexing. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) {n : ℕ}
    (times : FiniteOrderedTimes n) :
    (continuousProcess P hP).map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
      finiteTimeKernel P times := by
  classical
  have hmem : ∀ i : Fin n,
      times i ∈ Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n)) :=
    fun i ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)
  let I : Finset NNReal := Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n))
  let phi : Fin n ↪o I :=
    OrderEmbedding.ofStrictMono (fun i ↦ (⟨times i, hmem i⟩ : I))
      (fun _ _ hij ↦ times.strictMono hij)
  let emb : Fin n ↪o Fin I.card := phi.trans (I.orderIsoOfFin rfl).symm.toOrderEmbedding
  have hphi : ∀ i : Fin n, ((phi i : I) : NNReal) = times i := fun _ ↦ rfl
  have hsel : Measurable (fun w : I → alpha ↦ w ∘ (phi : Fin n → I)) :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (phi i)
  have hfinset : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha) I) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finiteEvaluation (α := alpha) (fun i ↦ times i) =
      (fun w : I → alpha ↦ w ∘ (phi : Fin n → I)) ∘
        ContinuousPath.finsetEvaluation (alpha := alpha) I := rfl
  have hrestrict : (fun w : I → alpha ↦ w ∘ (phi : Fin n → I)) ∘
      orderedPathToFiniteSet (α := alpha) I = FiniteOrderedTimes.restrictPath emb := rfl
  have htimes : (finiteSetTimes I).restrict emb = times := by
    apply DFunLike.ext _ _
    intro i
    show finiteSetTimes I ((I.orderIsoOfFin rfl).symm (phi i)) = times i
    rw [finiteSetTimes_orderIsoOfFin_symm_apply, hphi i]
  rw [hcomp, Kernel.map_comp_right _ hfinset hsel,
    hFeller.continuousProcess_map_finiteEvaluation P hP hK I, finiteSetKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet I) hsel, hrestrict,
    hP.finiteTimeKernel_map_restrictPath P (finiteSetTimes I) emb, htimes]


end
end SubMarkovKernelSemigroup
end MarkovProcess

#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered

noncomputable def MarkovProcess.V3HRepairProof_bb9c2e311e6a4ea6876ed326a867d1f7 :=
  @MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered


