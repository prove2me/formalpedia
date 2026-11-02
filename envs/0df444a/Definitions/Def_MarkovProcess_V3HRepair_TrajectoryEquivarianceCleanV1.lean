-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_TrajectoryEquivarianceCleanV1
-- name    : MarkovProcess_V3HRepair_TrajectoryEquivarianceCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:26:52.80209+00:00
-- url     : https://prove2.me/theorems/b02bc72b-7f76-42f0-9331-1cb77638655a
-- title:
--   Verified MarkovProcess source repair: TrajectoryEquivarianceCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess TrajectoryEquivarianceCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.TrajectoryEquivarianceCleanV1 source SHA-256 e6a9be3b9ac65a6b3e2af4f1a3cd0ff6d3c5a09a23093bfa45de1ba6fc74a047. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets c907a860-c581-42c3-b866-438b1ef42566, 9c1768f3-b4c1-4a48-86db-7cd6c3fc8f58, e59588fd-6528-4252-bcda-141b4e9fb110, d388181f-f7a3-4ec6-8c28-c0819d16e460; these add no mathematical assumptions.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Trajectory_Equivariance_2a745e86
import Definitions.Def_MarkovProcess_V3HRepair_FiniteKernelEquivarianceCleanV2
import Definitions.Def_MarkovProcess_V3HRepair_EquivarianceOrderedEvaluationCleanV2
import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentUniquenessCleanV1
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

namespace ContinuousPath

section Rescale

variable {alpha beta gamma : Type*} [TopologicalSpace alpha] [TopologicalSpace beta]
  [TopologicalSpace gamma]

/-- Time scaling, evaluated. -/
@[simp]
theorem timeScaling_apply (c t : NNReal) : timeScaling c t = c * t := rfl

/-- The rescaled path, evaluated: `e` applied to the path at the sped-up time. -/
@[simp]
theorem rescale_apply (e : alpha ≃ₜ beta) (c : NNReal) (omega : ContinuousPath alpha)
    (t : NNReal) : rescale e c omega t = e (omega (c * t)) :=
  rfl

/-- Rescaling by the identity homeomorphism and the factor one is the identity. -/
@[simp]
theorem rescale_refl_one (omega : ContinuousPath alpha) :
    rescale (Homeomorph.refl alpha) 1 omega = omega := by
  ext t
  simp only [rescale_apply, Homeomorph.refl_apply, id_eq, one_mul]

/-- Rescaling by the identity homeomorphism speeds the path up without touching the state. -/
@[simp]
theorem rescale_refl_apply (c : NNReal) (omega : ContinuousPath alpha) (t : NNReal) :
    rescale (Homeomorph.refl alpha) c omega t = omega (c * t) :=
  rfl

/-- Rescaling by the time factor one conjugates the state without touching the time. -/
@[simp]
theorem rescale_one_apply (e : alpha ≃ₜ beta) (omega : ContinuousPath alpha) (t : NNReal) :
    rescale e 1 omega t = e (omega t) := by
  simp only [rescale_apply, one_mul]

/-- Rescaling is jointly functorial in the homeomorphism and the time factor. -/
theorem rescale_rescale (e : beta ≃ₜ gamma) (d : alpha ≃ₜ beta) (c b : NNReal)
    (omega : ContinuousPath alpha) :
    rescale e c (rescale d b omega) = rescale (d.trans e) (b * c) omega := by
  ext t
  simp only [rescale_apply, Homeomorph.trans_apply, mul_assoc]

/-- Rescaling is continuous for the compact-open topology. -/
theorem continuous_rescale (e : alpha ≃ₜ beta) (c : NNReal) :
    Continuous (rescale e c : ContinuousPath alpha → ContinuousPath beta) :=
  (ContinuousMap.continuous_postcomp (e : C(alpha, beta))).comp
    (ContinuousMap.continuous_precomp (timeScaling c))

/-- Rescaling is Borel measurable on continuous-path space. -/
theorem measurable_rescale (e : alpha ≃ₜ beta) (c : NNReal) :
    Measurable (rescale e c : ContinuousPath alpha → ContinuousPath beta) :=
  (continuous_rescale e c).measurable

/-- Reading a rescaled path at a finite set of times reads the original path at the sped-up
times and conjugates the states. -/
theorem finsetEvaluation_rescale (e : alpha ≃ₜ beta) (c : NNReal) (I : Finset NNReal)
    (omega : ContinuousPath alpha) :
    finsetEvaluation I (rescale e c omega) = fun t : I ↦ e (omega (c * (t : NNReal))) :=
  rfl

end Rescale

end ContinuousPath

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

section TwoSpaces

variable {beta : Type*} [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P' : SubMarkovKernelSemigroup beta) (hP' : P'.IsConservative)

/-- **Equivariance of the continuous-path process.**  If `P'` is the rescaled conjugate of a
conservative Feller semigroup `P` by the homeomorphism `e` and the positive time factor `c`, then
the continuous-path process of `P'` is the continuous-path process of `P`, started at the
`e`-preimage of the initial state and pushed forward by the path map `ContinuousPath.rescale e c`.

The Feller hypothesis is needed only for `P`, because only the marginals of `P` at arbitrary real
times are used; `P'` enters through its Kolmogorov regularity alone. -/
theorem IsConservative.continuousProcess_eq_map_rescale
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hK' : P'.KolmogorovRegular hP') {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' e c) :
    continuousProcess P' hP' =
      (Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e c) := by
  classical
  let : IsMarkovKernel
      ((Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e c)) :=
    Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_rescale e c)
  refine (IsConservative.eq_continuousProcess_of_map_finiteEvaluation P' hP' hK' _ ?_).symm
  intro I
  have hmapPath : Measurable
      ((FiniteOrderedTimes.mapPath e : (I → alpha) → I → beta) ∘
        orderedPathToFiniteSet (α := alpha) I) :=
    (FiniteOrderedTimes.measurable_mapPath e.measurable).comp
      (measurable_orderedPathToFiniteSet I)
  have hfinite : Measurable (ContinuousPath.finiteEvaluation (α := alpha)
      (fun i ↦ ((finiteSetTimes I).rescale c hc) i)) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finsetEvaluation (alpha := beta) I ∘
        ContinuousPath.rescale e c =
      ((FiniteOrderedTimes.mapPath e : (I → alpha) → I → beta) ∘
        orderedPathToFiniteSet (α := alpha) I) ∘
        ContinuousPath.finiteEvaluation (α := alpha)
          (fun i ↦ ((finiteSetTimes I).rescale c hc) i) := by
    funext omega t
    show e (omega (c * (t : NNReal))) =
      e (omega (c * finiteSetTimes I ((I.orderIsoOfFin rfl).symm t)))
    rw [finiteSetTimes_orderIsoOfFin_symm_apply]
  rw [← Kernel.map_comp_right _ (ContinuousPath.measurable_rescale e c)
      (ContinuousPath.measurable_finiteEvaluation (fun t : I ↦ (t : NNReal))), hcomp,
    Kernel.map_comp_right _ hfinite hmapPath,
    ← Kernel.comap_map_comm _ e.symm.measurable hfinite,
    IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered P hP hFeller hK
      ((finiteSetTimes I).rescale c hc),
    IsRescaledConjugate.finiteSetKernel_eq h hc hP I]

/-- The equivariance identity at a fixed starting state: the law of the process of `P'` started at
`x` is the law of the process of `P` started at `e.symm x`, pushed forward by the rescaling map. -/
theorem IsConservative.continuousProcess_apply_rescale
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hK' : P'.KolmogorovRegular hP') {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' e c) (x : beta) :
    continuousProcess P' hP' x =
      ((continuousProcess P hP) (e.symm x)).map (ContinuousPath.rescale e c) := by
  rw [IsConservative.continuousProcess_eq_map_rescale P hP P' hP' hFeller hK hK' hc h,
    Kernel.map_apply _ (ContinuousPath.measurable_rescale e c), Kernel.comap_apply]

/-- **Intrinsic form of the equivariance theorem.**  When the state map is an isometry, the
Kolmogorov moment criterion for `P` alone gives the regularity of both processes, by
`IsRescaledConjugate.hasKolmogorovMoments`; no hypothesis on `P'` beyond conservativity and the
intertwining is then needed. -/
theorem IsConservative.continuousProcess_eq_map_rescale_of_hasKolmogorovMoments
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) {e : alpha ≃ₜ beta}
    (he : Isometry (e : alpha → beta)) {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' e c) :
    continuousProcess P' hP' =
      (Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e c) :=
  IsConservative.continuousProcess_eq_map_rescale P hP P' hP' hFeller
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
    (KolmogorovRegular.of_hasKolmogorovMoments P' hP' (h.hasKolmogorovMoments he hmom)) hc h

end TwoSpaces

section OneSpace

variable (P' : SubMarkovKernelSemigroup alpha) (hP' : P'.IsConservative)

/-- **Pure time rescaling.**  If the transition kernels of `P'` are those of `P` at the sped-up
times, then the continuous-path process of `P'` is the continuous-path process of `P` pushed
forward by the time change `omega ↦ fun t ↦ omega (c * t)`.  No state map is involved, so no
starting point has to be relabelled. -/
theorem IsConservative.continuousProcess_eq_map_timeRescale
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hK' : P'.KolmogorovRegular hP') {c : NNReal} (hc : 0 < c)
    (htime : ∀ t, P' t = P (c * t)) :
    continuousProcess P' hP' =
      (continuousProcess P hP).map (ContinuousPath.rescale (Homeomorph.refl alpha) c) := by
  have hid : (⇑(Homeomorph.refl alpha) : alpha → alpha) = id := rfl
  have h : IsRescaledConjugate P P' (Homeomorph.refl alpha) c := by
    intro t x
    rw [htime t, hid, Measure.map_id]
    rfl
  have hcomap : Kernel.comap (continuousProcess P hP)
      (⇑(Homeomorph.refl alpha).symm) (Homeomorph.refl alpha).symm.measurable =
        continuousProcess P hP := Kernel.comap_id' _
  rw [IsConservative.continuousProcess_eq_map_rescale P hP P' hP' hFeller hK hK' hc h, hcomap]

/-- **Pure conjugation.**  If the transition kernels of `P'` are those of `P` conjugated by a
homeomorphism `e` of the state space, then the continuous-path process of `P'` is the process of
`P` started at `e.symm x` and read through `e` at every time. -/
theorem IsConservative.continuousProcess_eq_map_conjugate
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hK' : P'.KolmogorovRegular hP') {e : alpha ≃ₜ alpha}
    (hconj : ∀ t x, P' t x = ((P t) (e.symm x)).map e) :
    continuousProcess P' hP' =
      (Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e 1) := by
  refine IsConservative.continuousProcess_eq_map_rescale P hP P' hP' hFeller hK hK' one_pos ?_
  intro t x
  rw [hconj t x, one_mul]

end OneSpace

end

end SubMarkovKernelSemigroup

end MarkovProcess

#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_conjugate

noncomputable def MarkovProcess.V3HRepairProof_c907a860c58142c3b866438b1ef42566 :=
  @MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_conjugate

noncomputable def MarkovProcess.V3HRepairProof_9c1768f3b4c14a4886db7cd6c3fc8f58 :=
  @MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale

noncomputable def MarkovProcess.V3HRepairProof_e59588fd65284252bcda141b4e9fb110 :=
  @MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale_of_hasKolmogorovMoments

noncomputable def MarkovProcess.V3HRepairProof_d388181ff7a34ec68c28c0819d16e460 :=
  @MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_timeRescale


