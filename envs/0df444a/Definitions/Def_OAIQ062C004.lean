-- Prove2me | Definitions.Def_OAIQ062C004
-- name    : OAIQ062C004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:59:42.838994+00:00
-- url     : https://prove2.me/theorems/f4794493-05e0-48ba-a9a5-40b94cc22a40
-- title:
--   Definitions bundle OAIQ062C004 of the split of OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 468 declarations of OpenAI's Lean: 100 definitions, 2 inductive types or structures, 1 instance and 365 theorems. The definitions and types are `OAI.Coulomb.AtomicBudgetHistory.initial`, `OAI.Coulomb.AtomicScaleWindow`, `OAI.Coulomb.GroupAntisymmetric`, `OAI.Coulomb.GroupFermionicCoefficients`, `OAI.Coulomb.H1Vector.OuterSliceRegular`, `OAI.Coulomb.H1Vector.add`, `OAI.Coulomb.H1Vector.gradientL2`, `OAI.Coulomb.H1Vector.hardyMultiplier`, `OAI.Coulomb.H1Vector.ofL2`, `OAI.Coulomb.H1Vector.outerSlice`, `OAI.Coulomb.H1Vector.valueL2`, `OAI.Coulomb.RecordedEnsemble.CoreSupported`, `OAI.Coulomb.RecordedEnsemble.InnerEnvelope`, `OAI.Coulomb.RecordedEnsemble.OutFermionic`, `OAI.Coulomb.RecordedEnsemble.coreDeficitMoment`, `OAI.Coulomb.RecordedEnsemble.coreMean`, `OAI.Coulomb.RecordedEnsemble.dataRMS`, `OAI.Coulomb.RecordedEnsemble.deletedSquare`, `OAI.Coulomb.RecordedEnsemble.favorableMass`, `OAI.Coulomb.RecordedEnsemble.initial`, `OAI.Coulomb.RecordedEnsemble.innerSquare`, `OAI.Coulomb.RecordedEnsemble.totalCoreForm`, `OAI.Coulomb.SmoothBoundedCoefficient`, `OAI.Coulomb.SourceFreeHoleDensity`, `OAI.Coulomb.annularAddbackKernel`, `OAI.Coulomb.annularAngle`, `OAI.Coulomb.annularBand`, `OAI.Coulomb.annularCut`, `OAI.Coulomb.annularIMSCost`, `OAI.Coulomb.arrayStatistic`, `OAI.Coulomb.atom`, `OAI.Coulomb.atomicAttractionExcess`, `OAI.Coulomb.atomicBudgetRawSup`, `OAI.Coulomb.atomicBudgetRawValues`, `OAI.Coulomb.atomicBudgetRecursionA`, `OAI.Coulomb.atomicBudgetRecursionC`, `OAI.Coulomb.atomicComparisonExpression`, `OAI.Coulomb.atomicIMSConstant`, `OAI.Coulomb.atomicPatchCap`, `OAI.Coulomb.atomicPatchCountFactor` and 62 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombRadii_FieldAnalysis_AtomicStability`, `CoulombRadii_FieldAnalysis_BodyCoefficient`, `CoulombRadii_FieldAnalysis_ComplexMollify`, `CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv`, `CoulombRadii_FieldAnalysis_CoreCoulombPotential`, `CoulombRadii_FieldAnalysis_CorePerm`, `CoulombRadii_FieldAnalysis_CoulombBilinear`, `CoulombRadii_FieldAnalysis_CoulombTest`, `CoulombRadii_FieldAnalysis_CubeLabelEquiv`, `CoulombRadii_FieldAnalysis_CubeMeasure`, `CoulombRadii_FieldAnalysis_FarSubmean`, `CoulombRadii_FieldAnalysis_FieldSubmean`, `CoulombRadii_FieldAnalysis_FrameOperator`, `CoulombRadii_FieldAnalysis_Gaussian`, `CoulombRadii_FieldAnalysis_GroupFermionicCoefficients`, `CoulombRadii_FieldAnalysis_IntegrableIntegralAeTendsto`, `CoulombRadii_FieldAnalysis_MeridianMap`, `CoulombRadii_FieldAnalysis_OuterJoinConfiguration`, `CoulombRadii_FieldAnalysis_PhaseRegion`, `CoulombRadii_FieldAnalysis_RawObservable`, `CoulombRadii_FieldAnalysis_RawThomasFermiEnergy`, `CoulombRadii_FieldAnalysis_RestrictedField`, `CoulombRadii_FieldAnalysis_RetainedFineDensity`, `CoulombRadii_FieldAnalysis_RetainedFinePower`, `CoulombRadii_FieldAnalysis_Rotation`, `CoulombRadii_FieldAnalysis_SliceExpectation`, `CoulombRadii_FieldAnalysis_SortedObservable`, `CoulombRadii_FieldAnalysis_Space`, `CoulombRadii_FieldAnalysis_SpinMode`, `CoulombRadii_FieldAnalysis_UniformBall`, `CoulombRadii_FormDomain_Add`, `CoulombRadii_FormDomain_AppendJensen`, `CoulombRadii_FormDomain_CoreKinetic`, `CoulombRadii_FormDomain_H1VectorL2`, `CoulombRadii_FormDomain_L2MultiplierContinuity`, `CoulombRadii_FormDomain_OrbitalHilbertBasis`, `CoulombRadii_FormDomain_PatchErrors`, `CoulombRadii_FormDomain_PhysicalEnsemble`, `CoulombRadii_FormDomain_SchwartzSquareIntegrable`, `CoulombRadii_Localization_AnnularCut`, `CoulombRadii_Localization_AtomicHistory`, `CoulombRadii_Localization_CutCombinatorics`, `CoulombRadii_Localization_DeletedLabels`, `CoulombRadii_Localization_DensityCut`, `CoulombRadii_Localization_RadialCut`, `CoulombRadii_Localization_ShellChoice`, `CoulombRadii_Localization_ThinCut`, `CoulombRadii_Localization_ThinIMS`, `CoulombRadii_Localization_TruncatedCoulomb`, `CoulombRadii_Packets_AnnularAddback`, `CoulombRadii_Packets_AnnularIMS`, `CoulombRadii_Packets_AtomicMesh`, `CoulombRadii_Packets_CoulombKernelFiveHalvesIntegrable`, `CoulombRadii_Packets_FineKernelShiftCoulombIntegrable`, `CoulombRadii_Packets_InnerMeshCap`, `CoulombRadii_Packets_PacketIndex`, `CoulombRadii_Packets_PacketSynthesis`, `CoulombRadii_Packets_PacketSynthesisIndicator`, `CoulombRadii_Packets_PacketWindowed`, `CoulombRadii_Packets_ScaledWindow`, `CoulombRadii_Packets_ScreenBox`, `CoulombRadii_Packets_TailMoment`, `CoulombRadii_Propagation_EnsembleMoments`, `CoulombRadii_Propagation_UniformScreening`, `CoulombRadii_RandomFields_AtomicThinScreening`, `CoulombRadii_RandomFields_BinaryDeletion`, `CoulombRadii_RandomFields_ConditionalEnergy`, `CoulombRadii_RandomFields_ConditionalRMS`, `CoulombRadii_RandomFields_EnsembleCauchy`, `CoulombRadii_RandomFields_EnsembleCoveredCost`, `CoulombRadii_RandomFields_ExactRecordedCount`, `CoulombRadii_RandomFields_InnerFieldRMS`, `CoulombRadii_RandomFields_JointSlice`, `CoulombRadii_RandomFields_RawCap`, `CoulombRadii_RandomFields_RecordedCount`, `CoulombRadii_RandomFields_RecordedEnsemble`, `CoulombRadii_RandomFields_RecordedStatistic`, `CoulombRadii_RandomFields_ThinEnsemble`, `CoulombRadii_Screening_AtomicBudgetScreening`, `CoulombRadii_Screening_AtomicPatchCap`, `CoulombRadii_Screening_CoreCount`, `CoulombRadii_Screening_CountMoments`, `CoulombRadii_Screening_CountScalar`, `CoulombRadii_Screening_CountUnits`, `CoulombRadii_Screening_CoveredOutCost`, `CoulombRadii_Screening_FineCountTest`, `CoulombRadii_Screening_OutCap`, `CoulombRadii_Screening_PatchComparison`, `CoulombRadii_Screening_ScaledTest`, `CoulombRadii_Screening_ScreenNumeric`, `CoulombRadii_Screening_SharpThinScreening`, `CoulombRadii_Screening_UniformCountConsequences`, `CoulombRadii_SpectralTheory_EigenspaceBasisSet`, `CoulombRadii_SpectralTheory_SectorFormBottom`, `CoulombRadii_ThomasFermi_AtomicThinCounts`, `CoulombRadii_ThomasFermi_BinaryEnsemble`, `CoulombRadii_ThomasFermi_LpParameter`, `CoulombRadii_ThomasFermi_PatchGeometry`, `CoulombRadii_ThomasFermi_TFExponent`, `CoulombRadii_ThomasFermi_TFNonneg`, `CoulombRadii_ThomasFermi_TfExtendNonneg`, `CoulombRadii_ThomasFermi_TfFunctionalGapControl`, `CoulombRadii_ThomasFermi_TfFunctionalUniformBound`, `CoulombRadii_ThomasFermi_TfPotential`, `CoulombRadii_Variational_PhysicalBridge`.
--
--   **Imports.** It imports the published bundle `Def_CoulombRadii`; the bundles `OAIQ062C000` and `OAIQ062C001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ062C006` and `OAIQ062C007`; the statements `OAI.Coulomb.RecordedEnsemble.atomic_zero_offset_core_deletion`, `OAI.Coulomb.atom_global_sector_minimum`, `OAI.Coulomb.atom_strict_binding_attained`, `OAI.Coulomb.strictly_bound_sequence_tight`, `OAI.NeutralAtom.physical_initial_event`, `OAI.NeutralAtom.physical_neutral_energy_offset`, `OAI.NeutralAtom.physical_normalized_inverse_point` and `OAI.NeutralAtom.physical_observed_small_annular_count_tail`.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C000
import Definitions.Def_OAIQ062C001

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

namespace Coulomb

noncomputable def totalCharge {M : ℕ} (S : Nuclei M) : ℝ := ∑ j, S.charge j

def atom (Z : ℕ) (hZ : 1 ≤ Z) : Nuclei 1 where
  nonempty := by decide
  position := fun _ => 0
  distinct := fun a b _ => Subsingleton.elim a b
  charge := fun _ => Z
  charge_ge_one := by intro j; exact_mod_cast hZ

theorem mass_smooth_partition {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, mass (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) = mass ψ := by
  classical
  let χ := fun i => ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)
  change (∑ i, mass (χ i)) = mass ψ
  have hblock : ∀ s, (∑ i, ∫ x, ‖(χ i).value s x‖ ^ 2) =
      ∫ x, ‖ψ.value s x‖ ^ 2 := by
    intro s
    rw [← integral_finsetSum _ (fun i _ =>
      ((χ i).value_L2 s).integrable_norm_pow (p := 2) (by decide))]
    apply integral_congr_ae
    filter_upwards [] with x
    change (∑ i, ‖(f i x : ℂ) * ψ.value s x‖ ^ 2) = ‖ψ.value s x‖ ^ 2
    simp_rw [norm_real_mul_sq]
    rw [← Finset.sum_mul, hpart, one_mul]
  unfold mass
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun s _ => hblock s)

open ContinuousLinearMap
open scoped Convolution

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

section CompleteProducts
variable {A B ι κ : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    [Countable ι]

theorem completeOrbitals_tensorPair {v : ι → A → ℂ} {w : κ → B → ℂ}
    (hv : ∀ i, MemLp (v i) 2 μ) (hw : ∀ j, MemLp (w j) 2 ν)
    (hc : CompleteOrbitals μ v) (hd : CompleteOrbitals ν w) :
    CompleteOrbitals (ν.prod μ) (fun ij : κ × ι => fun z => w ij.1 z.1 * v ij.2 z.2) := by
  intro f hf hz
  have hzero : ∀ i, fiberContract (μ := μ) (v i) f =ᵐ[ν] 0 := by
    intro i
    apply hd _ (fiberContract_memLp (hv i) hf)
    intro j
    rw [← integral_tensorPair (hw j) (hv i) hf]
    exact hz (j, i)
  have hslice : ∀ᵐ b ∂ν, (fun a => f (b, a)) =ᵐ[μ] 0 := by
    filter_upwards [memLp_fiber_ae hf, ae_all_iff.mpr hzero] with b hb hbi
    apply hc _ hb
    exact hbi
  have hi : (∫ z, ‖f z‖ ^ 2 ∂(ν.prod μ)) = 0 := by
    rw [integral_prod _ hf.norm.integrable_sq]
    apply integral_eq_zero_of_ae
    filter_upwards [hslice] with b hb
    apply integral_eq_zero_of_ae
    filter_upwards [hb] with a ha
    simp [ha]
  have hz' := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖f z‖)
    hf.norm.integrable_sq).1 hi
  filter_upwards [hz'] with z h
  simpa only [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero] using h

end CompleteProducts

theorem completeOrbitals_finPi {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] [Countable ι] (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (hc : CompleteOrbitals μ v) (n : ℕ) :
    CompleteOrbitals (Measure.pi fun _ : Fin n => μ)
      (fun b : Fin n → ι => fun x => ∏ i, v (b i) (x i)) := by
  induction n with
  | zero =>
    intro f hf hz
    have h := hz (fun i => Fin.elim0 i)
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext x
      congr 1
      exact Subsingleton.elim _ _
    have hcp : (∫ x, f x ∂(Measure.pi fun _ : Fin 0 => μ)) =
        f (fun i => Fin.elim0 i) := by
      rw [he]
      simp [Measure.real, Measure.pi_empty_univ]
    have hh : (∫ x, f x ∂(Measure.pi fun _ : Fin 0 => μ)) = 0 := by
      simpa only [Fin.prod_univ_zero, star_one, one_mul] using h
    rw [hcp] at hh
    filter_upwards with x
    have hx : x = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    simpa only [hx, Pi.zero_apply] using hh
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0
    have hp : MeasurePreserving e (Measure.pi fun _ => μ)
        (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have ht := (completeOrbitals_tensorPair
      (fun (b : Fin n → ι) => scalarTensor_memLp v hv b) hv ih hc).comp e hp
    intro f hf hz
    apply ht f hf
    intro ib
    have hz' := hz (Fin.insertNth 0 ib.1 ib.2)
    convert hz' using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    dsimp only
    congr 1
    rw [Fin.prod_univ_succAbove _ 0]
    simp [e, MeasurableEquiv.piFinSuccAbove, Fin.tail]

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_OrbitalHilbertBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical

noncomputable def orbitalHilbertBasis {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) : HilbertBasis ι ℂ (Lp ℂ 2 μ) :=
  HilbertBasis.mkOfOrthogonalEqBot (v := fun i => (hv i).toLp (v i))
    (by rw [orthonormal_iff_ite]; intro i j; rw [inner_toLp_complex]; exact ho i j)
    (by
      apply (Submodule.eq_bot_iff _).mpr
      intro f hf
      apply Lp.eq_zero_iff_ae_eq_zero.mpr
      apply hc f (Lp.memLp f)
      intro i
      have he := (Submodule.mem_orthogonal _ _).1 hf ((hv i).toLp (v i))
        (Submodule.subset_span (Set.mem_range_self i))
      have hi := inner_toLp_complex (hv i) (Lp.memLp f)
      simp only [Lp.toLp_coeFn] at hi
      rwa [hi] at he)

lemma orbitalHilbertBasis_apply {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (i : ι) :
    orbitalHilbertBasis v hv ho hc i = (hv i).toLp (v i) := by
  simp only [orbitalHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem completeOrbitals_parseval {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (f : A → ℂ) (hf : MemLp f 2 μ) :
    (∑' i, ‖∫ a, star (v i a) * f a ∂μ‖ ^ 2) = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  have h := hilbertBasis_parseval (orbitalHilbertBasis v hv ho hc) (hf.toLp f)
  simpa only [orbitalHilbertBasis_apply, inner_toLp_complex, norm_toLp_sq_complex] using h

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CubeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
section TensorNeumann
variable {A ι : Type*} [MeasurableSpace A] {ν : Measure A} [SigmaFinite ν]

lemma neumann_tensor_coefficient_derivative {b : ℝ} (hb : 0 < b)
    {f g : A × ℝ → ℂ} {w : A → ℂ}
    (hw : MemLp w 2 ν)
    (hf : MemLp f 2 (ν.prod (volume.restrict (Ioc 0 b))))
    (hg : MemLp g 2 (ν.prod (volume.restrict (Ioc 0 b))))
    (hd : ∀ᵐ a ∂ν, ∀ x ∈ Icc 0 b,
      HasDerivAt (fun t => f (a,t)) (g (a,x)) x) (n : ℕ) :
    (((((n : ℝ) + 1) * Real.pi / b : ℝ)) : ℂ) *
      (∫ z, star (w z.1 * neumannMode b (n+1) z.2) * f z
        ∂(ν.prod (volume.restrict (Ioc 0 b)))) =
      -(∫ z, star (w z.1 * dirichletMode b n z.2) * g z
        ∂(ν.prod (volume.restrict (Ioc 0 b)))) := by
  rw [integral_tensorPair hw (neumannMode_memLp b (n+1)) hf,
    integral_tensorPair hw (dirichletMode_memLp b n) hg,
    ← integral_const_mul, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hd, memLp_fiber_ae hg] with a hda hga
  have he := neumann_coefficient_derivative hb hda hga n
  dsimp only [fiberContract]
  calc
    _ = star (w a) * (((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) *
        (∫ t in Ioc 0 b, star (neumannMode b (n+1) t) * f (a,t))) := by ring
    _ = _ := by rw [he]; ring

theorem neumann_tensor_smooth_spectral_lower [DecidableEq ι] {b : ℝ} (hb : 0 < b)
    (w : ι → A → ℂ) (hw : ∀ i, MemLp (w i) 2 ν)
    (ho : ∀ i j, (∫ a, star (w i a) * w j a ∂ν) = if i = j then (1 : ℂ) else 0)
    {f g : A × ℝ → ℂ}
    (hf : MemLp f 2 (ν.prod (volume.restrict (Ioc 0 b))))
    (hg : MemLp g 2 (ν.prod (volume.restrict (Ioc 0 b))))
    (hd : ∀ᵐ a ∂ν, ∀ x ∈ Icc 0 b,
      HasDerivAt (fun t => f (a,t)) (g (a,x)) x) (s : Finset (ι × ℕ)) :
    ∑ q ∈ s, ((((q.2 : ℝ) + 1) * Real.pi / b)^2 *
      ‖∫ z, star (w q.1 z.1 * neumannMode b (q.2+1) z.2) * f z
        ∂(ν.prod (volume.restrict (Ioc 0 b)))‖^2) ≤
      ∫ z, ‖g z‖^2 ∂(ν.prod (volume.restrict (Ioc 0 b))) := by
  classical
  let u : (ι × ℕ) → Lp ℂ 2 (ν.prod (volume.restrict (Ioc 0 b))) :=
    fun q => (tensorPair_memLp (hw q.1) (dirichletMode_memLp b q.2)).toLp
      (fun z => w q.1 z.1 * dirichletMode b q.2 z.2)
  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro q r
    rw [inner_toLp_complex, tensorPair_inner (dirichletMode_memLp b q.2)
      (dirichletMode_memLp b r.2) (hw q.1) (hw r.1), ho, dirichletMode_orthonormal hb]
    by_cases h1 : q.1 = r.1 <;> by_cases h2 : q.2 = r.2 <;>
      simp [h1, h2, Prod.ext_iff]
  have hB := hu.sum_inner_products_le (hg.toLp g) (s := s)
  rw [norm_toLp_sq_complex hg] at hB
  convert hB using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro q _
  rw [inner_toLp_complex]
  have he := neumann_tensor_coefficient_derivative hb (hw q.1) hf hg hd q.2
  have hnorm := congrArg (fun z : ℂ => ‖z‖^2) he
  simpa only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs] using hnorm

end TensorNeumann

open Filter

open scoped Convolution
open ContinuousLinearMap

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ComplexMollify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma complexMollify_sq_sub {I : Type*} [Fintype I] (k : ℕ)
    (u : EuclideanSpace ℝ I → ℂ) (x : EuclideanSpace ℝ I) :
    ‖complexMollify k u x - u x‖^2 =
      (realMollify k (fun y => (u y).re) x - (u x).re)^2 +
      (realMollify k (fun y => (u y).im) x - (u x).im)^2 := by
  simp [complex_norm_sq_components, complexMollify]

theorem complexMollify_L2_tendsto {I : Type*} [Fintype I]
    {u : EuclideanSpace ℝ I → ℂ} (hu : MemLp u 2) :
    Tendsto (fun k => ∫ x, ‖complexMollify k u x - u x‖^2) atTop (nhds 0) := by
  have hr : MemLp (fun x => (u x).re) 2 := Complex.reCLM.comp_memLp' hu
  have hi : MemLp (fun x => (u x).im) 2 := Complex.imCLM.comp_memLp' hu
  have he (k : ℕ) : (∫ x, ‖complexMollify k u x - u x‖^2) =
      (∫ x, (realMollify k (fun y => (u y).re) x - (u x).re)^2) +
      (∫ x, (realMollify k (fun y => (u y).im) x - (u x).im)^2) := by
    simp_rw [complexMollify_sq_sub]
    exact integral_add ((realMollify_memLp k hr).sub hr).integrable_sq
      ((realMollify_memLp k hi).sub hi).integrable_sq
  simp_rw [he]
  simpa using (realMollify_L2_tendsto hr).add (realMollify_L2_tendsto hi)

lemma toLp_tendsto_of_integral_sq_sub {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} {F : ℕ → A → ℂ} (hf : MemLp f 2 μ) (hF : ∀ k, MemLp (F k) 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun k => (hF k).toLp (F k)) atTop (nhds (hf.toLp f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have he (k : ℕ) : ‖(hF k).toLp (F k) - hf.toLp f‖^2 =
      ∫ x, ‖F k x - f x‖^2 ∂μ := by
    rw [← MemLp.toLp_sub (hF k) hf, norm_toLp_sq_complex]
    rfl
  have ht := (Real.continuous_sqrt.tendsto 0).comp h
  simp only [Real.sqrt_zero] at ht
  change Tendsto (fun k => Real.sqrt (∫ x, ‖F k x - f x‖^2 ∂μ)) atTop (nhds 0) at ht
  simp_rw [← he, Real.sqrt_sq (norm_nonneg _)] at ht
  exact ht

lemma integral_norm_sq_tendsto_of_L2 {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} {F : ℕ → A → ℂ} (hf : MemLp f 2 μ) (hF : ∀ k, MemLp (F k) 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x, ‖F k x‖^2 ∂μ) atTop (nhds (∫ x, ‖f x‖^2 ∂μ)) := by
  simpa only [norm_toLp_sq_complex] using
    (toLp_tendsto_of_integral_sq_sub hf hF h).norm.pow 2

lemma integral_coefficient_tendsto_of_L2 {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f w : A → ℂ} {F : ℕ → A → ℂ}
    (hf : MemLp f 2 μ) (hw : MemLp w 2 μ) (hF : ∀ k, MemLp (F k) 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x, star (w x) * F k x ∂μ) atTop
      (nhds (∫ x, star (w x) * f x ∂μ)) := by
  simpa only [inner_toLp_complex] using
    (tendsto_const_nhds (x := hw.toLp w)).inner (𝕜 := ℂ)
      (toLp_tendsto_of_integral_sq_sub hf hF h)

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

theorem spin_lattice_count (s : Finset SpinMode) {r : ℝ}
    (hr : 0 ≤ r) (hs : ∀ a ∈ s, latticeRadius a.2 ≤ r) :
    (s.card : ℝ) ≤ (Real.pi / 3) * (r + Real.sqrt 3)^3 := by
  classical
  let t := s.image Prod.snd
  have H := spin_two_lattice_count t hr (by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact hs a ha)
  have ht : s ⊆ (Finset.univ : Finset (Fin 2)) ×ˢ t := by
    intro a ha
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  have hc : s.card ≤ 2 * t.card := by simpa using Finset.card_le_card ht
  have hcR : (s.card : ℝ) ≤ 2 * (t.card : ℝ) := by exact_mod_cast hc
  exact hcR.trans H

theorem ordered_lattice_radius_lower {n : ℕ} (a : Fin n → SpinMode)
    (ha : Function.Injective a) (hm : Monotone (fun i => latticeRadius (a i).2))
    (i : Fin n) :
    (3 * ((i.val + 1 : ℕ) : ℝ) / Real.pi) ^ (1/3 : ℝ) ≤
      latticeRadius (a i).2 + Real.sqrt 3 := by
  classical
  let s := (Finset.Iic i).image a
  have hc : s.card = i.val + 1 := by
    rw [Finset.card_image_of_injective _ ha]
    exact Fin.card_Iic i
  have h := spin_lattice_count s (latticeRadius_nonneg _) (by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    exact hm (Finset.mem_Iic.mp hj))
  rw [hc] at h
  have hx : 0 ≤ 3 * ((i.val + 1 : ℕ) : ℝ) / Real.pi := by positivity
  have hy : 0 ≤ latticeRadius (a i).2 + Real.sqrt 3 :=
    add_nonneg (latticeRadius_nonneg _) (Real.sqrt_nonneg _)
  rw [show (1/3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_le_iff_of_pos hx hy (by norm_num)]
  norm_num only [Real.rpow_ofNat]
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith

theorem neumann_radii_sum_lower {n : ℕ} (a : Fin n → SpinMode)
    (ha : Function.Injective a) :
    neumannLeading * (n : ℝ) ^ (5/3 : ℝ) -
      neumannBoundary * (n : ℝ) ^ (4/3 : ℝ) ≤
      ∑ i, (latticeRadius (a i).2)^2 := by
  classical
  obtain ⟨e, he⟩ := finite_sort_values (fun i => latticeRadius (a i).2)
  let A : ℝ := (3/Real.pi) ^ (1/3 : ℝ)
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hAi : A^2 = (3/Real.pi) ^ (2/3 : ℝ) := by
    dsimp only [A]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hl (i : Fin n) :
      A^2 * (((i.val+1 : ℕ) : ℝ) ^ (2/3 : ℝ)) -
       (2 * Real.sqrt 3 * A) * (((i.val+1 : ℕ) : ℝ) ^ (1/3 : ℝ)) ≤
        (latticeRadius (a (e i)).2)^2 := by
    have h := ordered_lattice_radius_lower (fun i => a (e i)) (ha.comp e.injective) he i
    have hx : (3 * ((i.val+1 : ℕ) : ℝ) / Real.pi) ^ (1/3 : ℝ) =
        A * (((i.val+1 : ℕ) : ℝ) ^ (1/3 : ℝ)) := by
      rw [show 3 * ((i.val+1 : ℕ) : ℝ) / Real.pi =
        (3/Real.pi) * ((i.val+1 : ℕ) : ℝ) by ring,
        Real.mul_rpow (by positivity) (by positivity)]
    rw [hx] at h
    have H := square_lower_of_shift (latticeRadius_nonneg _) (mul_nonneg hA (Real.rpow_nonneg (by positivity) _))
      (Real.sqrt_nonneg 3) h
    rw [mul_pow] at H
    have hp : ((((i.val+1 : ℕ) : ℝ) ^ (1/3 : ℝ)))^2 =
        (((i.val+1 : ℕ) : ℝ) ^ (2/3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hp] at H
    nlinarith
  have H := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at H
  have h2 : (3/5 : ℝ) * (n : ℝ) ^ (5/3 : ℝ) ≤
      ∑ i : Fin n, (((i.val+1 : ℕ) : ℝ) ^ (2/3 : ℝ)) := by
    simpa only [Finset.sum_range] using sum_two_thirds_lower n
  have h1 : (∑ i : Fin n, (((i.val+1 : ℕ) : ℝ) ^ (1/3 : ℝ))) ≤
      (n : ℝ) ^ (4/3 : ℝ) := by
    simpa only [Finset.sum_range] using sum_one_third_upper n
  have H2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg A)
  have H1 := mul_le_mul_of_nonneg_left h1
    (show 0 ≤ 2 * Real.sqrt 3 * A by positivity)
  have hs : (∑ i, (latticeRadius (a (e i)).2)^2) =
      ∑ i, (latticeRadius (a i).2)^2 := Equiv.sum_comp e (fun i => (latticeRadius (a i).2)^2)
  rw [hs] at H
  unfold neumannLeading neumannBoundary
  rw [← hAi]
  change (3/5 : ℝ) * A^2 * (n : ℝ) ^ (5/3 : ℝ) -
    (2 * Real.sqrt 3 * A) * (n : ℝ) ^ (4/3 : ℝ) ≤ _
  nlinarith

lemma neumann_coefficient_exact :
    (Real.pi^2/2) * neumannLeading = thomasFermiCoefficient := by
  unfold neumannLeading thomasFermiCoefficient
  rw [Real.div_rpow (by norm_num) Real.pi_pos.le,
    Real.mul_rpow (by norm_num) (sq_nonneg _)]
  have hp : (Real.pi^2) ^ (2/3 : ℝ) = Real.pi^2 / Real.pi ^ (2/3 : ℝ) := by
    rw [← Real.rpow_natCast_mul Real.pi_pos.le 2 (2/3 : ℝ)]
    rw [← Real.rpow_two, ← Real.rpow_sub Real.pi_pos]
    norm_num
  rw [hp]
  ring

theorem neumann_kinetic_sum_lower {n : ℕ} (a : Fin n → SpinMode)
    (ha : Function.Injective a) {b : ℝ} (_hb : 0 < b) :
    (b⁻¹)^2 * (thomasFermiCoefficient * (n : ℝ) ^ (5/3 : ℝ) -
      ((Real.pi^2/2)*neumannBoundary) * (n : ℝ) ^ (4/3 : ℝ)) ≤
      ∑ i, (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 := by
  have H := mul_le_mul_of_nonneg_left (neumann_radii_sum_lower a ha)
    (show 0 ≤ Real.pi^2/(2*b^2) by positivity)
  rw [← Finset.mul_sum]
  have he : (b⁻¹)^2 * (thomasFermiCoefficient * (n : ℝ) ^ (5/3 : ℝ) -
      ((Real.pi^2/2)*neumannBoundary) * (n : ℝ) ^ (4/3 : ℝ)) =
      (Real.pi^2/(2*b^2)) * (neumannLeading * (n : ℝ) ^ (5/3 : ℝ) -
        neumannBoundary * (n : ℝ) ^ (4/3 : ℝ)) := by
    rw [← neumann_coefficient_exact]
    field_simp
  rw [he]
  exact H

lemma cubeMode_complete {b : ℝ} (hb : 0 < b) (d : ℕ) :
    CompleteOrbitals (cubeMeasure b d) (cubeMode b) :=
  completeOrbitals_finPi (neumannMode b) (neumannMode_memLp b) (neumannModes_complete hb) d

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CubeLabelEquiv
attribute [-instance] _root_.OAI.Coulomb.finiteCubeMeasure_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

section FiniteCubeBasis
variable {I : Type*} [Fintype I]

lemma finiteCubeMode_inner {b : ℝ} (hb : 0 < b) (q r : I → ℕ) :
    (∫ x, star (finiteCubeMode b q x) * finiteCubeMode b r x ∂(finiteCubeMeasure b I)) =
      if q = r then (1 : ℂ) else 0 := by
  classical
  simp only [finiteCubeMode, finiteCubeMeasure, star_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : I => volume.restrict (Ioc 0 b))
    (fun i x => star (neumannMode b (q i) x) * neumannMode b (r i) x)]
  simp_rw [neumannMode_orthonormal hb]
  by_cases h : q = r
  · subst r; simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

lemma finiteCubeMode_complete {b : ℝ} (hb : 0 < b) :
    CompleteOrbitals (finiteCubeMeasure b I) (finiteCubeMode b) := by
  classical
  let e := Fintype.equivFin I
  have H := (cubeMode_complete hb (Fintype.card I)).comp (reindexCube e)
    (reindexCube_measurePreserving b e)
  intro f hf hz
  apply H f hf
  intro q
  have he (x : I → ℝ) : cubeMode b q (reindexCube e x) = finiteCubeMode b (q ∘ e) x := by
    have hh := finiteCubeMode_reindex b e (q ∘ e) x
    simpa only [Function.comp_def, e.apply_symm_apply, finiteCubeMode, cubeMode] using hh
  simp_rw [he]
  exact hz (q ∘ e)

end FiniteCubeBasis

noncomputable def cubeLabelEquiv (n : ℕ) :
    (Fin n → SpinMode) ≃ (Spins n × ((Fin n × Fin 3) → ℕ)) where
  toFun a := (fun i => (a i).1, fun ij => (a ij.1).2 ij.2)
  invFun sq := fun i => (sq.1 i, fun j => sq.2 (i,j))
  left_inv a := by rfl
  right_inv sq := by rfl

noncomputable def cubeFermionCoefficient {n : ℕ} (ψ : H1Vector n) (b : ℝ)
    (a : Fin n → SpinMode) : ℂ :=
  ∫ x, star (finiteCubeMode b (cubeLabelEquiv n a).2 x) *
    ψ.value (cubeLabelEquiv n a).1 (WithLp.toLp 2 x)
    ∂(finiteCubeMeasure b (Fin n × Fin 3))

noncomputable def cubeMass {n : ℕ} (ψ : H1Vector n) (b : ℝ) : ℝ :=
  ∑ s, ∫ x, ‖ψ.value s (WithLp.toLp 2 x)‖^2
    ∂(finiteCubeMeasure b (Fin n × Fin 3))

lemma H1Vector.cube_memLp {n : ℕ} (ψ : H1Vector n) (b : ℝ) (s : Spins n) :
    MemLp (fun x => ψ.value s (WithLp.toLp 2 x)) 2
      (finiteCubeMeasure b (Fin n × Fin 3)) :=
  ((ψ.value_L2 s).comp_measurePreserving (PiLp.volume_preserving_toLp _)).mono_measure
    (finiteCubeMeasure_le_volume b)

lemma finiteCubeCoefficient_summable {I : Type*} [Fintype I] {b : ℝ} (hb : 0 < b)
    (f : (I → ℝ) → ℂ) (hf : MemLp f 2 (finiteCubeMeasure b I)) :
    Summable (fun q => ‖∫ x, star (finiteCubeMode b q x) * f x
      ∂(finiteCubeMeasure b I)‖^2) := by
  have ho : Orthonormal ℂ (fun q : I → ℕ => (finiteCubeMode_memLp b q).toLp (finiteCubeMode b q)) := by
    rw [orthonormal_iff_ite]
    intro q r
    rw [inner_toLp_complex]
    exact finiteCubeMode_inner hb q r
  simpa only [inner_toLp_complex] using ho.inner_products_summable (hf.toLp f)

lemma cubeFermionCoefficient_summable {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    Summable (fun a => ‖cubeFermionCoefficient ψ b a‖^2) := by
  let F : Spins n × ((Fin n × Fin 3) → ℕ) → ℝ := fun sq =>
    ‖∫ x, star (finiteCubeMode b sq.2 x) * ψ.value sq.1 (WithLp.toLp 2 x)
      ∂(finiteCubeMeasure b (Fin n × Fin 3))‖^2
  have hs (s : Spins n) : Summable (fun q : (Fin n × Fin 3) → ℕ => F (s,q)) :=
    (by
      dsimp only [F]
      exact finiteCubeCoefficient_summable (I := Fin n × Fin 3) hb
        (fun x => ψ.value s (WithLp.toLp 2 x)) (ψ.cube_memLp b s))
  have hF : Summable F := (summable_prod_of_nonneg (f := F) (fun _ => sq_nonneg _)).2
    ⟨hs, (hasSum_fintype _).summable⟩
  exact (Equiv.summable_iff (cubeLabelEquiv n)).2 hF

lemma cubeFermionCoefficient_parseval {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    (∑' a, ‖cubeFermionCoefficient ψ b a‖^2) = cubeMass ψ b := by
  let F : Spins n × ((Fin n × Fin 3) → ℕ) → ℝ := fun sq =>
    ‖∫ x, star (finiteCubeMode b sq.2 x) * ψ.value sq.1 (WithLp.toLp 2 x)
      ∂(finiteCubeMeasure b (Fin n × Fin 3))‖^2
  have hF : Summable F := (Equiv.summable_iff (cubeLabelEquiv n)).1
    (cubeFermionCoefficient_summable ψ hb)
  change (∑' a, F (cubeLabelEquiv n a)) = _
  rw [(cubeLabelEquiv n).tsum_eq, hF.tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro s _
  exact completeOrbitals_parseval (finiteCubeMode b) (finiteCubeMode_memLp b)
    (fun q r => by
      by_cases hqr : q = r
      · simpa only [ite_eq_left hqr] using finiteCubeMode_inner hb q r
      · simpa only [ite_eq_right hqr] using finiteCubeMode_inner hb q r)
    (finiteCubeMode_complete hb) _ (ψ.cube_memLp b s)

noncomputable def cubeKinetic {n : ℕ} (ψ : H1Vector n) (b : ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ s, ∑ i, ∫ x, ‖ψ.gradient s i (WithLp.toLp 2 x)‖^2
    ∂(finiteCubeMeasure b (Fin n × Fin 3))

noncomputable def cubeSpectralWeight {n : ℕ} (b : ℝ) (a : Fin n → SpinMode) : ℝ :=
  (1/2 : ℝ) * ∑ i : Fin n × Fin 3, (((cubeLabelEquiv n a).2 i : ℝ) * Real.pi / b)^2

lemma cubeSpectralWeight_nonneg {n : ℕ} (b : ℝ) (a : Fin n → SpinMode) :
    0 ≤ cubeSpectralWeight b a := by
  unfold cubeSpectralWeight
  positivity

lemma cubeSpectralWeight_eq_neumann {n : ℕ} (b : ℝ) (a : Fin n → SpinMode) :
    cubeSpectralWeight b a =
      ∑ i, (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 := by
  classical
  unfold cubeSpectralWeight
  simp only [Fintype.sum_prod_type, cubeLabelEquiv, Equiv.coe_fn_mk,
    latticeRadius, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_IntegrableIntegralAeTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma H1Vector.spinSpace_memLp {n : ℕ} (ψ : H1Vector n) :
    MemLp (fun sx : Spins n × ((Fin n × Fin 3) → ℝ) =>
      ψ.value sx.1 (WithLp.toLp 2 sx.2)) 2 (Measure.count.prod volume) := by
  have hi (s : Spins n) : MemLp (fun t : Spins n => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Spins n) _ => tensorPair_memLp (hi s)
    ((ψ.value_L2 s).comp_measurePreserving (PiLp.volume_preserving_toLp _)))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext sx
  simp only [ite_mul, one_mul, zero_mul]
  simp

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_TruncatedCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma truncatedCoulomb_nonneg (R : ℝ) (x : Space) : 0 ≤ truncatedCoulomb R x :=
  Set.indicator_nonneg (fun _ _ => coulombKernel_nonneg _) x
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_MeridianMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma radial_coulomb_lintegral_le (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {x : Space} (hx : x ≠ 0) :
    (∫⁻ y : Space, ENNReal.ofReal ‖x-y‖⁻¹ * F ‖y‖) ≤
      ENNReal.ofReal ‖x‖⁻¹ * ∫⁻ y : Space, F ‖y‖ := by
  calc
    _ = ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s^2*(max ‖x‖ s)⁻¹) * F s :=
      radial_coulomb_lintegral F hF hx
    _ ≤ ENNReal.ofReal (4*Real.pi) *
        ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (‖x‖⁻¹*s^2) * F s := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Ioi
      intro s _
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left
        (inv_anti₀ (norm_pos_iff.mpr hx) (le_max_left ‖x‖ s)) (sq_nonneg s)]
    _ = _ := by
      rw [radial_space_lintegral F hF]
      simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg x)), mul_assoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      ac_rfl

lemma radial_coulomb_integral_le {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ} (hfM : ∀ y, f y ≤ M)
    (hrad : ∀ y, f y = f (EuclideanSpace.single 0 ‖y‖))
    {x : Space} (hx : x ≠ 0) :
    (∫ y, coulombKernel (x-y) * f y) ≤ coulombKernel x * ∫ y, f y := by
  let F : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (f (EuclideanSpace.single 0 s))
  have hmF : Measurable F := (hm.comp space_axis_continuous.measurable).ennreal_ofReal
  have he (y : Space) : F ‖y‖ = ENNReal.ofReal (f y) := congrArg ENNReal.ofReal (hrad y).symm
  have H := radial_coulomb_lintegral_le F hmF hx
  simp_rw [he] at H
  have hi := coulomb_convolution_integrable hf hm hf0 hfM (by norm_num : (0:ℝ) < 1) x
  have hp (y : Space) : 0 ≤ coulombKernel (x-y)*f y := mul_nonneg (coulombKernel_nonneg _) (hf0 _)
  have hI := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hp)
  have hmass := ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0)
  simp_rw [ENNReal.ofReal_mul (coulombKernel_nonneg _)] at hI
  change ENNReal.ofReal (∫ y, coulombKernel (x-y)*f y) =
    ∫⁻ y, ENNReal.ofReal ‖x-y‖⁻¹*ENNReal.ofReal (f y) at hI
  rw [← hI, ← hmass, ← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))] at H
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (coulombKernel_nonneg x) (integral_nonneg hf0))).mp H

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GroupFermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Coulomb

open scoped Classical

open scoped Classical

open Filter
open scoped Convolution
open ContinuousLinearMap

def GroupFermionicCoefficients {n : ℕ} {ι : Type*} (g : Fin n → ι)
    (f : (Fin n → SpinMode) → ℂ) : Prop :=
  ∀ p : Equiv.Perm (Fin n), g ∘ p = g → ∀ a,
    f (a ∘ p) = ((p.sign : ℤ) : ℂ) * f a

lemma GroupFermionicCoefficients.vanish_of_repeat {n : ℕ} {ι : Type*}
    {g : Fin n → ι} {f : (Fin n → SpinMode) → ℂ}
    (hf : GroupFermionicCoefficients g f) {a : Fin n → SpinMode}
    {i j : Fin n} (hne : i ≠ j) (hg : g i = g j) (ha : a i = a j) : f a = 0 := by
  classical
  have hgp : g ∘ Equiv.swap i j = g := by
    funext k
    by_cases hi : k = i
    · subst k; simpa using hg.symm
    by_cases hj : k = j
    · subst k; simpa using hg
    simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  have hap : a ∘ Equiv.swap i j = a := by
    funext k
    by_cases hi : k = i
    · subst k; simpa using ha.symm
    by_cases hj : k = j
    · subst k; simpa using ha
    simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  have H := hf (Equiv.swap i j) hgp a
  rw [hap, Equiv.Perm.sign_swap hne] at H
  norm_num at H
  linear_combination (1/2 : ℂ) * H

noncomputable def groupNeumannLower {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) (b : ℝ) : ℝ :=
  ∑ k : ι, (b⁻¹)^2 *
    (thomasFermiCoefficient * (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (5/3 : ℝ) -
      ((Real.pi^2/2)*neumannBoundary) *
        (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (4/3 : ℝ))

lemma grouped_neumann_spectral_lower {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) (a : Fin n → SpinMode)
    (hinj : Function.Injective (fun i => (g i, a i))) {b : ℝ} (hb : 0 < b) :
    groupNeumannLower g b ≤ cubeSpectralWeight b a := by
  classical
  rw [cubeSpectralWeight_eq_neumann, groupNeumannLower]
  have hlocal (k : ι) :
      (b⁻¹)^2 * (thomasFermiCoefficient *
        (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (5/3 : ℝ) -
      ((Real.pi^2/2)*neumannBoundary) *
        (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (4/3 : ℝ)) ≤
      ∑ i : {i : Fin n // g i = k},
        (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 := by
    let E := Fintype.equivFin {i : Fin n // g i = k}
    have hai : Function.Injective (fun i : {i : Fin n // g i = k} => a i) := by
      intro i j hij
      apply Subtype.ext
      apply hinj
      exact Prod.ext (i.property.trans j.property.symm) hij
    have H := neumann_kinetic_sum_lower (fun i => a (E.symm i))
      (hai.comp E.symm.injective) hb
    rw [Equiv.sum_comp E.symm (fun i => (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2)] at H
    exact H
  calc
    _ ≤ ∑ k : ι, ∑ i : {i : Fin n // g i = k},
        (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 :=
      Finset.sum_le_sum (fun k _ => hlocal k)
    _ = ∑ i : Fin n, (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 := by
      simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv_apply] using
        (Equiv.sum_comp (Equiv.sigmaFiberEquiv g)
          (fun i => (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2))

lemma GroupFermionicCoefficients.spectral_lower {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {g : Fin n → ι} {f : (Fin n → SpinMode) → ℂ}
    (hf : GroupFermionicCoefficients g f) {b : ℝ} (hb : 0 < b)
    (hs : Summable (fun a => ‖f a‖^2))
    (he : Summable (fun a => cubeSpectralWeight b a * ‖f a‖^2)) :
    groupNeumannLower g b * (∑' a, ‖f a‖^2) ≤
      ∑' a, cubeSpectralWeight b a * ‖f a‖^2 := by
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (hs.mul_left _) he
  intro a
  by_cases hz : f a = 0
  · simp [hz]
  have hai : Function.Injective (fun i => (g i,a i)) := by
    intro i j hij
    by_contra hne
    exact hz (hf.vanish_of_repeat hne (congrArg Prod.fst hij) (congrArg Prod.snd hij))
  exact mul_le_mul_of_nonneg_right (grouped_neumann_spectral_lower g a hai hb) (sq_nonneg _)

def GroupAntisymmetric {n : ℕ} (ψ : H1Vector n) {ι : Type*} (g : Fin n → ι) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)), g ∘ p = g → ∀ (s : Spins n),
    ∀ᵐ x ∂volume,
      ψ.value (s ∘ p) (permute p x) = ((p.sign : ℤ) : ℂ) * ψ.value s x

lemma cubeFermionCoefficient_group_antisymmetric {n : ℕ} {ψ : H1Vector n}
    {ι : Type*} {g : Fin n → ι}
    (hψ : GroupAntisymmetric ψ g) (b : ℝ) :
    GroupFermionicCoefficients g (cubeFermionCoefficient ψ b) := by
  intro p hgp a
  let e := Equiv.prodCongr p.symm (Equiv.refl (Fin 3))
  have hlabel : (cubeLabelEquiv n (a ∘ p)).2 = (cubeLabelEquiv n a).2 ∘ e.symm := rfl
  have hspin : (cubeLabelEquiv n (a ∘ p)).1 = (cubeLabelEquiv n a).1 ∘ p := rfl
  have hpos (x : (Fin n × Fin 3) → ℝ) :
      WithLp.toLp 2 (reindexCube e x) = permute p (WithLp.toLp 2 x) := by
    ext ij
    simp only [reindexCube_apply, e, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Equiv.symm_symm, Equiv.refl_symm]
    rfl
  unfold cubeFermionCoefficient
  rw [← (reindexCube_measurePreserving b e).integral_comp'
    (fun x => star (finiteCubeMode b (cubeLabelEquiv n (a ∘ p)).2 x) *
      ψ.value (cubeLabelEquiv n (a ∘ p)).1 (WithLp.toLp 2 x))]
  simp_rw [hlabel, finiteCubeMode_reindex, hspin, hpos]
  rw [← integral_const_mul]
  apply integral_congr_ae
  have ha := (PiLp.volume_preserving_toLp (Fin n × Fin 3)).quasiMeasurePreserving.ae
    (hψ p hgp (cubeLabelEquiv n a).1)
  filter_upwards [ha.filter_mono (ae_mono (finiteCubeMeasure_le_volume b))] with x hx
  rw [hx]
  ring

lemma translate_group_antisymmetric {n : ℕ} {ψ : H1Vector n}
    (hψ : Antisymmetric ψ) {ι : Type*} (g : Fin n → ι) (center : ι → Space) :
    GroupAntisymmetric (ψ.translate (WithLp.toLp 2 (fun ij => center (g ij.1) ij.2))) g := by
  intro p hgp s
  let c : Configuration n := WithLp.toLp 2 (fun ij => center (g ij.1) ij.2)
  have hpc : permute p c = c := by
    ext ij
    change center (g (p ij.1)) ij.2 = center (g ij.1) ij.2
    exact congrArg (fun k => center k ij.2) (congrFun hgp ij.1)
  have ha := (measurePreserving_add_right (volume : Measure (Configuration n)) c).quasiMeasurePreserving.ae
    (hψ p s)
  filter_upwards [ha] with x hx
  simpa only [H1Vector.translate, permute_add, hpc] using hx

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Rotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

noncomputable def rotationIsometry (Q : Rotation) : Space ≃ₗᵢ[ℝ] Space :=
  Unitary.linearIsometryEquiv ⟨Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) Q.1, by
    constructor
    · have H := congrArg (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)) Q.prop.1.1
      simpa only [map_mul, map_star, map_one] using H
    · have H := congrArg (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)) Q.prop.1.2
      simpa only [map_mul, map_star, map_one] using H⟩

lemma rotationIsometry_apply (Q : Rotation) (x : Space) (j : Fin 3) :
    rotationIsometry Q x j = ∑ k, Q.1 j k*x k := rfl

lemma rotation_action_continuous : Continuous (fun p : Rotation × Space => rotationIsometry p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  change Continuous (fun p : Rotation × Space => ∑ k, p.1.1 j k * p.2 k)
  apply continuous_finsetSum
  intro k _
  have hQ : Continuous (fun p : Rotation × Space => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : Rotation × Space => p.2 k) :=
    (PiLp.continuous_apply 2 _ k).comp continuous_snd
  exact ((continuous_apply k).comp ((continuous_apply j).comp hQ)).mul hx

lemma flatFineKernel_eq_zero {b : ℝ} (hb : 0 < b) (x : Space)
    (hx : 3*b^2 < ‖x‖^2) : flatFineKernel b x.ofLp = 0 := by
  have hj : ∃ j : Fin 3, b ≤ |x j| := by
    by_contra! H
    have Hs : ‖x‖^2 ≤ 3*b^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        _ ≤ ∑ _ : Fin 3, b^2 := Finset.sum_le_sum (fun j _ =>
          (sq_abs _).symm.trans_le ((sq_le_sq₀ (abs_nonneg _) hb.le).mpr (H j).le))
        _ = _ := by simp
    linarith
  obtain ⟨j,hj⟩ := hj
  unfold flatFineKernel
  rw [Finset.prod_eq_zero (Finset.mem_univ j)]
  · ring
  · exact max_eq_left (by dsimp; linarith)

noncomputable def fineKernel (b : ℝ) (x : Space) : ℝ :=
  ∫ Q : Rotation, flatFineKernel b (rotationIsometry Q x).ofLp ∂rotationMeasure

lemma rotated_flatKernel_continuous (b : ℝ) :
    Continuous (fun p : Rotation × Space => flatFineKernel b (rotationIsometry p.1 p.2).ofLp) :=
  (flatFineKernel_continuous b).comp ((PiLp.continuous_ofLp 2 _).comp rotation_action_continuous)

lemma rotated_flatKernel_integrable (b : ℝ) (x : Space) :
    Integrable (fun Q : Rotation => flatFineKernel b (rotationIsometry Q x).ofLp) rotationMeasure :=
  ((rotated_flatKernel_continuous b).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma fineKernel_nonneg (b : ℝ) (x : Space) : 0 ≤ fineKernel b x :=
  integral_nonneg (fun _ => flatFineKernel_nonneg _ _)

lemma fineKernel_le {b : ℝ} (hb : 0 < b) (x : Space) : fineKernel b x ≤ (b⁻¹)^3 := by
  calc
    _ ≤ ∫ _ : Rotation, (b⁻¹)^3 ∂rotationMeasure :=
      integral_mono (rotated_flatKernel_integrable b x) (integrable_const _)
        (fun _ => flatFineKernel_le hb _)
    _ = _ := by simp

lemma fineKernel_eq_zero {b : ℝ} (hb : 0 < b) (x : Space)
    (hx : 3*b^2 < ‖x‖^2) : fineKernel b x = 0 := by
  unfold fineKernel
  calc
    _ = ∫ _ : Rotation, (0 : ℝ) ∂rotationMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun Q => flatFineKernel_eq_zero hb _ (by simpa using hx))
    _ = 0 := integral_zero _ _

lemma rotationIsometry_mul (P Q : Rotation) (x : Space) :
    rotationIsometry (P*Q) x = rotationIsometry P (rotationIsometry Q x) := by
  ext j
  simp only [rotationIsometry_apply]
  change (∑ k, (P.val * Q.val) j k * x k) = ∑ k, P.val j k * (∑ l, Q.val k l * x l)
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma fineKernel_rotation (b : ℝ) (P : Rotation) (x : Space) :
    fineKernel b (rotationIsometry P x) = fineKernel b x := by
  unfold fineKernel
  simp_rw [← rotationIsometry_mul]
  exact integral_mul_right_eq_self (μ := rotationMeasure) (fun Q : Rotation => flatFineKernel b (rotationIsometry Q x).ofLp) P

lemma flatFineKernel_space_integrable (b : ℝ) :
    Integrable (fun x : Space => flatFineKernel b x.ofLp) :=
  (PiLp.volume_preserving_ofLp (Fin 3)).integrable_comp_of_integrable (flatFineKernel_integrable b)

lemma flatFineKernel_space_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : Space, flatFineKernel b x.ofLp) = 1 := by
  exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp' (flatFineKernel b)).trans
    (flatFineKernel_integral hb)

lemma rotated_flatKernel_space_integrable (b : ℝ) (Q : Rotation) :
    Integrable (fun x : Space => flatFineKernel b (rotationIsometry Q x).ofLp) :=
  (rotationIsometry Q).measurePreserving.integrable_comp_of_integrable (flatFineKernel_space_integrable b)

lemma rotated_flatKernel_space_integral {b : ℝ} (hb : 0 < b) (Q : Rotation) :
    (∫ x : Space, flatFineKernel b (rotationIsometry Q x).ofLp) = 1 := by
  exact ((show MeasurePreserving (rotationIsometry Q).toHomeomorph.toMeasurableEquiv volume volume from
    (rotationIsometry Q).measurePreserving).integral_comp' (fun x : Space => flatFineKernel b x.ofLp)).trans
    (flatFineKernel_space_integral hb)

lemma rotated_flatKernel_integrable_prod {b : ℝ} (hb : 0 < b) :
    Integrable (fun p : Rotation × Space => flatFineKernel b (rotationIsometry p.1 p.2).ofLp)
      (rotationMeasure.prod volume) := by
  apply (integrable_prod_iff (rotated_flatKernel_continuous b).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun Q => rotated_flatKernel_space_integrable b Q)
  · simp_rw [Real.norm_of_nonneg (flatFineKernel_nonneg ..)]
    simp_rw [rotated_flatKernel_space_integral hb]
    exact integrable_const _

lemma fineKernel_integrable {b : ℝ} (hb : 0 < b) : Integrable (fineKernel b) :=
  (rotated_flatKernel_integrable_prod hb).integral_prod_right

lemma fineKernel_integral {b : ℝ} (hb : 0 < b) : (∫ x, fineKernel b x) = 1 := by
  unfold fineKernel
  rw [← integral_integral_swap (rotated_flatKernel_integrable_prod hb)]
  simp_rw [rotated_flatKernel_space_integral hb]
  simp

noncomputable def fineDensity {n : ℕ} (b : ℝ) (x : Fin n → Space) (y : Space) : ℝ :=
  ∑ i, fineKernel b (y-x i)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoulombBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
namespace Coulomb
lemma fineKernel_continuous (b : ℝ) : Continuous (fineKernel b) := by
  have hs : Continuous (fun p : Space × Rotation => (p.2,p.1)) :=
    continuous_snd.prodMk continuous_fst
  have hc := (rotated_flatKernel_continuous b).comp hs
  dsimp only [Function.comp_def] at hc
  have H := continuous_parametric_integral_of_continuous
    (μ := rotationMeasure) (f := fun x : Space => fun Q : Rotation => flatFineKernel b (rotationIsometry Q x).ofLp)
    hc
    (s := univ) isCompact_univ
  change Continuous (fun x : Space => ∫ Q : Rotation, flatFineKernel b (rotationIsometry Q x).ofLp ∂rotationMeasure)
  simpa only [Measure.restrict_univ] using H

lemma fineKernel_neg (b : ℝ) (x : Space) : fineKernel b (-x) = fineKernel b x := by
  unfold fineKernel
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun Q => by
    dsimp only
    rw [map_neg]
    exact flatFineKernel_neg b _)

lemma fineKernel_isometry (b : ℝ) (E : Space ≃ₗᵢ[ℝ] Space) (x : Space) :
    fineKernel b (E x) = fineKernel b x := by
  let U := Unitary.linearIsometryEquiv.symm E
  let T := Matrix.toEuclideanCLM (n:=Fin 3) (𝕜:=ℝ)
  let A : Matrix (Fin 3) (Fin 3) ℝ := T.symm U.val
  have hAE : T A = (E : Space →L[ℝ] Space) := by
    simp [A, U, Unitary.coe_symm_linearIsometryEquiv_apply]
  have hA : A ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
    constructor
    · apply T.injective
      change T (star A*A) = T 1
      dsimp only [A]
      simpa only [map_mul, map_star, map_one, T.apply_symm_apply] using U.prop.1
    · apply T.injective
      change T (A*star A) = T 1
      dsimp only [A]
      simpa only [map_mul, map_star, map_one, T.apply_symm_apply] using U.prop.2
  have hdet : A.det = 1 ∨ A.det = -1 := by
    have H := (Matrix.det_of_mem_unitary hA).1
    simp only [star_trivial] at H
    rcases mul_self_eq_one_iff.mp H with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hdet with hdet | hdet
  · let Q : Rotation := ⟨A,hA,hdet⟩
    have hQ : rotationIsometry Q x = E x := by
      change T A x = E x
      rw [hAE]
      rfl
    rw [← hQ]
    exact fineKernel_rotation b Q x
  · have hnA : -A ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
      constructor
      · simpa only [star_neg, neg_mul_neg] using hA.1
      · simpa only [star_neg, neg_mul_neg] using hA.2
    have hnD : (-A).det = 1 := by norm_num [Matrix.det_neg, hdet]
    let Q : Rotation := ⟨-A,hnA,hnD⟩
    have hQ : rotationIsometry Q x = -(E x) := by
      change T (-A) x = -(E x)
      rw [map_neg, hAE]
      rfl
    rw [← fineKernel_neg b (E x), ← hQ]
    exact fineKernel_rotation b Q x

lemma fineKernel_radial (b : ℝ) {x y : Space} (h : ‖x‖ = ‖y‖) :
    fineKernel b x = fineKernel b y := by
  let E := (ℝ ∙ (x-y))ᗮ.reflection
  have hE : E x = y := Submodule.reflection_sub h
  rw [← hE, fineKernel_isometry]

lemma fineKernel_profile (b : ℝ) (x : Space) :
    fineKernel b x = fineKernel b (EuclideanSpace.single 0 ‖x‖) := by
  apply fineKernel_radial
  simp

lemma fineKernel_coulomb_integrable {b : ℝ} (hb : 0 < b) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*fineKernel b y) :=
  coulomb_convolution_integrable (fineKernel_integrable hb) (fineKernel_continuous b).measurable
    (fineKernel_nonneg b) (fineKernel_le hb) (by norm_num : (0:ℝ) < 1) x

lemma fineKernel_coulomb_le {b : ℝ} (hb : 0 < b) {x : Space} (hx : x ≠ 0) :
    (∫ y, coulombKernel (x-y)*fineKernel b y) ≤ coulombKernel x := by
  simpa only [fineKernel_integral hb, mul_one] using
    radial_coulomb_integral_le (fineKernel_integrable hb) (fineKernel_continuous b).measurable
      (fineKernel_nonneg b) (fineKernel_le hb) (fineKernel_profile b) hx

lemma fineKernel_coulomb_eq {b : ℝ} (hb : 0 < b) {x : Space}
    (hx : Real.sqrt 3*b ≤ ‖x‖) :
    (∫ y, coulombKernel (x-y)*fineKernel b y) = coulombKernel x := by
  have hR : 0 < Real.sqrt 3*b := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hb
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
  have hfs (y : Space) (hy : Real.sqrt 3*b < ‖y‖) : fineKernel b y = 0 := by
    apply fineKernel_eq_zero hb
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), sq_nonneg (‖y‖-Real.sqrt 3*b)]
  simpa only [fineKernel_integral hb, mul_one] using
    radial_coulomb_integral_eq (fineKernel_integrable hb) (fineKernel_continuous b).measurable
      (fineKernel_nonneg b) (fineKernel_le hb) (fineKernel_profile b) hR.le hfs hx0 hx

lemma fineKernel_shift_integrable {b : ℝ} (hb : 0 < b) (a : Space) :
    Integrable (fun y => fineKernel b (y-a)) := (fineKernel_integrable hb).comp_sub_right a

lemma fineKernel_shift_integral {b : ℝ} (hb : 0 < b) (a : Space) :
    (∫ y, fineKernel b (y-a)) = 1 := by
  rw [integral_sub_right_eq_self, fineKernel_integral hb]

lemma fineKernel_shift_coulomb_integral {b : ℝ} (a x : Space) :
    (∫ y, coulombKernel (x-y)*fineKernel b (y-a)) =
      ∫ y, coulombKernel ((x-a)-y)*fineKernel b y := by
  rw [← integral_sub_right_eq_self (fun y => coulombKernel ((x-a)-y)*fineKernel b y) a]
  congr 1
  funext y
  congr 2
  abel

lemma fineKernel_coulomb_bound {b : ℝ} (hb : 0 < b) (x : Space) :
    (∫ y, coulombKernel (x-y)*fineKernel b y) ≤ (2*Real.pi+1)/b := by
  have H := coulomb_convolution_bound (fineKernel_integrable hb) (fineKernel_continuous b).measurable
    (fineKernel_nonneg b) (fineKernel_le hb) hb x
  rw [fineKernel_integral hb] at H
  convert H using 1; field_simp

lemma fineKernel_pair_le {b : ℝ} (hb : 0 < b) {a c : Space} (hac : a ≠ c) :
    coulombBilinear (fun x => fineKernel b (x-a)) (fun x => fineKernel b (x-c)) ≤
      coulombKernel (a-c) := by
  have hi := fineKernel_shift_integrable hb
  have hm (v : Space) : Measurable (fun x => fineKernel b (x-v)) :=
    (fineKernel_continuous b).measurable.comp (by fun_prop)
  have hbnd (v x : Space) : ‖fineKernel b (x-v)‖ ≤ (b⁻¹)^3 := by
    rw [Real.norm_of_nonneg (fineKernel_nonneg b _)]
    exact fineKernel_le hb _
  rw [coulombBilinear_iterated (hi a) (hm a) (hi c) (hm c) (hbnd c)]
  simp_rw [fineKernel_shift_coulomb_integral]
  have hp := (coulomb_pair_integrable (hi a) (hm a) (hi c) (hm c) (hbnd c)).integral_prod_left
  have hip : Integrable (fun x => fineKernel b (x-a)*
      (∫ y, coulombKernel ((x-c)-y)*fineKernel b y)) := by
    apply hp.congr
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [← fineKernel_shift_coulomb_integral c x, ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring))
  have hik : Integrable (fun x => fineKernel b (x-a)*coulombKernel (x-c)) := by
    have h := coulomb_convolution_integrable (hi a) (hm a)
      (fun y => fineKernel_nonneg b (y-a)) (fun y => fineKernel_le hb (y-a))
      hb c
    apply h.congr
    exact Filter.Eventually.of_forall (fun x => by dsimp only; unfold coulombKernel; rw [norm_sub_rev]; ring)
  calc
    _ ≤ ∫ x, fineKernel b (x-a)*coulombKernel (x-c) := by
      apply integral_mono_ae hip hik
      have hc : ∀ᵐ x : Space, x ≠ c := by rw [ae_iff]; simp
      filter_upwards [hc] with x hx
      exact mul_le_mul_of_nonneg_left (fineKernel_coulomb_le hb (sub_ne_zero.mpr hx)) (fineKernel_nonneg b _)
    _ = ∫ x, coulombKernel ((c-a)-x)*fineKernel b x := by
      rw [← fineKernel_shift_coulomb_integral]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; unfold coulombKernel; rw [norm_sub_rev]; ring)
    _ ≤ coulombKernel (c-a) := fineKernel_coulomb_le hb (sub_ne_zero.mpr hac.symm)
    _ = _ := by unfold coulombKernel; rw [norm_sub_rev]

lemma fineKernel_pair_self_le {b : ℝ} (hb : 0 < b) (a : Space) :
    coulombBilinear (fun x => fineKernel b (x-a)) (fun x => fineKernel b (x-a)) ≤
      (2*Real.pi+1)/b := by
  have hi := fineKernel_shift_integrable hb a
  have hm : Measurable (fun x => fineKernel b (x-a)) :=
    (fineKernel_continuous b).measurable.comp (by fun_prop)
  have hbnd (x : Space) : ‖fineKernel b (x-a)‖ ≤ (b⁻¹)^3 := by
    rw [Real.norm_of_nonneg (fineKernel_nonneg b _)]
    exact fineKernel_le hb _
  rw [coulombBilinear_iterated hi hm hi hm hbnd]
  have hp := (coulomb_pair_integrable hi hm hi hm hbnd).integral_prod_left
  have hip : Integrable (fun x => fineKernel b (x-a)*
      (∫ y, coulombKernel (x-y)*fineKernel b (y-a))) := by
    apply hp.congr
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring))
  calc
    _ ≤ ∫ x, fineKernel b (x-a)*((2*Real.pi+1)/b) := by
      apply integral_mono hip (hi.mul_const _)
      intro x
      dsimp only
      rw [fineKernel_shift_coulomb_integral]
      exact mul_le_mul_of_nonneg_left (fineKernel_coulomb_bound hb _) (fineKernel_nonneg b _)
    _ = (2*Real.pi+1)/b := by rw [integral_mul_const, fineKernel_shift_integral hb, one_mul]

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RetainedFineDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def retainedFineDensity {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) (y : Space) : ℝ := ∑ i ∈ r, fineKernel b (y-x i)

lemma retainedFineDensity_coulomb_expansion {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) :
    coulombBilinear (retainedFineDensity b r x) (retainedFineDensity b r x) =
      ∑ i ∈ r, ∑ j ∈ r, coulombBilinear (fun y => fineKernel b (y-x i))
        (fun y => fineKernel b (y-x j)) := by
  have hi (i j : Fin n) : Integrable (fun p : Space × Space =>
      fineKernel b (p.1-x i)*fineKernel b (p.2-x j)*coulombKernel (p.1-p.2)) :=
    coulomb_pair_integrable (fineKernel_shift_integrable hb _) ((fineKernel_continuous b).measurable.comp (by fun_prop))
      (fineKernel_shift_integrable hb _) ((fineKernel_continuous b).measurable.comp (by fun_prop))
      (fun y => by rw [Real.norm_of_nonneg (fineKernel_nonneg ..)]; exact fineKernel_le hb _)
  unfold coulombBilinear retainedFineDensity
  simp_rw [Finset.sum_mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  congr 1
  ext i
  exact integral_finsetSum _ (fun j _ => hi i j)

lemma coulombKernel_sub_symm (x y : Space) : coulombKernel (x-y) = coulombKernel (y-x) := by
  unfold coulombKernel
  rw [norm_sub_rev]

theorem retained_fine_pair_lower {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) (hx : Function.Injective x) :
    coulombBilinear (retainedFineDensity b r x) (retainedFineDensity b r x)/2 -
      ((2*Real.pi+1)/(2*b)) * r.card ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then coulombKernel (x i-x j) else 0 := by
  have hdiag : (∑ i ∈ r, ∑ j ∈ r,
      coulombBilinear (fun y => fineKernel b (y-x i)) (fun y => fineKernel b (y-x j))) ≤
      ∑ i ∈ r, ∑ j ∈ r, if i = j then (2*Real.pi+1)/b else coulombKernel (x i-x j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with h
    · subst j; exact fineKernel_pair_self_le hb _
    · exact fineKernel_pair_le hb (hx.ne h)
  have hs (i : Fin n) : (∑ j ∈ r, if i = j then (2*Real.pi+1)/b else coulombKernel (x i-x j)) =
      (if i ∈ r then (2*Real.pi+1)/b else 0) + ∑ j ∈ r, coulombKernel (x i-x j) := by
    have hterm (j : Fin n) : (if i = j then (2*Real.pi+1)/b else coulombKernel (x i-x j)) =
        (if i = j then (2*Real.pi+1)/b else 0) + coulombKernel (x i-x j) := by
      by_cases h : i = j
      · subst j; simp [coulombKernel]
      · simp [h]
    simp_rw [hterm, Finset.sum_add_distrib]
    simp
  have hall : (∑ i ∈ r, ∑ j ∈ r, coulombKernel (x i-x j)) ≤
      ∑ i : Fin n, ∑ j : Fin n, coulombKernel (x i-x j) := by
    apply (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ r) (fun _ _ _ => coulombKernel_nonneg _))).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ r)
      (fun _ _ _ => Finset.sum_nonneg (fun _ _ => coulombKernel_nonneg _))
  have hsplit : (∑ i : Fin n, ∑ j : Fin n, coulombKernel (x i-x j)) =
      2 * (∑ i : Fin n, ∑ j : Fin n, if i < j then coulombKernel (x i-x j) else 0) := by
    have h (i j : Fin n) : coulombKernel (x i-x j) =
        (if i < j then coulombKernel (x i-x j) else 0) +
        (if j < i then coulombKernel (x j-x i) else 0) := by
      rcases lt_trichotomy i j with h | h | h
      · simp [h, not_lt.mpr h.le]
      · subst j; simp [coulombKernel]
      · simp only [h, not_lt.mpr h.le, ite_false, ite_true, zero_add]
        exact coulombKernel_sub_symm _ _
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, ((if i < j then coulombKernel (x i-x j) else 0) +
          (if j < i then coulombKernel (x j-x i) else 0)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then coulombKernel (x j-x i) else 0)]
        ring
  simp_rw [hs] at hdiag
  simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul] at hdiag
  rw [hsplit] at hall
  rw [retainedFineDensity_coulomb_expansion hb]
  have he : ((2*Real.pi+1)/(2*b))*r.card*2 = r.card*((2*Real.pi+1)/b) := by ring
  linarith

lemma ae_position_injective (n : ℕ) : ∀ᵐ x : Configuration n, Function.Injective (position x) := by
  have hpair (i j : Fin n) (hij : i ≠ j) : ∀ᵐ x : Configuration n, position x i ≠ position x j := by
    let L : Configuration n →ₗ[ℝ] ℝ :=
      { toFun := fun x => x (i,0)-x (j,0)
        map_add' := by intro x y; simp only [PiLp.add_apply]; ring
        map_smul' := by intro c x; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    have hL : LinearMap.ker L ≠ ⊤ := by
      intro h
      have hx : EuclideanSpace.single (i,0) (1:ℝ) ∈ LinearMap.ker L := by rw [h]; trivial
      simp [LinearMap.mem_ker, L, hij] at hx
    have hm := Measure.addHaar_submodule (volume : Measure (Configuration n)) (LinearMap.ker L) hL
    have hnull : (volume : Measure (Configuration n)) {x | position x i = position x j} = 0 := by
      apply measure_mono_null _ hm
      intro x hx
      change x (i,0)-x (j,0) = 0
      exact sub_eq_zero.mpr (congrArg (fun z : Space => z 0) hx)
    rw [ae_iff]
    simpa only [not_not] using hnull
  simp only [Function.Injective, ae_all_iff]
  intro i j
  by_cases h : i = j
  · exact Eventually.of_forall fun _ _ => h
  · exact (hpair i j h).mono fun _ hx he => (hx he).elim

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Add
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma H1Vector.test_integrable {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    Integrable (fun x => ψ.value s x * (φ x : ℂ)) := by
  have hL : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hc.comp_left (by simp))
  exact (ψ.value_L2 s).integrable_mul hL

noncomputable def H1Vector.add {n : ℕ} (ψ φ : H1Vector n) : H1Vector n where
  value s x := ψ.value s x + φ.value s x
  gradient s a x := ψ.gradient s a x + φ.gradient s a x
  value_L2 s := (ψ.value_L2 s).add (φ.value_L2 s)
  partial_L2 s a := (ψ.partial_L2 s a).add (φ.partial_L2 s a)
  weak_partial s a f hf hc := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (EuclideanSpace.single a 1)) :=
      (hf.fderiv_right (by simp)).clm_apply contDiff_const
    have hdc := hc.fderiv_apply ℝ (EuclideanSpace.single a 1)
    have hiψ := ψ.test_integrable s _ hd hdc
    have hiφ := φ.test_integrable s _ hd hdc
    have hL : MemLp (fun x => (f x : ℂ)) 2 volume :=
      (Complex.continuous_ofReal.comp hf.continuous).memLp_of_hasCompactSupport
        (hc.comp_left (by simp))
    have hjψ := (ψ.partial_L2 s a).integrable_mul hL
    have hjφ := (φ.partial_L2 s a).integrable_mul hL
    change Integrable (fun x => ψ.gradient s a x * (f x : ℂ)) at hjψ
    change Integrable (fun x => φ.gradient s a x * (f x : ℂ)) at hjφ
    simp_rw [add_mul]
    rw [integral_add hiψ hiφ, integral_add hjψ hjφ,
      ψ.weak_partial s a f hf hc, φ.weak_partial s a f hf hc]
    ring

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoreCoulombPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb

lemma coreCoulombPotential_bound {m : ℕ} (u : H1Vector m) (z : Space) :
    coreCoulombPotential u z ≤ ∑ s : Spins m, ∑ i : Fin m,
      (4*(∑ b : Fin 3, ∫ x, ‖u.gradient s (i,b) x‖^2)+(1/4:ℝ)*(∫ x, ‖u.value s x‖^2)) := by
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_one] using
    (u.nuclear_coulomb_integrable_bound s i z (by norm_num : (0:ℝ)<1)).2

end Coulomb

open scoped Classical

open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FrameOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
namespace Coulomb
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]
lemma id_sub_frameOperator_positive {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ)
    (hb : ∀ u, (∫ x,‖inner ℂ (v x) u‖^2 ∂μ) ≤ ‖u‖^2) :
    (ContinuousLinearMap.id ℂ E - frameOperator μ v).toLinearMap.IsPositive := by
  have hid : (LinearMap.id : E →ₗ[ℂ] E).IsSymmetric := fun _ _ => rfl
  refine ⟨hid.sub (frameOperator_symmetric hv),fun u => ?_⟩
  change 0 ≤ RCLike.re (inner ℂ (u-frameOperator μ v u) u)
  rw [inner_sub_left,map_sub,inner_self_eq_norm_sq_to_K]
  change 0 ≤ ((‖u‖ : ℂ)^2).re - (inner ℂ (frameOperator μ v u) u).re
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  change 0 ≤ ‖u‖^2 - RCLike.re (inner ℂ (frameOperator μ v u) u)
  rw [inner_re_symm]
  apply sub_nonneg.mpr
  change (inner ℂ u (frameOperator μ v u)).re ≤ ‖u‖^2
  rw [frameOperator_quadratic hv]
  exact hb u
end Coulomb

open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_EigenspaceBasisSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
lemma compactSpectralBasis_eigen_le_one (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.toLinearMap.IsPositive)
    (hI : (ContinuousLinearMap.id ℂ E-T).toLinearMap.IsPositive)
    (i : Σ z, eigenspaceBasisSet T z) : i.1.re ≤ 1 := by
  have h := hI.re_inner_nonneg_right (compactSpectralBasis T hc hT.1 i)
  change 0 ≤ RCLike.re (inner ℂ _ (_-T _)) at h
  rw [inner_sub_right,map_sub] at h
  simpa [compactSpectralBasis_eigen,inner_smul_right,inner_self_eq_norm_sq_to_K,
    (compactSpectralBasis T hc hT.1).orthonormal.1 i,sub_nonneg] using h
end Coulomb

open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketWindowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
lemma packetAnalysis_momentum (g h : 𝓢(Space,ℂ)) (y : Space) :
    (∫ p : Space,‖packetAnalysis g h y p‖^2) =
      ∫ x : Space, ‖g (x-y)‖^2*‖h x‖^2 := by
  simp only [packetAnalysis]
  rw [SchwartzMap.integral_norm_sq_fourier]
  simp [packetWindowed_apply,mul_pow]
lemma packetAnalysis_momentum_integrable (g h : 𝓢(Space,ℂ)) (y : Space) :
    Integrable (fun p : Space => ‖packetAnalysis g h y p‖^2) :=
  (𝓕 (packetWindowed g h y)).memLp 2 volume |>.integrable_norm_pow (by norm_num)
lemma packetWindowed_joint_integrable (g h : 𝓢(Space,ℂ)) :
    Integrable (fun yx : Space × Space => ‖g (yx.2-yx.1)‖^2*‖h yx.2‖^2)
      (volume.prod volume) := by
  have hg : Integrable (fun x : Space => ‖g x‖^2) :=
    (g.memLp 2 volume).integrable_norm_pow (by norm_num)
  have hh : Integrable (fun x : Space => ‖h x‖^2) :=
    (h.memLp 2 volume).integrable_norm_pow (by norm_num)
  have hm : Continuous (fun yx : Space × Space => ‖g (yx.2-yx.1)‖^2*‖h yx.2‖^2) :=
    ((g.continuous.comp (continuous_snd.sub continuous_fst)).norm.pow 2).mul
      ((h.continuous.comp continuous_snd).norm.pow 2)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => (hg.comp_sub_left x).mul_const (‖h x‖^2)),?_⟩
  change Integrable (fun x : Space => ∫ y : Space, ‖‖g (x-y)‖^2*‖h x‖^2‖)
  have hs (x : Space) : (∫ y : Space,‖g (x-y)‖^2) = ∫ y : Space,‖g y‖^2 :=
    integral_sub_left_eq_self (fun y : Space => ‖g y‖^2) volume x
  simp only [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),integral_mul_const,hs]
  exact hh.const_mul _
lemma packetWindowed_joint_integral (g h : 𝓢(Space,ℂ)) :
    (∫ yx : Space × Space, ‖g (yx.2-yx.1)‖^2*‖h yx.2‖^2 ∂volume.prod volume) =
      (∫ x : Space,‖g x‖^2)*(∫ x : Space,‖h x‖^2) := by
  rw [integral_prod_symm _ (packetWindowed_joint_integrable g h)]
  have hs (x : Space) : (∫ y : Space,‖g (x-y)‖^2) = ∫ y : Space,‖g y‖^2 :=
    integral_sub_left_eq_self (fun y : Space => ‖g y‖^2) volume x
  simp only [integral_mul_const,hs,integral_const_mul]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PhaseRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
namespace Coulomb

lemma phaseMeasure_le (R : Space → ℝ) : phaseMeasure R ≤ volume.prod volume :=
  Measure.restrict_le_self

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DensityCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
namespace Coulomb

def densityCut (ρ : Space → ℝ) (k : ℕ) (x : Space) : ℝ := min (ρ x) (k:ℝ)
lemma densityCut_nonneg (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (k : ℕ) (x : Space) :
    0 ≤ densityCut ρ k x := le_min (hp x) (Nat.cast_nonneg k)
lemma densityCut_le (ρ : Space → ℝ) (k : ℕ) (x : Space) : densityCut ρ k x ≤ ρ x := min_le_left _ _
lemma densityCut_bound (ρ : Space → ℝ) (k : ℕ) (x : Space) : densityCut ρ k x ≤ (k:ℝ) := min_le_right _ _
lemma densityCut_measurable (ρ : Space → ℝ) (hm : Measurable ρ) (k : ℕ) :
    Measurable (densityCut ρ k) := hm.min measurable_const
lemma densityCut_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) (k : ℕ) : Integrable (densityCut ρ k) := by
  apply hi.mono' (densityCut_measurable ρ hm k).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (densityCut_nonneg ρ hp k x)]
  exact densityCut_le ρ k x
lemma densityCut_kinetic_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (ht : Integrable (fun x => ρ x^(5/3:ℝ))) (k : ℕ) :
    Integrable (fun x => densityCut ρ k x^(5/3:ℝ)) := by
  apply ht.mono' ((densityCut_measurable ρ hm k).pow_const _).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (densityCut_nonneg ρ hp k x) _)]
  exact Real.rpow_le_rpow (densityCut_nonneg ρ hp k x) (densityCut_le ρ k x) (by norm_num)
lemma densityCut_support (ρ : Space → ℝ) (K : Set Space)
    (hs : ∀ x, x ∉ K → ρ x = 0) (k : ℕ) (x : Space) (hx : x ∉ K) : densityCut ρ k x = 0 := by
  simp only [densityCut,hs x hx,min_eq_left (Nat.cast_nonneg k)]
lemma densityCut_tendsto (ρ : Space → ℝ) (x : Space) :
    Tendsto (fun k => densityCut ρ k x) atTop (nhds (ρ x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (ρ x))] with k hk
  exact (min_eq_left hk).symm

end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
namespace Coulomb

def packetSynthesis (g : Space → ℂ) (f : Space × Space → ℂ) (x : Space) : ℂ :=
  ∫ yp : Space × Space, f yp * (Complex.exp ((2*Real.pi*inner ℝ x yp.2 : ℝ)*Complex.I) * g (x-yp.1))

lemma packetSynthesis_contDiff (g : Space → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (f : Space × Space → ℂ) (hf : LocallyIntegrable f volume)
    (P : ℝ) (hP : ∀ yp, f yp ≠ 0 → ‖yp.2‖ ≤ P) :
    ContDiff ℝ (⊤ : ℕ∞) (packetSynthesis g f) := by
  let χ : ContDiffBump (0 : Space) :=
    ⟨max 1 P, max 1 P+1, lt_of_lt_of_le (by norm_num) (le_max_left _ _), by linarith⟩
  let G : Space → Space × Space → ℂ := fun x z =>
    Complex.exp ((-2*Real.pi*inner ℝ z.2 x : ℝ)*Complex.I) * g z.1 * (χ z.2 : ℂ)
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space × (Space × Space) => G z.1 z.2) := by
    dsimp only [G]
    have hphase : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space × (Space × Space) =>
        ((-2*Real.pi*inner ℝ z.2.2 z.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_snd.snd.inner ℝ contDiff_fst))
    have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space × (Space × Space) => (χ z.2.2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp (contDiff_snd.snd))
    fun_prop
  have hs (x : Space) (z : Space × Space) (_ : x ∈ (univ : Set Space))
      (hz : z ∉ tsupport g ×ˢ tsupport χ) : G x z = 0 := by
    have hh : z.1 ∉ tsupport g ∨ z.2 ∉ tsupport χ := by simpa only [mem_prod, not_and_or] using hz
    rcases hh with hz | hz
    · simp [G, image_eq_zero_of_notMem_tsupport hz]
    · simp [G, image_eq_zero_of_notMem_tsupport hz]
  have hc := contDiffOn_convolution_right_with_param_comp
    (ContinuousLinearMap.mul ℝ ℂ) (s := (univ : Set Space))
    (v := fun x : Space => (x, (0 : Space))) (f := f) (g := G)
    (by fun_prop) isOpen_univ (hgc.isCompact.prod χ.hasCompactSupport.isCompact) hs hf hG.contDiffOn
  rw [contDiffOn_univ] at hc
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [packetSynthesis, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with yp
  by_cases hz : f yp = 0
  · simp [hz]
  · have hχ : χ (-yp.2) = 1 := χ.one_of_mem_closedBall (by
      simp only [mem_closedBall, dist_zero_right, norm_neg]
      exact (hP yp hz).trans (le_max_right _ _))
    simp only [G, Prod.fst_sub, Prod.snd_sub, zero_sub, hχ, Complex.ofReal_one, mul_one]
    congr 2
    congr 1
    rw [inner_neg_left, real_inner_comm]
    push_cast
    ring

lemma packetSynthesis_compactSupport (g : Space → ℂ) (hgc : HasCompactSupport g)
    (f : Space × Space → ℂ) (K : Set Space) (hK : IsCompact K)
    (hfK : ∀ yp, yp.1 ∉ K → f yp = 0) : HasCompactSupport (packetSynthesis g f) := by
  apply HasCompactSupport.intro (hK.add hgc.isCompact)
  intro x hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with yp
  by_cases hy : yp.1 ∈ K
  · have hz : x-yp.1 ∉ tsupport g := by
      intro hz
      exact hx ⟨yp.1, hy, x-yp.1, hz, by abel_nf⟩
    simp [image_eq_zero_of_notMem_tsupport hz]
  · simp [hfK yp hy]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketSynthesisIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
namespace Coulomb

open scoped Pointwise
lemma packetSynthesis_zero_of_notMem_region (g : Space → ℂ)
    (f : Space × Space → ℂ) (K : Set Space)
    (hfK : ∀ yp, yp.1 ∉ K → f yp = 0) (x : Space)
    (hx : x ∉ K + tsupport g) : packetSynthesis g f x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with yp
  by_cases hy : yp.1 ∈ K
  · have hz : x-yp.1 ∉ tsupport g := by
      intro hz
      exact hx ⟨yp.1, hy, x-yp.1, hz, by abel_nf⟩
    simp [image_eq_zero_of_notMem_tsupport hz]
  · simp [hfK yp hy]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
namespace Coulomb

lemma orthonormal_representative_inner {ι : Type*}
    (b : ι → Lp ℂ 2 (volume : Measure Space)) (hb : Orthonormal ℂ b)
    (F : ι → Space → ℂ) (he : ∀ i, (b i : Space → ℂ) =ᵐ[volume] F i) (i j : ι) :
    (∫ x : Space, star (F i x)*F j x) = if i = j then 1 else 0 := by
  classical
  have H : (∫ x : Space, star (F i x)*F j x) = inner ℂ (b i) (b j) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [he i,he j] with x hi hj
    simp only [RCLike.inner_apply',starRingEnd_apply,hi,hj]
  rw [H]
  exact orthonormal_iff_ite.mp hb i j

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SchwartzSquareIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma window_coulomb_le (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {x : Space} (hx : x ≠ 0) :
    (∫ y : Space, coulombKernel (x-y)*g y^2) ≤ coulombKernel x := by
  simpa only [hg,mul_one] using radial_coulomb_integral_le (schwartz_square_integrable g)
    (g.continuous.measurable.pow_const 2) (fun y => sq_nonneg (g y)) (schwartz_square_le g)
    (fun y => congrArg (fun t : ℝ => t^2) (hrad y)) hx

lemma window_shape_pair_le (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {a c : Space} (hac : a ≠ c) :
    (∫ xy : Space × Space, g (xy.1-a)^2*g (xy.2-c)^2*coulombKernel (xy.1-xy.2)) ≤
      coulombKernel (a-c) := by
  have hi := window_shift_integrable g
  have hm (v : Space) : Measurable (fun x => g (x-v)^2) :=
    (g.continuous.measurable.comp (measurable_id.sub measurable_const)).pow_const 2
  have hbnd (v x : Space) : ‖g (x-v)^2‖ ≤ (SchwartzMap.seminorm ℝ 0 0 g)^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact schwartz_square_le g _
  have hpair := coulomb_pair_integrable (hi a) (hm a) (hi c) (hm c) (hbnd c)
  change (∫ xy : Space × Space, g (xy.1-a)^2*g (xy.2-c)^2*coulombKernel (xy.1-xy.2) ∂volume.prod volume) ≤ _
  rw [integral_prod _ hpair]
  have hip : Integrable (fun x => g (x-a)^2*(∫ y, coulombKernel ((x-c)-y)*g y^2)) := by
    apply hpair.integral_prod_left.congr
    filter_upwards [] with x
    rw [← window_shift_coulomb_integral g c x,← integral_const_mul]
    congr 1
    funext y
    ring
  have hik : Integrable (fun x => g (x-a)^2*coulombKernel (x-c)) := by
    have H := coulomb_convolution_integrable (hi a) (hm a) (fun y => sq_nonneg (g (y-a)))
      (fun y => schwartz_square_le g (y-a)) (by norm_num : (0:ℝ)<1) c
    apply H.congr
    filter_upwards [] with x
    rw [coulombKernel_sub_comm c x]
    ring
  calc
    _ = ∫ x, g (x-a)^2*(∫ y, coulombKernel ((x-c)-y)*g y^2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← window_shift_coulomb_integral g c x,← integral_const_mul]
      congr 1
      funext y
      ring
    _ ≤ ∫ x, g (x-a)^2*coulombKernel (x-c) := by
      apply integral_mono_ae hip hik
      have hc : ∀ᵐ x : Space, x ≠ c := by rw [ae_iff]; simp
      filter_upwards [hc] with x hx
      exact mul_le_mul_of_nonneg_left (window_coulomb_le g hg hrad (sub_ne_zero.mpr hx)) (sq_nonneg _)
    _ = ∫ x, coulombKernel ((c-a)-x)*g x^2 := by
      rw [← window_shift_coulomb_integral]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [coulombKernel_sub_comm c x]
      ring
    _ ≤ coulombKernel (c-a) := window_coulomb_le g hg hrad (sub_ne_zero.mpr hac.symm)
    _ = _ := coulombKernel_sub_comm c a
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_SectorFormBottom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def sectorFormBottom {M : ℕ} (S : Nuclei M) (n : ℕ) : EReal :=
  sInf {e : EReal | ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧ e = (form S ψ : EReal)}

def unrestrictedFormBottom {M : ℕ} (S : Nuclei M) : EReal := ⨅ n, sectorFormBottom S n

lemma unrestrictedFormBottom_le_trial {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n)
    (ha : Antisymmetric ψ) (hm : mass ψ = 1) : unrestrictedFormBottom S ≤ (form S ψ : EReal) :=
  (iInf_le _ n).trans (sInf_le ⟨ψ,ha,hm,rfl⟩)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators
noncomputable section
namespace Coulomb

def atomicAttractionExcess {ι : Type*} (Z : ℕ) (X : ι → Space) (s : Finset ι) : ℝ :=
  (Z:ℝ) * (∑ i ∈ s, coulombKernel (X i)) -
    (1/2:ℝ) * (∑ i ∈ s, ∑ j ∈ s, coulombKernel (X i-X j))

end Coulomb
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_BodyCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma oneBody_derivative {n:ℕ} (f:Space → ℝ) (hf:ContDiff ℝ ∞ f)
    (i j:Fin n) (b:Fin 3) (x:Configuration n) :
    fderiv ℝ (fun y => f (position y i)) x (EuclideanSpace.single (j,b) 1)=
      if i=j then fderiv ℝ f (position x i) (EuclideanSpace.single b 1) else 0 := by
  have H:=(((hf.differentiable (by simp) (position x i)).hasFDerivAt).comp x
    (positionCLM i).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f (position y i)) x=_ at H
  rw [H]
  simp only [ContinuousLinearMap.comp_apply,positionCLM_single]
  split_ifs <;> simp_all
structure SmoothBoundedCoefficient where
  value:Space → ℝ
  smooth:ContDiff ℝ ∞ value
  bound:ℝ
  derivBound:ℝ
  bound_nonneg:0≤bound
  derivBound_nonneg:0≤derivBound
  value_le:∀ x,|value x|≤bound
  deriv_le:∀ a x,|fderiv ℝ value x (EuclideanSpace.single a 1)|≤derivBound
namespace SmoothBoundedCoefficient
lemma lift_smooth (f:SmoothBoundedCoefficient) {n:ℕ} (i:Fin n) :
    ContDiff ℝ ∞ (fun x:Configuration n => f.value (position x i)) :=
  f.smooth.comp (positionCLM i).contDiff
lemma lift_deriv_le (f:SmoothBoundedCoefficient) {n:ℕ} (i:Fin n) (a:Fin n × Fin 3) (x:Configuration n) :
    |fderiv ℝ (fun y => f.value (position y i)) x (EuclideanSpace.single a 1)|≤f.derivBound := by
  rw [oneBody_derivative f.value f.smooth i a.1 a.2 x]
  split_ifs
  · exact f.deriv_le _ _
  · simpa using f.derivBound_nonneg
end SmoothBoundedCoefficient

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CorePerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma integral_kinetic_coreSlice {m k : ℕ} (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, kinetic (ψ.coreSlice s x)) =
      (1/2 : ℝ) * ∑ st : Spins (m+k), ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient st (Fin.natAdd m a.1,a.2) z‖^2 := by
  have hs (s : Spins m) : (∫ x, kinetic (ψ.coreSlice s x)) =
      (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) z‖^2 := by
    rw [integral_congr_ae (kinetic_coreSlice_ae ψ s), integral_const_mul]
    congr 1
    have hi (t : Spins k) (a : Fin k × Fin 3) :
        Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) (joinConfiguration m k z)‖^2)
          (volume.prod volume) :=
      ((ψ.partial_L2 (Fin.append s t) (Fin.natAdd m a.1,a.2)).comp_measurePreserving
        (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
    rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun a _ => (hi t a).integral_prod_left))]
    apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum _ (fun a _ => (hi t a).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro a _
    rw [← integral_prod _ (hi t a)]
    exact (joinConfiguration_measurePreserving m k).integral_comp'
      (fun z => ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) z‖^2)
  simp_rw [hs]
  rw [← Finset.mul_sum, ← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∑ a : Fin k × Fin 3, ∫ z, ‖ψ.gradient (Fin.append st.1 st.2) (Fin.natAdd m a.1,a.2) z‖^2)]
  congr 1
  exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

lemma integral_potentialForm_coreSlice {m k : ℕ} (ψ : H1Vector (m+k))
    (V : Configuration k → ℝ)
    (hV : ∀ st : Spins (m+k), Integrable (fun z => V ((joinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2)) :
    (∑ s : Spins m, ∫ x, potentialForm V (ψ.coreSlice s x)) =
      ∑ st : Spins (m+k), ∫ z, V ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  have hs (s : Spins m) : (∫ x, potentialForm V (ψ.coreSlice s x)) =
      ∑ t : Spins k, ∫ z, V ((joinConfiguration m k).symm z).2 * ‖ψ.value (Fin.append s t) z‖^2 := by
    rw [integral_congr_ae (potentialForm_coreSlice_ae ψ s V)]
    have hi (t : Spins k) : Integrable (fun z : Configuration m × Configuration k =>
        V z.2 * ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) := by
      have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
        (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr
        (hV (Fin.append s t))
      change Integrable (fun z : Configuration m × Configuration k =>
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
    rw [integral_finsetSum _ (fun t _ => (hi t).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro t _
    rw [← integral_prod _ (hi t)]
    have H := (joinConfiguration_measurePreserving m k).integral_comp'
        (fun z => V ((joinConfiguration m k).symm z).2 * ‖ψ.value (Fin.append s t) z‖^2)
    change (∫ z : Configuration m × Configuration k,
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2 ∂volume.prod volume) = _ at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  simp_rw [hs]
  rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∫ z, V ((joinConfiguration m k).symm z).2 * ‖ψ.value (Fin.append st.1 st.2) z‖^2)]
  exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_CoreKinetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma potentialForm_const {n : ℕ} (c : ℝ) (ψ : H1Vector n) :
    potentialForm (fun _ => c) ψ = c * mass ψ := by
  simp only [potentialForm, mass, integral_const_mul, Finset.mul_sum]

noncomputable def coreKinetic {m k : ℕ} (ψ : H1Vector (m+k)) : ℝ :=
  (1/2 : ℝ) * ∑ st : Spins (m+k), ∑ a : Fin k × Fin 3,
    ∫ z, ‖ψ.gradient st (Fin.natAdd m a.1,a.2) z‖^2

lemma kinetic_split {m k : ℕ} (ψ : H1Vector (m+k)) :
    kinetic ψ = coreKinetic ψ + outerKinetic ψ := by
  simp only [kinetic, coreKinetic, outerKinetic, Fintype.sum_prod_type, Fin.sum_univ_add,
    Finset.sum_add_distrib, mul_add]
  ring

lemma conditional_core_form_identity {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) * form S (ψ.coreSlice s x).normalized) =
      coreKinetic ψ - potentialForm (fun z => nuclearPotential S ((joinConfiguration m k).symm z).2) ψ +
        potentialForm (fun z => pairPotential ((joinConfiguration m k).symm z).2) ψ := by
  simp_rw [form_normalized_weight]
  change (∑ s : Spins m, ∫ x, kinetic (ψ.coreSlice s x) -
    potentialForm (nuclearPotential S) (ψ.coreSlice s x) + potentialForm pairPotential (ψ.coreSlice s x)) = _
  have he (s : Spins m) :
      (∫ x, kinetic (ψ.coreSlice s x) - potentialForm (nuclearPotential S) (ψ.coreSlice s x) +
        potentialForm pairPotential (ψ.coreSlice s x)) =
      (∫ x, kinetic (ψ.coreSlice s x)) - (∫ x, potentialForm (nuclearPotential S) (ψ.coreSlice s x)) +
        ∫ x, potentialForm pairPotential (ψ.coreSlice s x) := by
    have H := integral_add ((kinetic_coreSlice_integrable ψ s).sub
      (potentialForm_coreSlice_integrable ψ s (nuclearPotential S)
        (fun t => ψ.core_nuclear_integrable S (Fin.append s t))))
      (potentialForm_coreSlice_integrable ψ s pairPotential
        (fun t => ψ.core_pair_integrable (Fin.append s t)))
    simp only [Pi.sub_apply] at H
    rw [H, integral_sub (kinetic_coreSlice_integrable ψ s)
        (potentialForm_coreSlice_integrable ψ s (nuclearPotential S)
          (fun t => ψ.core_nuclear_integrable S (Fin.append s t)))]
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [integral_kinetic_coreSlice, integral_potentialForm_coreSlice ψ (nuclearPotential S)
    (ψ.core_nuclear_integrable S), integral_potentialForm_coreSlice ψ pairPotential ψ.core_pair_integrable]
  rfl

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RetainedFinePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def retainedFinePower {n : ℕ} (b : ℝ) (r : Configuration n → Finset (Fin n))
    (x : Configuration n) : ℝ :=
  ∫ y, retainedFineDensity b (r x) (position x) y^(5/3:ℝ)

def retainedFineCoulomb {n : ℕ} (b : ℝ) (r : Configuration n → Finset (Fin n))
    (x : Configuration n) : ℝ :=
  coulombBilinear (retainedFineDensity b (r x) (position x))
    (retainedFineDensity b (r x) (position x))/2

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_OuterJoinConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def outerJoinConfiguration (m k : ℕ) :
    (Configuration m × Configuration k) ≃L[ℝ] Configuration (k+m) :=
  (ContinuousLinearEquiv.prodComm ℝ (Configuration m) (Configuration k)).trans
    (joinConfiguration k m)
lemma outerJoinConfiguration_apply (m k : ℕ) (x : Configuration m) (y : Configuration k) :
    outerJoinConfiguration m k (x,y) = joinConfiguration k m (y,x) := rfl
lemma outerJoinConfiguration_measurePreserving (m k : ℕ) :
    MeasurePreserving (outerJoinConfiguration m k).toHomeomorph.toMeasurableEquiv
      (volume.prod volume) volume :=
  (joinConfiguration_measurePreserving k m).comp Measure.measurePreserving_swap
lemma outerJoinConfiguration_right_single (m k : ℕ) (a : Fin k × Fin 3) :
    outerJoinConfiguration m k (0, EuclideanSpace.single a 1) =
      EuclideanSpace.single (Fin.castAdd m a.1,a.2) 1 := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [outerJoinConfiguration_apply, joinConfiguration_left]
    simp [PiLp.single_apply, Prod.ext_iff]
  · intro j
    rw [outerJoinConfiguration_apply, joinConfiguration_right]
    simp only [PiLp.single_apply, PiLp.zero_apply, Prod.mk.injEq]
    split_ifs with h
    · have := congrArg (fun z : Fin (k+m) => z.val) h.1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl
abbrev outerAppend {m k : ℕ} (s : Spins m) (t : Spins k) : Spins (k+m) := Fin.append t s
lemma append_outerPerm {m k : ℕ} (s : Spins m) (t : Spins k) (p : Equiv.Perm (Fin k)) :
    outerAppend s t ∘ outerPerm m p = outerAppend s (t ∘ p) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [outerAppend, outerPerm_left]
  · intro j; simp [outerAppend, outerPerm_right]
lemma permute_outer_join {m k : ℕ} (p : Equiv.Perm (Fin k)) (x : Configuration m)
    (y : Configuration k) :
    permute (outerPerm m p) (outerJoinConfiguration m k (x,y)) =
      outerJoinConfiguration m k (x, permute p y) := by
  rw [outerJoinConfiguration_apply, outerJoinConfiguration_apply]
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    change joinConfiguration k m (y,x) (outerPerm m p (Fin.castAdd m j),b) = _
    rw [outerPerm_left, joinConfiguration_left, joinConfiguration_left]
    rfl
  · intro j
    change joinConfiguration k m (y,x) (outerPerm m p (Fin.natAdd k j),b) = _
    rw [outerPerm_right, joinConfiguration_right, joinConfiguration_right]
lemma H1Vector.weak_partial_outerJoin {m k : ℕ} (ψ : H1Vector (k+m))
    (s : Spins (k+m)) (a : Fin k × Fin 3) :
    ∀ (η : Configuration m × Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η →
      (∫ z, ψ.value s (outerJoinConfiguration m k z) *
        (fderiv ℝ η z (0, EuclideanSpace.single a 1) : ℂ) ∂(volume.prod volume)) =
      -(∫ z, ψ.gradient s (Fin.castAdd m a.1, a.2) (outerJoinConfiguration m k z) *
        (η z : ℂ) ∂(volume.prod volume)) := by
  apply weak_directional_change (outerJoinConfiguration m k) (outerJoinConfiguration_measurePreserving m k)
    (0, EuclideanSpace.single a 1)
  rw [outerJoinConfiguration_right_single]
  exact ψ.weak_partial s (Fin.castAdd m a.1, a.2)

lemma H1Vector.outer_slices_H1 {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    ∀ᵐ x ∂(volume : Measure (Configuration m)),
      (∀ t : Spins k, MemLp (fun y => ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y)) * (φ y : ℂ))) := by
  have hV (t : Spins k) := (ψ.value_L2 (outerAppend s t)).comp_measurePreserving
    (outerJoinConfiguration_measurePreserving m k)
  have hG (t : Spins k) (a : Fin k × Fin 3) :=
    (ψ.partial_L2 (outerAppend s t) (Fin.castAdd m a.1,a.2)).comp_measurePreserving
      (outerJoinConfiguration_measurePreserving m k)
  have hval : ∀ᵐ x ∂(volume : Measure (Configuration m)),
      ∀ t : Spins k, MemLp (fun y => ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))) 2 volume :=
    ae_all_iff.mpr (fun t => memLp_fiber_ae
      (f := fun z : Configuration m × Configuration k =>
        ψ.value (outerAppend s t) (outerJoinConfiguration m k z)) (hV t))
  have hgrad := fun (t : Spins k) (a : Fin k × Fin 3) =>
    weak_slice (hV t) (hG t a) (EuclideanSpace.single a 1)
      (ψ.weak_partial_outerJoin (outerAppend s t) a)
  have hall := ae_all_iff.mpr (fun t => ae_all_iff.mpr (hgrad t))
  filter_upwards [hval, hall] with x hx hall
  exact ⟨hx, fun t a => (hall t a).2⟩

def H1Vector.OuterSliceRegular {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (x : Configuration m) : Prop :=
      (∀ t : Spins k, MemLp (fun y => ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y)) * (φ y : ℂ)))

lemma H1Vector.outerSliceRegular_ae {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    ∀ᵐ x ∂volume, ψ.OuterSliceRegular s x := ψ.outer_slices_H1 s

noncomputable def H1Vector.outerSlice {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (x : Configuration m) : H1Vector k := by
  classical
  exact if h : ψ.OuterSliceRegular s x then
    { value := fun t y => ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))
      gradient := fun t a y => ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
        (outerJoinConfiguration m k (x,y))
      value_L2 := h.1
      partial_L2 := fun t a => (h.2 t a).1
      weak_partial := fun t a => (h.2 t a).2 }
  else H1Vector.zero k

lemma H1Vector.outerSlice_value {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    {x : Configuration m} (hx : ψ.OuterSliceRegular s x) (t : Spins k) (y : Configuration k) :
    (ψ.outerSlice s x).value t y = ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y)) := by
  simp [H1Vector.outerSlice, hx]

lemma H1Vector.outerSlice_gradient {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    {x : Configuration m} (hx : ψ.OuterSliceRegular s x) (t : Spins k) (a : Fin k × Fin 3)
    (y : Configuration k) :
    (ψ.outerSlice s x).gradient t a y =
      ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2) (outerJoinConfiguration m k (x,y)) := by
  simp [H1Vector.outerSlice, hx]

lemma H1Vector.outerSlice_antisymmetric {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (hψ : ∀ (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (outerAppend s t ∘ outerPerm m p) (permute (outerPerm m p) z) =
        (((outerPerm m p).sign : ℤ) : ℂ) * ψ.value (outerAppend s t) z) :
    ∀ᵐ x ∂volume, Antisymmetric (ψ.outerSlice s x) := by
  have h (p : Equiv.Perm (Fin k)) (t : Spins k) :=
    Measure.ae_ae_of_ae_prod ((outerJoinConfiguration_measurePreserving m k).quasiMeasurePreserving.ae (hψ p t))
  have hall := ae_all_iff.mpr (fun p => ae_all_iff.mpr (h p))
  filter_upwards [ψ.outerSliceRegular_ae s, hall] with x hx hxA
  intro p t
  filter_upwards [hxA p t] with y hy
  change ψ.value (outerAppend s t ∘ outerPerm m p)
      (permute (outerPerm m p) (outerJoinConfiguration m k (x,y))) =
    (((outerPerm m p).sign : ℤ) : ℂ) * ψ.value (outerAppend s t)
      (outerJoinConfiguration m k (x,y)) at hy
  simpa only [ψ.outerSlice_value s hx, append_outerPerm, outerPerm_sign, permute_outer_join] using hy

lemma outerJoinConfiguration_symm_snd (m k : ℕ) (z : Configuration (k+m)) :
    ((outerJoinConfiguration m k).symm z).2 = ((joinConfiguration k m).symm z).1 := rfl
end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma outerKinetic_nonneg {m k : ℕ} (ψ : H1Vector (m+k)) : 0 ≤ outerKinetic ψ := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SliceExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def retainedNuclearPotential {M m : ℕ} (S : Nuclei M)
    (r : Configuration m → Finset (Fin m)) (x : Configuration m) : ℝ :=
  ∑ i ∈ r x, attraction S (position x i)

def retainedCrossPotential {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (y : Configuration k) : ℝ :=
  ∑ i ∈ r x, ∑ j : Fin k, coulombKernel (position x i-position y j)

lemma retainedNuclearPotential_nonneg {M m : ℕ} (S : Nuclei M)
    (r : Configuration m → Finset (Fin m)) (x : Configuration m) :
    0 ≤ retainedNuclearPotential S r x := Finset.sum_nonneg (fun i _ => attraction_nonneg S (position x i))
lemma retainedNuclearPotential_le {M m : ℕ} (S : Nuclei M)
    (r : Configuration m → Finset (Fin m)) (x : Configuration m) :
    retainedNuclearPotential S r x ≤ nuclearPotential S x :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => attraction_nonneg S (position x i))

lemma retainedCrossPotential_nonneg {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (y : Configuration k) : 0 ≤ retainedCrossPotential r x y :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => coulombKernel_nonneg _))
lemma retainedCrossPotential_measurable {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (fun p : Configuration m × Configuration k => retainedCrossPotential r p.1 p.2) := by
  unfold retainedCrossPotential
  apply measurable_retained_sum (fun p : Configuration m × Configuration k => r p.1)
    (fun i => (hr i).preimage measurable_fst)
  intro i
  apply Finset.measurable_sum
  intro j _
  exact coulombKernel_measurable.comp (((positionCLM i).measurable.comp measurable_fst).sub
    ((positionCLM j).measurable.comp measurable_snd))

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DeletedLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma sliceExpectation_add {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Spins m → Configuration m → ℝ)
    (hf : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*f s x))
    (hg : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*g s x)) :
    sliceExpectation ψ (fun s x => f s x+g s x) = sliceExpectation ψ f + sliceExpectation ψ g := by
  simp only [sliceExpectation, mul_add, integral_add (hf _) (hg _), Finset.sum_add_distrib]
lemma sliceExpectation_sub {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Spins m → Configuration m → ℝ)
    (hf : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*f s x))
    (hg : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*g s x)) :
    sliceExpectation ψ (fun s x => f s x-g s x) = sliceExpectation ψ f - sliceExpectation ψ g := by
  simp only [sliceExpectation, mul_sub, integral_sub (hf _) (hg _), Finset.sum_sub_distrib]
lemma sliceExpectation_const_mul {m k : ℕ} (ψ : H1Vector (m+k))
    (c : ℝ) (f : Spins m → Configuration m → ℝ) :
    sliceExpectation ψ (fun s x => c*f s x) = c*sliceExpectation ψ f := by
  simp only [sliceExpectation, mul_left_comm (mass _) c, integral_const_mul, Finset.mul_sum]

def discreteFineTF {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (b : ℝ) (r : Configuration m → Finset (Fin m)) (s : Spins m) (x : Configuration m) : ℝ :=
  thomasFermiCoefficient*retainedFinePower b r x + retainedFineCoulomb b r x -
    ∑ i ∈ r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_FineKernelShiftCoulombIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma fineKernel_shift_coulomb_integrable {b : ℝ} (hb : 0 < b) (a x : Space) :
    Integrable (fun y => coulombKernel (a-y)*fineKernel b (y-x)) := by
  have h := (fineKernel_coulomb_integrable hb (a-x)).comp_sub_right x
  apply h.congr
  exact Eventually.of_forall (fun y => by
    change coulombKernel (a-x-(y-x))*fineKernel b (y-x) = _
    rw [show a-x-(y-x) = a-y by abel])

lemma fineKernel_shift_coulomb_eq {b : ℝ} (hb : 0 < b) (a x : Space)
    (hsep : Real.sqrt 3*b ≤ ‖a-x‖) :
    (∫ y, coulombKernel (a-y)*fineKernel b (y-x)) = coulombKernel (a-x) := by
  rw [fineKernel_shift_coulomb_integral, fineKernel_coulomb_eq hb hsep]

lemma retainedFineDensity_coulomb_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) (a : Space) :
    Integrable (fun y => coulombKernel (a-y)*retainedFineDensity b r x y) := by
  simp only [retainedFineDensity, Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ => fineKernel_shift_coulomb_integrable hb a (x i))

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawThomasFermiEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def SourceFreeHoleDensity {M k : ℕ} (S : Nuclei M) (u : H1Vector k)
    (g : 𝓢(Space,ℝ)) (R : ℝ) (ρ : Space → ℝ) (K A : Set Space) : Prop :=
  (∀ y, 0 ≤ ρ y) ∧ Measurable ρ ∧ Integrable (fun y => ρ y^(5/3:ℝ)) ∧
  IsCompact K ∧ IsClosed A ∧ (∀ y, y ∉ K → ρ y=0) ∧ SpatiallySupported u A ∧
  Disjoint A (K+tsupport (g : Space → ℝ)) ∧
  (∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖) ∧
  (∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖)

def packetKineticError (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) : ℝ :=
  (1/2:ℝ)*(∫ y, ρ y)*(∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2)

lemma sliceExpectation_number {m k : ℕ} (ψ : H1Vector (m+k)) (E : ℝ) :
    sliceExpectation ψ (fun _ _ => E) = E*mass ψ := by
  simp only [sliceExpectation, mul_comm (mass _) E, integral_const_mul, ←Finset.mul_sum]
  rw [integral_mass_coreSlice]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_CoulombKernelFiveHalvesIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma coulombKernel_fiveHalves_integrableOn (R : ℝ) :
    IntegrableOn (fun x : Space => coulombKernel x ^ (5/2:ℝ)) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 5/2) (by simp) (by norm_num)
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (coulombKernel_nonneg x) _)]
      simp [coulombKernel, Real.rpow_neg_eq_inv_rpow])
  · exact (coulombKernel_measurable.pow_const _).aestronglyMeasurable

lemma truncatedCoulomb_memLp (R : ℝ) :
    MemLp (truncatedCoulomb R) (ENNReal.ofReal (5/2:ℝ)) volume := by
  apply (integrable_norm_rpow_iff
    (coulombKernel_measurable.indicator measurableSet_ball).aestronglyMeasurable
    (by norm_num) (by simp)).mp
  have H := (coulombKernel_fiveHalves_integrableOn R).integrable_indicator measurableSet_ball
  apply H.congr
  filter_upwards [] with x
  by_cases hx : x ∈ Metric.ball (0:Space) R
  · simp [hx, Real.norm_of_nonneg (coulombKernel_nonneg x), ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤5/2)]
  · simp [hx, ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤5/2)]

lemma truncatedCoulomb_fiveHalves_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Space, ‖truncatedCoulomb R x‖ ^ (5/2:ℝ)) =
      8*Real.pi*R^(1/2:ℝ) := by
  have he (x : Space) : ‖truncatedCoulomb R x‖ ^ (5/2:ℝ) =
      if ‖x‖ < R then ‖x‖ ^ (-(5/2:ℝ)) else 0 := by
    by_cases hx : ‖x‖ < R
    · simp [truncatedCoulomb, Metric.mem_ball, dist_zero_right, hx, coulombKernel,
        ← Real.rpow_neg_eq_inv_rpow]
    · simp [truncatedCoulomb, Metric.mem_ball, dist_zero_right, hx]
  simp_rw [he]
  rw [integral_fun_norm_addHaar (volume : Measure Space)
    (fun t : ℝ => if t < R then t ^ (-(5/2:ℝ)) else 0)]
  have hball : volume.real (Metric.ball (0 : Space) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [hdim, hball, nsmul_eq_mul, smul_eq_mul]
  have hint : (∫ t in Ioi (0:ℝ), t^(3-1) * (if t < R then t^(-(5/2:ℝ)) else 0)) =
      ∫ t in Ioo 0 R, t^(-(1/2:ℝ)) := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Iio R).indicator (fun u : ℝ => u^(-(1/2:ℝ))) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change 0 < t at ht
        by_cases h : t < R
        · simp only [h, ite_true, Set.indicator, mem_Iio]
          rw [show (3:ℕ)-1=2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_add ht]
          norm_num
        · simp [Set.indicator, h]
      _ = _ := by rw [integral_indicator measurableSet_Iio,
        Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio]
  rw [hint, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR,
    integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ)))]
  norm_num
  ring

lemma truncatedCoulomb_mul_integrable {f : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume) (R : ℝ) (x : Space) :
    Integrable (fun y => truncatedCoulomb R (x-y)*f y) := by
  have hk := (truncatedCoulomb_memLp R).comp_measurePreserving
    (volume.measurePreserving_sub_left x)
  have : ENNReal.HolderConjugate (ENNReal.ofReal (5/2:ℝ))
      (ENNReal.ofReal (5/3:ℝ)) := by
    exact coulomb_holder_exponents.ennrealOfReal
  exact hk.integrable_mul hf

lemma coulomb_near_holder {f : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume) {R : ℝ} (hR : 0 ≤ R) (x : Space) :
    (∫ y, truncatedCoulomb R (x-y)*‖f y‖) ≤
      (8*Real.pi*R^(1/2:ℝ))^(2/5:ℝ) * (∫ y, ‖f y‖^(5/3:ℝ))^(3/5:ℝ) := by
  have hk := (truncatedCoulomb_memLp R).comp_measurePreserving
    (volume.measurePreserving_sub_left x)
  have H := integral_mul_norm_le_Lp_mul_Lq coulomb_holder_exponents hk hf
  simp only [Function.comp_apply] at H
  rw [integral_sub_left_eq_self (fun z : Space => ‖truncatedCoulomb R z‖^(5/2:ℝ)) volume x,
    truncatedCoulomb_fiveHalves_integral hR] at H
  simpa only [Real.norm_of_nonneg (truncatedCoulomb_nonneg ..),
    show (1:ℝ)/(5/2)=2/5 by norm_num, show (1:ℝ)/(5/3)=3/5 by norm_num] using H
lemma coulomb_lp_integrand_bound {R : ℝ} (hR : 0 < R) (x y : Space) :
    coulombKernel (x-y) ≤ truncatedCoulomb R (x-y)+R⁻¹ := by
  by_cases h : x-y ∈ Metric.ball (0:Space) R
  · rw [truncatedCoulomb, Set.indicator_of_mem h]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hR.le)
  · rw [truncatedCoulomb, Set.indicator_of_notMem h, zero_add]
    have hn : R ≤ ‖x-y‖ := by simpa [Metric.mem_ball, dist_zero_right] using h
    exact inv_anti₀ hR hn

lemma coulomb_lp_convolution_integrable {f : Space → ℝ} (hf : Integrable f)
    (hfm : Measurable f) (hfp : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*f y) := by
  have hi := (truncatedCoulomb_mul_integrable hfp.norm 1 x).add hf.norm
  apply hi.mono'
    ((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hfm).aestronglyMeasurable
  filter_upwards [] with y
  change ‖coulombKernel (x-y)*f y‖ ≤ truncatedCoulomb 1 (x-y)*‖f y‖+‖f y‖
  rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
  calc
    _ ≤ (truncatedCoulomb 1 (x-y)+1)*‖f y‖ :=
      mul_le_mul_of_nonneg_right (by simpa using coulomb_lp_integrand_bound (by norm_num : (0:ℝ)<1) x y)
        (norm_nonneg _)
    _ = _ := by ring

lemma coulomb_lp_convolution_bound {f : Space → ℝ} (hf : Integrable f)
    (hfm : Measurable f) (hfp : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume)
    {R : ℝ} (hR : 0 < R) (x : Space) :
    (∫ y, coulombKernel (x-y)*‖f y‖) ≤
      (8*Real.pi*R^(1/2:ℝ))^(2/5:ℝ)*(∫ y, ‖f y‖^(5/3:ℝ))^(3/5:ℝ) +
      R⁻¹*(∫ y, ‖f y‖) := by
  have hi := truncatedCoulomb_mul_integrable hfp.norm R x
  calc
    _ ≤ ∫ y, truncatedCoulomb R (x-y)*‖f y‖ + R⁻¹*‖f y‖ :=
      integral_mono (coulomb_lp_convolution_integrable hf.norm hfm.norm hfp.norm x)
        (hi.add (hf.norm.const_mul _)) (fun y => by
          simpa only [add_mul] using
            mul_le_mul_of_nonneg_right (coulomb_lp_integrand_bound hR x y) (norm_nonneg (f y)))
    _ = (∫ y, truncatedCoulomb R (x-y)*‖f y‖) + R⁻¹*(∫ y, ‖f y‖) := by
      rw [integral_add hi (hf.norm.const_mul _), integral_const_mul]
    _ ≤ _ := add_le_add (coulomb_near_holder hfp hR.le x) le_rfl

lemma coulomb_lp_pair_integrable {f g : Space → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hg : Integrable g) (hgm : Measurable g)
    (hgp : MemLp g (ENNReal.ofReal (5/3:ℝ)) volume) :
    Integrable (fun p : Space × Space => f p.1*g p.2*coulombKernel (p.1-p.2)) := by
  have hm : Measurable (fun p : Space × Space => f p.1*g p.2*coulombKernel (p.1-p.2)) :=
    ((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul
      (coulombKernel_measurable.comp (measurable_fst.sub measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply ae_of_all
    intro x
    have hi := (coulomb_lp_convolution_integrable hg hgm hgp x).const_mul (f x)
    exact hi.congr (ae_of_all _ (fun y => by dsimp only; ring))
  · let A : ℝ := (8*Real.pi)^(2/5:ℝ)*(∫ y, ‖g y‖^(5/3:ℝ))^(3/5:ℝ) + ∫ y, ‖g y‖
    have hb (x : Space) : (∫ y, coulombKernel (x-y)*‖g y‖) ≤ A := by
      simpa [A] using coulomb_lp_convolution_bound hg hgm hgp (by norm_num : (0:ℝ)<1) x
    have he (x : Space) : (∫ y, ‖f x*g y*coulombKernel (x-y)‖) =
        ‖f x‖*(∫ y, coulombKernel (x-y)*‖g y‖) := by
      simp_rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
      simp_rw [mul_assoc, mul_comm ‖g _‖ (coulombKernel _)]
      rw [integral_const_mul]
    apply (hf.norm.mul_const A).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [] with x
    change ‖∫ y, ‖f x*g y*coulombKernel (x-y)‖‖ ≤ ‖f x‖*A
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable def gaussian (a : ℝ) (x : Space) : ℝ := Real.exp (-a*‖x‖^2)
lemma gaussian_pos (a : ℝ) (x : Space) : 0 < gaussian a x := Real.exp_pos _
lemma gaussian_le_one {a : ℝ} (ha : 0 ≤ a) (x : Space) : gaussian a x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg ‖x‖]
lemma gaussian_continuous (a : ℝ) : Continuous (gaussian a) := by unfold gaussian; fun_prop
lemma gaussian_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussian a) := by
  change Integrable (fun x : Space => Real.exp (-a*‖x‖^2))
  have H := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V:=Space)
    (show 0 < (a : ℂ).re from ha) 0 0).re
  change Integrable (fun x : Space => (Complex.exp (-(a:ℂ)*↑‖x‖^2 + 0 * ↑(inner ℝ (0:Space) x))).re) at H
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re, gaussian] using H
lemma gaussian_integral {a : ℝ} (ha : 0 < a) :
    (∫ x, gaussian a x) = (Real.pi/a)^(3/2:ℝ) := by
  simpa [gaussian] using GaussianFourier.integral_rexp_neg_mul_sq_norm (V:=Space) ha
lemma kernel_gaussian_integral {d : Space} (hd : d ≠ 0) :
    ‖d‖⁻¹ = (Real.sqrt Real.pi)⁻¹ * ∫ t : ℝ, gaussian (t^2) d := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  rw [integral_gaussian, Real.sqrt_div (by positivity), Real.sqrt_sq (norm_nonneg _)]
  field_simp

lemma gaussian_product (a : ℝ) (x y z : Space) :
    gaussian (2*a) (x-z)*gaussian (2*a) (y-z) =
      gaussian a (x-y)*gaussian (4*a) (z-(1/2:ℝ) • (x+y)) := by
  unfold gaussian
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2),
    inner_smul_right, inner_add_right]
  rw [mul_pow, norm_add_sq_real]
  rw [real_inner_comm z x, real_inner_comm z y]
  ring

lemma gaussian_product_integrable {a : ℝ} (ha : 0 < a) (x y : Space) :
    Integrable (fun z => gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) := by
  simp_rw [gaussian_product]
  exact ((gaussian_integrable (by positivity : 0 < 4*a)).comp_sub_right _).const_mul _

lemma gaussian_convolution_identity {a : ℝ} (ha : 0 < a) (x y : Space) :
    (∫ z, gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) =
      gaussian a (x-y)*(Real.pi/(4*a))^(3/2:ℝ) := by
  simp_rw [gaussian_product]
  rw [integral_const_mul, integral_sub_right_eq_self, gaussian_integral (by positivity)]

lemma integrable_gaussian_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun p : Space × Space => f p.1*f p.2*gaussian a (p.1-p.2)) := by
  apply (hf.norm.mul_prod hf.norm).mono' (by
    apply Measurable.aestronglyMeasurable
    exact ((hm.comp measurable_fst).mul (hm.comp measurable_snd)).mul
      ((gaussian_continuous a).measurable.comp (by fun_prop)))
  exact Filter.Eventually.of_forall (fun p => by
    simp only [norm_mul, Real.norm_of_nonneg (gaussian_pos a _).le]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (gaussian_le_one ha _))

lemma gaussian_square_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
  have hm' : Measurable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
    have h1 : Measurable (fun q : (Space × Space) × Space => f q.1.1*f q.1.2) :=
      (hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))
    apply h1.mul
    exact ((gaussian_continuous _).measurable.comp (by fun_prop)).mul
      ((gaussian_continuous _).measurable.comp (by fun_prop))
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p => (gaussian_product_integrable ha p.1 p.2).const_mul (f p.1*f p.2))
  · have he (p : Space × Space) :
        (∫ z, ‖(f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))‖) =
          (‖f p.1‖*‖f p.2‖*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
      simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
      rw [integral_const_mul, gaussian_convolution_identity ha]
      ring
    simp_rw [he]
    exact (integrable_gaussian_pair hf.norm hm.norm ha.le).mul_const _

lemma gaussian_form_nonneg {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2) := by
  have hi := gaussian_square_integrable hf hm ha
  have H := integral_integral_swap (f := fun (p : Space × Space) (z : Space) =>
    (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) hi
  have hleft (p : Space × Space) :
      (∫ z, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (f p.1*f p.2*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
    rw [integral_const_mul, gaussian_convolution_identity ha]
    ring
  have hright (z : Space) :
      (∫ p : Space × Space, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (∫ x, f x*gaussian (2*a) (x-z))^2 := by
    simp_rw [show ∀ p : Space × Space,
      (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z)) =
      (f p.1*gaussian (2*a) (p.1-z))*(f p.2*gaussian (2*a) (p.2-z)) from fun p => by ring]
    exact (integral_prod_mul (μ:=volume) (ν:=volume)
      (fun x : Space => f x*gaussian (2*a) (x-z))
      (fun x : Space => f x*gaussian (2*a) (x-z))).trans (pow_two _).symm
  simp_rw [hleft, hright] at H
  rw [integral_mul_const] at H
  have hnonneg : 0 ≤ (∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2)) *
      (Real.pi/(4*a))^(3/2:ℝ) := H.symm ▸ integral_nonneg (fun z => sq_nonneg _)
  exact nonneg_of_mul_nonneg_left hnonneg (Real.rpow_pos_of_pos (by positivity) _)
lemma space_ae_distinct : ∀ᵐ p : Space × Space, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Filter.Eventually.of_forall (fun x => by
    rw [ae_iff]
    simp only [not_not]
    have he : {y : Space | x = y} = {x} := by ext y; simp [eq_comm]
    change volume {y : Space | x = y} = 0
    rw [he, measure_singleton])

lemma gaussian_parameter_integrable {d : Space} (hd : d ≠ 0) :
    Integrable (fun t : ℝ => gaussian (t^2) d) := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  exact integrable_exp_neg_mul_sq (sq_pos_of_pos (norm_pos_iff.mpr hd))

lemma gaussian_parameter_integral {d : Space} (hd : d ≠ 0) :
    (∫ t : ℝ, gaussian (t^2) d) = coulombKernel d * Real.sqrt Real.pi := by
  have H := kernel_gaussian_integral hd
  unfold coulombKernel
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    _ = ((Real.sqrt Real.pi)⁻¹*(∫ t : ℝ, gaussian (t^2) d))*Real.sqrt Real.pi := by field_simp
    _ = _ := by rw [← H]

lemma coulomb_gaussian_integrable_of_pair {f : Space → ℝ} (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    Integrable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
  have hm' : Measurable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
    apply ((hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))).mul
    unfold gaussian
    fun_prop
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [space_ae_distinct] with p hp
    exact (gaussian_parameter_integrable (sub_ne_zero.mpr hp)).const_mul (f p.1*f p.2)
  · have hi := hp.norm.mul_const (Real.sqrt Real.pi)
    apply hi.congr
    filter_upwards [space_ae_distinct] with p hp
    simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    simp only [Real.norm_of_nonneg (coulombKernel_nonneg _)]
    ring

lemma coulomb_form_nonneg_of_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2) := by
  have hi := coulomb_gaussian_integrable_of_pair hm hp
  have H := integral_integral_swap (f := fun (p : Space × Space) (t : ℝ) =>
    f p.1*f p.2*gaussian (t^2) (p.1-p.2)) hi
  have hl : (∫ p : Space × Space, ∫ t : ℝ, f p.1*f p.2*gaussian (t^2) (p.1-p.2)) =
      (∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2))*Real.sqrt Real.pi := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [space_ae_distinct] with p hp
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    ring
  rw [hl] at H
  have ht : ∀ᵐ t : ℝ, t ≠ 0 := by rw [ae_iff]; simp
  have hn : 0 ≤ ∫ t : ℝ, ∫ p : Space × Space, f p.1*f p.2*gaussian (t^2) (p.1-p.2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ht] with t ht
    exact gaussian_form_nonneg hf hm (sq_pos_of_ne_zero ht)
  rw [← H] at hn
  exact nonneg_of_mul_nonneg_left hn (Real.sqrt_pos.mpr Real.pi_pos)

lemma coulomb_lp_form_nonneg {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    (hp : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2) :=
  coulomb_form_nonneg_of_pair hf hm (coulomb_lp_pair_integrable hf hm hf hm hp)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def tfExtend (Ω : Set Space) (f : TFLp (volume.restrict Ω)) : Space → ℝ :=
  Ω.indicator f
lemma tfExtend_measurable {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    Measurable (tfExtend Ω f) := (Lp.stronglyMeasurable f).measurable.indicator hΩ
lemma tfExtend_memLp {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    MemLp (tfExtend Ω f) TFExponent volume :=
  (memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp f)
lemma tfExtend_integrable {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f : TFLp (volume.restrict Ω)) :
    Integrable (tfExtend Ω f) :=
  (show IntegrableOn (fun x => f x) Ω volume from
    (Lp.memLp f).integrable (show 1 ≤ TFExponent by norm_num [TFExponent])).integrable_indicator hΩ
lemma tfExtend_norm_integral {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    (∫ x, ‖tfExtend Ω f x‖) = ∫ x in Ω, ‖f x‖ := by
  simp only [tfExtend, norm_indicator_eq_indicator_norm, integral_indicator hΩ]
lemma tfExtend_norm_power_integral {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    (∫ x, ‖tfExtend Ω f x‖^(5/3:ℝ)) = ‖f‖^(5/3:ℝ) := by
  rw [tfLp_norm_power]
  rw [← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ω <;> simp [tfExtend, hx]

noncomputable def tfCoulomb (Ω : Set Space) (f g : TFLp (volume.restrict Ω)) : ℝ :=
  ∫ p : Space × Space, tfExtend Ω f p.1 * tfExtend Ω g p.2 * coulombKernel (p.1-p.2)
lemma tfCoulomb_integrable {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f g : TFLp (volume.restrict Ω)) :
    Integrable (fun p : Space × Space => tfExtend Ω f p.1 * tfExtend Ω g p.2 * coulombKernel (p.1-p.2)) :=
  coulomb_lp_pair_integrable (tfExtend_integrable hΩ f) (tfExtend_measurable hΩ f)
    (tfExtend_integrable hΩ g) (tfExtend_measurable hΩ g) (tfExtend_memLp hΩ g)
lemma tfCoulomb_self_nonneg {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f : TFLp (volume.restrict Ω)) :
    0 ≤ tfCoulomb Ω f f :=
  coulomb_lp_form_nonneg (tfExtend_integrable hΩ f) (tfExtend_measurable hΩ f) (tfExtend_memLp hΩ f)
lemma tfExtend_convolution_bound {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f : TFLp (volume.restrict Ω)) (x : Space) :
    (∫ y, coulombKernel (x-y)*‖tfExtend Ω f y‖) ≤
      ((8*Real.pi)^(2/5:ℝ) + (volume.real Ω)^(2/5:ℝ))*‖f‖ := by
  have H := coulomb_lp_convolution_bound (tfExtend_integrable hΩ f) (tfExtend_measurable hΩ f)
    (tfExtend_memLp hΩ f) (by norm_num : (0:ℝ)<1) x
  rw [tfExtend_norm_power_integral hΩ, ← Real.rpow_mul (norm_nonneg f)] at H
  norm_num only [Real.one_rpow, mul_one, inv_one, one_mul, show (5/3:ℝ)*(3/5)=1 by norm_num,
    Real.rpow_one] at H
  rw [tfExtend_norm_integral hΩ] at H
  have H1 := tfLp_integral_norm_le f
  simp only [Measure.real, Measure.restrict_apply_univ] at H1
  dsimp only [Measure.real]
  nlinarith
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tfExtend_add_ae {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (f g : TFLp (volume.restrict Ω)) :
    tfExtend Ω (f+g) =ᵐ[volume] fun x => tfExtend Ω f x + tfExtend Ω g x := by
  filter_upwards [(ae_restrict_iff' hΩ).mp (Lp.coeFn_add f g)] with x hx
  by_cases h : x ∈ Ω
  · simpa only [tfExtend, Set.indicator_of_mem h, Pi.add_apply] using hx h
  · simp [tfExtend, h]
lemma tfExtend_smul_ae {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (c : ℝ) (f : TFLp (volume.restrict Ω)) :
    tfExtend Ω (c • f) =ᵐ[volume] fun x => c * tfExtend Ω f x := by
  filter_upwards [(ae_restrict_iff' hΩ).mp (Lp.coeFn_smul c f)] with x hx
  by_cases h : x ∈ Ω
  · simpa only [tfExtend, Set.indicator_of_mem h, Pi.smul_apply, smul_eq_mul] using hx h
  · simp [tfExtend, h]
lemma tfCoulomb_symm {Ω : Set Space} (f g : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω f g = tfCoulomb Ω g f := by
  unfold tfCoulomb
  rw [Measure.volume_eq_prod]
  rw [← integral_prod_swap (fun p : Space × Space => tfExtend Ω g p.1*tfExtend Ω f p.2*coulombKernel (p.1-p.2))]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [Prod.swap, coulombKernel, norm_sub_rev]
  ring
lemma tfCoulomb_add_left {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f g h : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω (f+g) h = tfCoulomb Ω f h + tfCoulomb Ω g h := by
  have H := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp (tfExtend_add_ae hΩ f g)
  change _ =ᵐ[(volume : Measure Space).prod volume] _ at H
  unfold tfCoulomb
  rw [← integral_add (tfCoulomb_integrable hΩ f h) (tfCoulomb_integrable hΩ g h)]
  apply integral_congr_ae
  filter_upwards [H] with p hp
  dsimp only [Function.comp_def] at hp
  rw [hp]
  ring
lemma tfCoulomb_smul_left {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (c : ℝ) (f g : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω (c • f) g = c * tfCoulomb Ω f g := by
  have H := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp (tfExtend_smul_ae hΩ c f)
  change _ =ᵐ[(volume : Measure Space).prod volume] _ at H
  unfold tfCoulomb
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [H] with p hp
  dsimp only [Function.comp_def] at hp
  rw [hp]
  ring
lemma tfCoulomb_bound {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f g : TFLp (volume.restrict Ω)) :
    ‖tfCoulomb Ω f g‖ ≤
      ((volume.real Ω)^(2/5:ℝ)*((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ)))*‖f‖*‖g‖ := by
  let A := ((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ))*‖g‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hi := (tfCoulomb_integrable hΩ f g).norm
  have hiter : (∫ p : Space × Space, ‖tfExtend Ω f p.1*tfExtend Ω g p.2*coulombKernel (p.1-p.2)‖) =
      ∫ x, ‖tfExtend Ω f x‖*(∫ y, coulombKernel (x-y)*‖tfExtend Ω g y‖) := by
    rw [Measure.volume_eq_prod, integral_prod _ hi]
    congr 1; funext x
    simp_rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
    simp_rw [mul_assoc, mul_comm ‖tfExtend Ω g _‖ (coulombKernel _)]
    rw [integral_const_mul]
  calc
    _ ≤ ∫ p : Space × Space, ‖tfExtend Ω f p.1*tfExtend Ω g p.2*coulombKernel (p.1-p.2)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := hiter
    _ ≤ ∫ x, ‖tfExtend Ω f x‖*A := by
      apply integral_mono
      · convert hi.integral_prod_left using 1
        all_goals try with_reducible_and_instances rfl
        funext x
        simp_rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
        simp_rw [mul_assoc, mul_comm ‖tfExtend Ω g _‖ (coulombKernel _)]
        rw [integral_const_mul]
      · exact (tfExtend_integrable hΩ f).norm.mul_const A
      · intro x
        exact mul_le_mul_of_nonneg_left (tfExtend_convolution_bound hΩ g x) (norm_nonneg _)
    _ = (∫ x in Ω, ‖f x‖)*A := by rw [integral_mul_const, tfExtend_norm_integral hΩ]
    _ ≤ ((volume.real Ω)^(2/5:ℝ)*‖f‖)*A := by
      apply mul_le_mul_of_nonneg_right _ hA
      simpa only [Measure.real, Measure.restrict_apply_univ] using tfLp_integral_norm_le f
    _ = _ := by dsimp [A]; ring
noncomputable def tfCoulombLinear {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] :
    TFLp (volume.restrict Ω) →ₗ[ℝ] TFLp (volume.restrict Ω) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (tfCoulomb Ω) (tfCoulomb_add_left hΩ)
    (fun c f g => tfCoulomb_smul_left hΩ c f g)
    (fun f g h => by rw [tfCoulomb_symm, tfCoulomb_add_left hΩ, tfCoulomb_symm g, tfCoulomb_symm h])
    (fun c f g => by rw [tfCoulomb_symm, tfCoulomb_smul_left hΩ, tfCoulomb_symm g]; rfl)
noncomputable def tfCoulombContinuous {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] :
    TFLp (volume.restrict Ω) →L[ℝ] TFLp (volume.restrict Ω) →L[ℝ] ℝ :=
  (tfCoulombLinear hΩ).mkContinuous₂
    ((volume.real Ω)^(2/5:ℝ)*((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ)))
    (tfCoulomb_bound hΩ)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfFunctionalGapControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
noncomputable def tfEnergy (c : ℝ) (W : TFLq (volume.restrict Ω))
    (f : TFLp (volume.restrict Ω)) : ℝ :=
  tfFunctional c (tfFieldContinuous W) (tfCoulombContinuous hΩ) f
lemma tfEnergy_formula (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfEnergy hΩ c W f = c*(∫ x in Ω, (f x)^(5/3:ℝ)) -
      (∫ x in Ω, W x*f x) + tfCoulomb Ω f f/2 := by
  unfold tfEnergy tfFunctional
  rw [tfLp_nonneg_power hf]
  rfl
lemma tfEnergy_exists_unique_minimizer {c : ℝ} (hc : 0 < c)
    (W : TFLq (volume.restrict Ω)) :
    ∃! f : TFLp (volume.restrict Ω), TFNonneg f ∧
      ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g := by
  have hB : ∀ f, 0 ≤ (tfCoulombContinuous hΩ) f f := tfCoulomb_self_nonneg hΩ
  obtain ⟨f,hf,hfm⟩ := tfFunctional_exists_minimizer hc (tfFieldContinuous W) (tfCoulombContinuous hΩ) hB
  refine ⟨f,⟨hf,hfm⟩,?_⟩
  rintro g ⟨hg,hgm⟩
  exact tfFunctional_minimizer_unique hc _ _ hB hg hf hgm hfm
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
noncomputable def tfPotential (f : TFLp (volume.restrict Ω)) (x : Space) : ℝ :=
  ∫ y, coulombKernel (x-y)*tfExtend Ω f y
include hΩ
lemma tfPotential_integrand (f : TFLp (volume.restrict Ω)) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*tfExtend Ω f y) :=
  coulomb_lp_convolution_integrable (tfExtend_integrable hΩ f) (tfExtend_measurable hΩ f)
    (tfExtend_memLp hΩ f) x
omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_measurable (f : TFLp (volume.restrict Ω)) : Measurable (tfPotential f) := by
  have H : StronglyMeasurable (fun p : Space × Space => coulombKernel (p.1-p.2)*tfExtend Ω f p.2) :=
    ((coulombKernel_measurable.comp (measurable_fst.sub measurable_snd)).mul
      ((tfExtend_measurable hΩ f).comp measurable_snd)).stronglyMeasurable
  exact H.integral_prod_right'.measurable
lemma tfPotential_bound (f : TFLp (volume.restrict Ω)) (x : Space) :
    ‖tfPotential f x‖ ≤ ((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ))*‖f‖ := by
  calc
    _ ≤ ∫ y, ‖coulombKernel (x-y)*tfExtend Ω f y‖ := norm_integral_le_integral_norm _
    _ = ∫ y, coulombKernel (x-y)*‖tfExtend Ω f y‖ := by
      simp only [norm_mul,Real.norm_of_nonneg (coulombKernel_nonneg _)]
    _ ≤ _ := tfExtend_convolution_bound hΩ f x
lemma tfPotential_memLp (f : TFLp (volume.restrict Ω)) :
    MemLp (tfPotential f) TFFieldExponent (volume.restrict Ω) :=
  MemLp.of_bound (tfPotential_measurable hΩ f).aestronglyMeasurable _
    (Eventually.of_forall (tfPotential_bound hΩ f))
noncomputable def tfPotentialField (f : TFLp (volume.restrict Ω)) : TFLq (volume.restrict Ω) :=
  (tfPotential_memLp hΩ f).toLp (tfPotential f)
lemma tfPotentialField_coe (f : TFLp (volume.restrict Ω)) :
    tfPotentialField hΩ f =ᵐ[volume.restrict Ω] tfPotential f := MemLp.coeFn_toLp _
lemma tfCoulomb_eq_potential (f g : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω f g = ∫ x in Ω, f x*tfPotential g x := by
  rw [tfCoulomb,Measure.volume_eq_prod,integral_prod _ (tfCoulomb_integrable hΩ f g)]
  rw [← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show (∫ y, tfExtend Ω f x*tfExtend Ω g y*coulombKernel (x-y)) =
      tfExtend Ω f x*tfPotential g x by
    unfold tfPotential
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring]
  by_cases hx : x ∈ Ω <;> simp [tfExtend,hx]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfFunctionalUniformBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
noncomputable def tfMinimizer {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω)) : TFLp (volume.restrict Ω) :=
  Classical.choose (tfEnergy_exists_unique_minimizer hΩ hc W)
lemma tfMinimizer_nonneg {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω)) :
    TFNonneg (tfMinimizer hΩ hc W) := (Classical.choose_spec (tfEnergy_exists_unique_minimizer hΩ hc W)).1.1
lemma tfMinimizer_min {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω)) :
    ∀ g, TFNonneg g → tfEnergy hΩ c W (tfMinimizer hΩ hc W) ≤ tfEnergy hΩ c W g :=
  (Classical.choose_spec (tfEnergy_exists_unique_minimizer hΩ hc W)).1.2
lemma tfMinimizer_continuous {c : ℝ} (hc : 0 < c) : Continuous (tfMinimizer hΩ hc) := by
  rw [continuous_iff_continuousAt]
  intro W
  exact tfFunctional_minimizers_tendsto hc (tfFieldContinuous.continuous.tendsto W)
    (tfCoulombContinuous hΩ) (tfCoulomb_self_nonneg hΩ) (tfMinimizer_nonneg hΩ hc W)
    (tfMinimizer_nonneg hΩ hc) (tfMinimizer_min hΩ hc W) (tfMinimizer_min hΩ hc)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfExtendNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
include hΩ
omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfExtend_nonneg {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    ∀ᵐ x, 0 ≤ tfExtend Ω f x := by
  filter_upwards [(ae_restrict_iff' hΩ).mp hf] with x hx
  by_cases hs : x ∈ Ω
  · simpa only [tfExtend,Set.indicator_of_mem hs] using hx hs
  · simp [tfExtend,hs]
omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_restrict (f : TFLp (volume.restrict Ω)) (x : Space) :
    tfPotential f x = ∫ y in Ω, coulombKernel (x-y)*f y := by
  unfold tfPotential tfExtend
  rw [←integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Ω <;> simp [hy]
lemma tfPotential_restrict_integrable (f : TFLp (volume.restrict Ω)) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*f y) (volume.restrict Ω) := by
  apply (integrable_indicator_iff hΩ).mp
  apply (tfPotential_integrand hΩ f x).congr
  filter_upwards [] with y
  by_cases hy : y ∈ Ω <;> simp [tfExtend,hy]
lemma tfPotential_mass_lower {D : ℝ} (_hD : 0 < D)
    (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x-y‖ ≤ D) {f : TFLp (volume.restrict Ω)}
    (hf : TFNonneg f) {x : Space} (hx : x ∈ Ω) :
    (∫ y in Ω,f y)/D ≤ tfPotential f x := by
  rw [tfPotential_restrict hΩ,←integral_div]
  apply integral_mono_ae ((Lp.memLp f).integrable (by norm_num [TFExponent]) |>.div_const D)
    (tfPotential_restrict_integrable hΩ f x)
  filter_upwards [hf,ae_restrict_mem hΩ,(volume.restrict Ω).ae_ne x] with y hy hs hn
  have hk : 1/D ≤ coulombKernel (x-y) := by
    rw [coulombKernel,←one_div]
    apply one_div_le_one_div_of_le
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hn))
    · exact hd x hx y hs
  simpa only [div_eq_mul_inv,one_mul,mul_comm (D⁻¹) (f y)] using mul_le_mul_of_nonneg_right hk hy
omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfMass_nonneg {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    0 ≤ ∫ x in Ω,f x := integral_nonneg_of_ae hf
lemma tfCoulomb_mass_lower {D : ℝ} (hD : 0 < D)
    (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x-y‖ ≤ D) {f : TFLp (volume.restrict Ω)}
    (hf : TFNonneg f) :
    (∫ x in Ω,f x)^2/D ≤ tfCoulomb Ω f f := by
  rw [tfCoulomb_eq_potential hΩ]
  have hi : Integrable (fun x => f x*tfPotential f x) (volume.restrict Ω) := by
    apply (tfFieldPairing_integrable (tfPotentialField hΩ f) f).congr
    filter_upwards [tfPotentialField_coe hΩ f] with x hx
    rw [hx,mul_comm]
  calc
    _ = ∫ x in Ω,f x*((∫ y in Ω,f y)/D) := by rw [integral_mul_const]; ring
    _ ≤ _ := integral_mono_ae ((Lp.memLp f).integrable (by norm_num [TFExponent]) |>.mul_const _) hi
      (by
        filter_upwards [hf,ae_restrict_mem hΩ] with x hx hs
        exact mul_le_mul_of_nonneg_left (tfPotential_mass_lower hΩ hD hd hf hs) hx)
lemma tfEnergy_mass_lower {D c F : ℝ} (hD : 0 < D)
    (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x-y‖ ≤ D) (W : TFLq (volume.restrict Ω))
    (hF : ∀ᵐ x ∂volume.restrict Ω,W x ≤ F) {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    c*‖f‖^(5/3:ℝ)+(∫ x in Ω,f x)^2/(2*D)-F*(∫ x in Ω,f x) ≤ tfEnergy hΩ c W f := by
  have Hf : tfFieldContinuous W f ≤ F*(∫ x in Ω,f x) := by
    rw [tfFieldContinuous_apply,←integral_const_mul]
    apply integral_mono_ae (tfFieldPairing_integrable W f)
      ((Lp.memLp f).integrable (by norm_num [TFExponent]) |>.const_mul F)
    filter_upwards [hf,hF] with x hx hy
    exact mul_le_mul_of_nonneg_right hy hx
  have HB := tfCoulomb_mass_lower hΩ hD hd hf
  change _ ≤ c*‖f‖^(5/3:ℝ)-tfFieldContinuous W f+tfCoulomb Ω f f/2
  have he : (∫ x in Ω,f x)^2/(2*D) = ((∫ x in Ω,f x)^2/D)/2 := by ring
  rw [he]
  linarith
lemma tfEnergy_sublevel_mass_bound {D c F : ℝ} (hD : 0 < D) (hc : 0 < c) (hF0 : 0 ≤ F)
    (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x-y‖ ≤ D) (W : TFLq (volume.restrict Ω))
    (hF : ∀ᵐ x ∂volume.restrict Ω,W x ≤ F) {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (he : tfEnergy hΩ c W f ≤ 0) :
    (∫ x in Ω,f x) ≤ 2*D*F ∧ ‖f‖^(5/3:ℝ) ≤ D*F^2/(2*c) := by
  have H := tfEnergy_mass_lower hΩ (c := c) hD hd W hF hf
  have hm := tfMass_nonneg hf
  have hk := Real.rpow_nonneg (norm_nonneg f) (5/3:ℝ)
  have H1 : c*‖f‖^(5/3:ℝ)+(∫ x in Ω,f x)^2/(2*D)-F*(∫ x in Ω,f x) ≤ 0 := H.trans he
  have H2 : 2*D*c*‖f‖^(5/3:ℝ)+(∫ x in Ω,f x)^2-2*D*F*(∫ x in Ω,f x) ≤ 0 := by
    have H3 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2*D by positivity) H1
    field_simp at H3
    nlinarith
  refine ⟨?_,?_⟩
  · have Hkin : 0 ≤ 2*D*c*‖f‖^(5/3:ℝ) := by positivity
    by_contra! hn
    have hmpos : 0 < ∫ x in Ω,f x := (show 0 ≤ 2*D*F by positivity).trans_lt hn
    have Hp := mul_pos hmpos (sub_pos.mpr hn)
    nlinarith
  · apply (le_div_iff₀ (show 0<2*c by positivity)).mpr
    have Hsq := sq_nonneg ((∫ x in Ω,f x)-D*F)
    nlinarith
end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise
namespace Coulomb

lemma coulombBilinear_congr_ae {f f' g g' : Space → ℝ}
    (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    coulombBilinear f g = coulombBilinear f' g' := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp hf
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp hg
  unfold coulombBilinear
  rw [Measure.volume_eq_prod]
  apply integral_congr_ae
  filter_upwards [h1,h2] with xy hx hy
  simp only [Function.comp_def] at hx hy
  rw [hx,hy]

lemma rawThomasFermiEnergy_congr_ae (Φ : Space → ℝ) {f g : Space → ℝ}
    (h : f =ᵐ[volume] g) : rawThomasFermiEnergy Φ f = rawThomasFermiEnergy Φ g := by
  have h1 : (∫ x, f x^(5/3:ℝ)) = ∫ x, g x^(5/3:ℝ) :=
    integral_congr_ae (h.mono fun _ hx => congrArg (·^(5/3:ℝ)) hx)
  have h2 : (∫ x, Φ x*f x) = ∫ x, Φ x*g x :=
    integral_congr_ae (h.mono fun x hx => congrArg (Φ x*·) hx)
  simp only [rawThomasFermiEnergy, h1, h2, coulombBilinear_congr_ae h h]

lemma rawThomasFermiEnergy_tfExtend {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    rawThomasFermiEnergy Φ (tfExtend Ω f) = tfEnergy hΩ thomasFermiKineticConstant W f := by
  have hk : (∫ x, (tfExtend Ω f x)^(5/3:ℝ)) = ∫ x in Ω, (f x)^(5/3:ℝ) := by
    rw [← integral_indicator hΩ]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ω <;> simp [tfExtend,hx]
  have hw : (∫ x, Φ x*tfExtend Ω f x) = ∫ x in Ω, W x*f x := by
    calc
      _ = ∫ x in Ω, Φ x*f x := by
        rw [← integral_indicator hΩ]
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Ω <;> simp [tfExtend,hx]
      _ = _ := integral_congr_ae (hW.mono fun x hx => by rw [hx])
  rw [rawThomasFermiEnergy, hk, hw, tfEnergy_formula hΩ _ _ hf]
  rfl

def tfDensity (Ω : Set Space) (f : TFLp (volume.restrict Ω)) (x : Space) : ℝ :=
  max (tfExtend Ω f x) 0

lemma tfDensity_ae_tfExtend {Ω : Set Space} (hΩ : MeasurableSet Ω)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfDensity Ω f =ᵐ[volume] tfExtend Ω f :=
  (tfExtend_nonneg hΩ hf).mono fun _ hx => max_eq_left hx
lemma rawThomasFermiEnergy_tfDensity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    rawThomasFermiEnergy Φ (tfDensity Ω f) = tfEnergy hΩ thomasFermiKineticConstant W f := by
  rw [rawThomasFermiEnergy_congr_ae Φ (tfDensity_ae_tfExtend hΩ hf)]
  exact rawThomasFermiEnergy_tfExtend hΩ Φ W hW hf

lemma thomasFermiKineticConstant_pos : 0 < thomasFermiKineticConstant := by
  unfold thomasFermiKineticConstant
  positivity

def localTFMinimizer {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω)) : TFLp (volume.restrict Ω) :=
  tfMinimizer hΩ thomasFermiKineticConstant_pos W
lemma localTFMinimizer_nonneg {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω)) :
    TFNonneg (localTFMinimizer hΩ W) :=
  tfMinimizer_nonneg hΩ thomasFermiKineticConstant_pos W
lemma localTFMinimizer_minimizes {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfEnergy hΩ thomasFermiKineticConstant W (localTFMinimizer hΩ W) ≤
      tfEnergy hΩ thomasFermiKineticConstant W f :=
  tfMinimizer_min hΩ thomasFermiKineticConstant_pos W f hf

lemma continuous_localTFMinimizer {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] : Continuous (localTFMinimizer hΩ) :=
  tfMinimizer_continuous hΩ thomasFermiKineticConstant_pos

def localTFDensity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω)) : Space → ℝ :=
  tfDensity Ω (localTFMinimizer hΩ W)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoulombTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

def testCharge (χ : Space → ℝ) : Space → ℝ :=
  fun x => -(NeutralAtom.coordinateLaplacian χ x)/(4*Real.pi)

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_UniformBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma uniformBall_power_integrable (a M : ℝ) :
    Integrable (fun x => uniformBall a M x^(5/3:ℝ)) := by
  have he : (fun x => uniformBall a M x^(5/3:ℝ)) =
      (Metric.ball (0:Space) a).indicator (fun _ => (M/(4*Real.pi/3*a^3))^(5/3:ℝ)) := by
    funext x
    simp only [uniformBall,Set.indicator_apply]
    split <;> simp
  rw [he]
  exact (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const (C := (M/(4*Real.pi/3*a^3))^(5/3:ℝ)) measure_ball_lt_top.ne)

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FieldSubmean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma coreCoulombPotential_aestronglyMeasurable {k : ℕ} (u : H1Vector k) :
    AEStronglyMeasurable (coreCoulombPotential u) volume := by
  unfold coreCoulombPotential
  apply Finset.aestronglyMeasurable_fun_sum
  intro s hs
  apply Finset.aestronglyMeasurable_fun_sum
  intro i hi
  have hK : AEStronglyMeasurable (fun z : Configuration k × Space =>
      coulombKernel (position z.1 i-z.2)) (volume.prod volume) :=
    (((continuous_position i).measurable.comp measurable_fst).sub measurable_snd).norm.inv.aestronglyMeasurable
  exact (hK.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2).comp_fst).prod_swap.integral_prod_right'

lemma attraction_le_totalCharge_div {J : ℕ} (S : Nuclei J) {a : ℝ} (ha : 0 < a)
    (x : Space) (hsep : ∀ j, a ≤ ‖x-S.position j‖) : attraction S x ≤ totalCharge S/a := by
  unfold attraction totalCharge
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  have hK : coulombKernel (x-S.position j) ≤ 1/a := by
    simpa only [coulombKernel,one_div] using one_div_le_one_div_of_le ha (hsep j)
  exact (mul_le_mul_of_nonneg_left hK (le_trans zero_le_one (S.charge_ge_one j))).trans_eq (by ring)

lemma ballCloud_nested_le {a : ℝ} (ha : 0 < a) (z w x : Space) (hw : ‖w-z‖ ≤ a) :
    ballCloud w a 1 x ≤ 8*ballCloud z (2*a) 1 x := by
  by_cases hx : x-w ∈ Metric.ball (0:Space) a
  · have hh : ‖x-w‖ < a := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hxz : x-z ∈ Metric.ball (0:Space) (2*a) := by
      simp only [Metric.mem_ball,dist_zero_right]
      have ht : ‖x-z‖ ≤ ‖x-w‖+‖w-z‖ := by simpa only [dist_eq_norm] using dist_triangle x w z
      linarith
    simp only [ballCloud,uniformBall,indicator_of_mem hx,indicator_of_mem hxz]
    have he : 1/(4*Real.pi/3*a^3) = 8*(1/(4*Real.pi/3*(2*a)^3)) := by ring
    exact he.le
  · simp only [ballCloud,uniformBall,indicator_of_notMem hx]
    exact mul_nonneg (by norm_num) (uniformBall_nonneg (by linarith) zero_le_one (x-z))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RestrictedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def restrictedCorePotential {k : ℕ} (u : H1Vector k) (A : Set Space) (y : Space) : ℝ :=
  ∑ s : Spins k, ∑ i : Fin k, ∫ x : Configuration k,
    if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2 else 0

lemma restrictedCore_integrable {k : ℕ} (u : H1Vector k) {A : Set Space}
    (hA : MeasurableSet A) (s : Spins k) (i : Fin k) (y : Space) :
    Integrable (fun x => if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2 else 0) := by
  exact ((u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1).indicator
    (hA.preimage (continuous_position i).measurable)

lemma restrictedCorePotential_nonneg {k : ℕ} (u : H1Vector k) (A : Set Space) (y : Space) :
    0 ≤ restrictedCorePotential u A y := by
  apply Finset.sum_nonneg
  intro s hs
  apply Finset.sum_nonneg
  intro i hi
  apply integral_nonneg
  intro x
  dsimp only [Pi.zero_apply]
  split_ifs <;> first | exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _) | exact le_rfl

lemma restrictedCorePotential_le {k : ℕ} (u : H1Vector k) {A : Set Space}
    (hA : MeasurableSet A) (y : Space) : restrictedCorePotential u A y ≤ coreCoulombPotential u y := by
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro i hi
  apply integral_mono (restrictedCore_integrable u hA s i y)
    (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1
  intro x
  dsimp only [Pi.zero_apply]
  split_ifs <;> first | exact le_rfl | exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _)

lemma restrictedCorePotential_mono {k : ℕ} (u : H1Vector k) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) (y : Space) :
    restrictedCorePotential u A y ≤ restrictedCorePotential u B y := by
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro i hi
  apply integral_mono (restrictedCore_integrable u hA s i y) (restrictedCore_integrable u hB s i y)
  intro x
  by_cases h : position x i ∈ A
  · simp [h,hAB h]
  · simp only [ite_eq_right h]
    split_ifs <;> first | exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _) | exact le_rfl

lemma restrictedCorePotential_eq {k : ℕ} (u : H1Vector k) {A : Set Space}
    (hu : SpatiallySupported u A) (y : Space) : restrictedCorePotential u A y=coreCoulombPotential u y := by
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases h : position x i ∈ A
  · simp [h]
  · have hz : u.value s x=0 := hx (fun hh => h (hh i))
    simp [h,hz]

lemma restrictedCorePotential_aestronglyMeasurable {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) : AEStronglyMeasurable (restrictedCorePotential u A) volume := by
  unfold restrictedCorePotential
  apply Finset.aestronglyMeasurable_fun_sum
  intro s hs
  apply Finset.aestronglyMeasurable_fun_sum
  intro i hi
  have hK : AEStronglyMeasurable (fun z : Configuration k × Space =>
      coulombKernel (position z.1 i-z.2)*‖u.value s z.1‖^2) (volume.prod volume) :=
    ((((continuous_position i).measurable.comp measurable_fst).sub measurable_snd).norm.inv.aestronglyMeasurable).mul
      ((u.value_L2 s).aestronglyMeasurable.norm.pow 2).comp_fst
  have H := hK.indicator (hA.preimage ((continuous_position i).measurable.comp measurable_fst))
  exact H.prod_swap.integral_prod_right'

lemma restrictedCore_density_prod_integrable {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) (s : Spins k) (i : Fin k)
    (d : Space → ℝ) (hd : Integrable d) :
    Integrable (fun z : Configuration k × Space =>
      if position z.1 i ∈ A then coulombKernel (position z.1 i-z.2)*‖u.value s z.1‖^2*d z.2 else 0)
      (volume.prod volume) := by
  exact (u.coulomb_density_prod_integrable s i d hd).indicator
    (hA.preimage ((continuous_position i).measurable.comp measurable_fst))

lemma restrictedCorePotential_mul_integrable {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) (d : Space → ℝ) (hd : Integrable d) :
    Integrable (fun y => restrictedCorePotential u A y*d y) := by
  simp only [restrictedCorePotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro s hs
  apply integrable_finsetSum
  intro i hi
  have H := (restrictedCore_density_prod_integrable u hA s i d hd).integral_prod_right
  apply H.congr
  filter_upwards [] with y
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  split_ifs <;> simp

lemma restrictedCorePotential_fubini {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) (d : Space → ℝ) (hd : Integrable d) :
    (∫ y, restrictedCorePotential u A y*d y)=
      ∑ s : Spins k, ∑ i : Fin k, ∫ x,
        if position x i ∈ A then (∫ y, coulombKernel (position x i-y)*d y)*‖u.value s x‖^2 else 0 := by
  have H (s : Spins k) (i : Fin k) := restrictedCore_density_prod_integrable u hA s i d hd
  have hi (s : Spins k) (i : Fin k) :
      Integrable (fun y => (∫ x, if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2 else 0)*d y) := by
    apply (H s i).integral_prod_right.congr
    filter_upwards [] with y
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    split_ifs <;> simp
  simp only [restrictedCorePotential,Finset.sum_mul]
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hi s i))]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_finsetSum _ (fun i _ => hi s i)]
  apply Finset.sum_congr rfl
  intro i hi'
  calc
    _ = ∫ y, ∫ x, if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2*d y else 0 := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      split_ifs <;> simp
    _ = ∫ x, ∫ y, if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2*d y else 0 :=
      (integral_integral_swap (H s i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases h : position x i ∈ A
      · simp only [ite_eq_left h,← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      · simp [h]

lemma restrictedCorePotential_ballCloud {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hsep : ∀ z ∈ A, a ≤ ‖z-y‖) :
    (∫ z, restrictedCorePotential u A z*ballCloud y a M z)=M*restrictedCorePotential u A y := by
  rw [restrictedCorePotential_fubini u hA _ (ballCloud_integrable a M y)]
  simp only [restrictedCorePotential,Finset.mul_sum,← integral_const_mul]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases h : position x i ∈ A
  · rw [ite_eq_left h,ite_eq_left h,ballCloud_coulomb ha hM y (position x i) (hsep _ h)]
    ring
  · simp [h]

lemma restrictedOutPotential_nonneg {m : ℕ} (x : Configuration m) (A : Set Space) (y : Space) :
    0 ≤ restrictedOutPotential x A y := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact le_rfl

lemma restrictedOutPotential_mono {m : ℕ} (x : Configuration m) {A B : Set Space}
    (hAB : A ⊆ B) (y : Space) : restrictedOutPotential x A y ≤ restrictedOutPotential x B y := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : position x i ∈ A
  · simp [h,hAB h]
  · simp only [ite_eq_right h]
    split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact le_rfl

def recordedFarField {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (A : Set Space) (y : Space) : ℝ :=
  attraction S y-restrictedCorePotential u A y-restrictedOutPotential x A y

lemma recordedFarField_le_attraction {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (A : Set Space) (y : Space) : recordedFarField S u x A y ≤ attraction S y := by
  unfold recordedFarField
  linarith [restrictedCorePotential_nonneg u A y,restrictedOutPotential_nonneg x A y]

lemma recordedFarField_anti {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A B : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (y : Space) : recordedFarField S u x B y ≤ recordedFarField S u x A y := by
  unfold recordedFarField
  linarith [restrictedCorePotential_mono u hA hB hAB y,restrictedOutPotential_mono x hAB y]

lemma coreField_le_far_addback {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) (y : Space) :
    coreScreenedField S u y ≤ recordedFarField S u x A y+restrictedOutPotential x A y := by
  unfold coreScreenedField recordedFarField
  linarith [restrictedCorePotential_le u hA y]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FarSubmean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma restrictedOutPotential_measurable {m : ℕ} (x : Configuration m) (A : Set Space) :
    Measurable (restrictedOutPotential x A) := by
  apply Finset.measurable_fun_sum
  intro i hi
  by_cases h : position x i ∈ A
  · simp only [ite_eq_left h, coulombKernel]
    fun_prop
  · simp only [ite_eq_right h]
    exact measurable_const

lemma restrictedOutPotential_ballCloud_integrable {m : ℕ} (x : Configuration m) (A : Set Space)
    {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => restrictedOutPotential x A z*ballCloud y a 1 z) := by
  simp only [restrictedOutPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i hi
  by_cases h : position x i ∈ A
  · simpa only [ite_eq_left h] using coulomb_convolution_integrable (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (fun z => uniformBall_nonneg ha zero_le_one (z-y))
      (fun z => uniformBall_le ha zero_le_one (z-y)) ha (position x i)
  · simp only [ite_eq_right h,zero_mul]
    exact integrable_zero _ _ _

lemma restrictedOutPotential_ballCloud {m : ℕ} (x : Configuration m) (A : Set Space)
    {a : ℝ} (ha : 0 < a) (y : Space) (hsep : ∀ v ∈ A, a ≤ ‖v-y‖) :
    (∫ z, restrictedOutPotential x A z*ballCloud y a 1 z)=restrictedOutPotential x A y := by
  have hi (i : Fin m) : Integrable (fun z =>
      (if position x i ∈ A then coulombKernel (position x i-z) else 0)*ballCloud y a 1 z) := by
    by_cases h : position x i ∈ A
    · simpa only [ite_eq_left h] using coulomb_convolution_integrable (ballCloud_integrable a 1 y)
        (ballCloud_measurable a 1 y) (fun z => uniformBall_nonneg ha zero_le_one (z-y))
        (fun z => uniformBall_le ha zero_le_one (z-y)) ha (position x i)
    · simp only [ite_eq_right h,zero_mul]
      exact integrable_zero _ _ _
  unfold restrictedOutPotential
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi'
  by_cases h : position x i ∈ A
  · simp only [ite_eq_left h]
    simpa only [one_mul] using ballCloud_coulomb ha zero_le_one y (position x i) (hsep _ h)
  · simp [h]

lemma attraction_ballCloud_integrable {J : ℕ} (S : Nuclei J) {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => attraction S z*ballCloud y a 1 z) := by
  simp only [attraction,Finset.sum_mul]
  apply integrable_finsetSum
  intro j hj
  have H := (coulomb_convolution_integrable (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y)
    (fun z => uniformBall_nonneg ha zero_le_one (z-y))
    (fun z => uniformBall_le ha zero_le_one (z-y)) ha (S.position j)).const_mul (S.charge j)
  exact H.congr (Eventually.of_forall (fun z => by dsimp only; rw [coulombKernel_sub_comm]; ring))

lemma recordedFarField_ballCloud_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => recordedFarField S u x A z*ballCloud y a 1 z) := by
  apply (((attraction_ballCloud_integrable S ha y).sub
    (restrictedCorePotential_mul_integrable u hA _ (ballCloud_integrable a 1 y))).sub
    (restrictedOutPotential_ballCloud_integrable x A ha y)).congr
  exact Eventually.of_forall (fun z => by dsimp only [Pi.sub_apply,recordedFarField]; ring)

lemma recordedFarField_ballCloud {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) {a : ℝ} (ha : 0 < a) (y : Space)
    (hcore : ∀ z ∈ A, a ≤ ‖z-y‖) (hnuc : ∀ j, a ≤ ‖S.position j-y‖) :
    (∫ z, recordedFarField S u x A z*ballCloud y a 1 z)=recordedFarField S u x A y := by
  simp only [recordedFarField,sub_mul]
  have hsub : Integrable (fun z => attraction S z*ballCloud y a 1 z-
      restrictedCorePotential u A z*ballCloud y a 1 z) := by
    exact (attraction_ballCloud_integrable S ha y).sub
      (restrictedCorePotential_mul_integrable u hA _ (ballCloud_integrable a 1 y))
  rw [integral_sub hsub (restrictedOutPotential_ballCloud_integrable x A ha y),
    integral_sub (attraction_ballCloud_integrable S ha y)
      (restrictedCorePotential_mul_integrable u hA _ (ballCloud_integrable a 1 y)),
    attraction_ballCloud S ha zero_le_one y hnuc,
    restrictedCorePotential_ballCloud u hA ha zero_le_one y hcore,
    restrictedOutPotential_ballCloud x A ha y hcore,one_mul,one_mul]

lemma positive_ballCloud_integrable {a : ℝ} (ha : 0 < a) (y : Space) (f : Space → ℝ)
    (hf : Integrable (fun z => f z*ballCloud y a 1 z)) :
    Integrable (fun z => max (f z) 0*ballCloud y a 1 z) := by
  apply (hf.sup (integrable_zero _ _ _)).congr
  filter_upwards [] with z
  change max (f z*ballCloud y a 1 z) 0 = _
  symm
  simpa only [zero_mul, ballCloud] using max_mul_of_nonneg (f z) 0 (uniformBall_nonneg ha zero_le_one (z-y))

lemma positive_square_ballCloud_integrable {J : ℕ} (S : Nuclei J) (f : Space → ℝ)
    (hm : AEStronglyMeasurable f volume) (hbound : ∀ z, f z ≤ attraction S z)
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    Integrable (fun z => (max (f z) 0)^2*ballCloud y a 1 z) := by
  have hp : AEStronglyMeasurable (fun z => (max (f z) 0)^2) volume :=
    (hm.sup aestronglyMeasurable_const).pow 2
  apply ((ballCloud_integrable a 1 y).const_mul ((totalCharge S/a)^2)).mono'
    (hp.mul (ballCloud_measurable a 1 y).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖(max (f z) 0)^2*ballCloud y a 1 z‖ ≤ _
  have hball : 0 ≤ ballCloud y a 1 z := uniformBall_nonneg ha zero_le_one (z-y)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hball)]
  by_cases hz : z-y ∈ Metric.ball (0:Space) a
  · have hdist : ‖z-y‖ < a := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have hsep (j : Fin J) : a ≤ ‖z-S.position j‖ := by
      have ht : ‖S.position j-y‖ ≤ ‖S.position j-z‖+‖z-y‖ := by
        simpa only [dist_eq_norm] using dist_triangle (S.position j) z y
      rw [norm_sub_rev (S.position j) z] at ht
      linarith [hnuc j]
    have hP : max (f z) 0 ≤ totalCharge S/a :=
      (max_le (hbound z) (attraction_nonneg S z)).trans (attraction_le_totalCharge_div S ha z hsep)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_right _ _) hP 2)
      (uniformBall_nonneg ha zero_le_one (z-y))
  · simp only [ballCloud,uniformBall,indicator_of_notMem hz,mul_zero,le_refl]

lemma restrictedOutPotential_le {m : ℕ} (x : Configuration m) (A : Set Space)
    {r : ℝ} (hr : 0 < r) (y : Space) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) :
    restrictedOutPotential x A y ≤ (m:ℝ)/r := by
  calc
    _ ≤ ∑ _i : Fin m, 1/r := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : position x i ∈ A
      · simp only [ite_eq_left h, coulombKernel]
        simpa only [one_div] using one_div_le_one_div_of_le hr (hsep _ h)
      · simp only [ite_eq_right h]
        positivity
    _ = _ := by simp; ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_CutCombinatorics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma mass_labelCut {n : ℕ} {L : Type*} [Fintype L] (ψ : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D) :
    ∑ p : Fin n → L, mass (ψ.labelCut χ hχ hp D hD hd p) = mass ψ :=
  mass_smooth_partition ψ _ (tensorCut_contDiff χ hχ) 1 D (tensorCut_abs_le_one χ hp)
    (tensorCut_partial_bound χ hχ hp hD hd) (tensorCut_partition χ hp)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_ScaledWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma space_integral_inv_smul (f : Space → ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ x, f (a⁻¹ • x)) = a^3*(∫ x, f x) := by
  rw [Measure.integral_comp_smul_of_nonneg volume f a⁻¹ (hR := inv_nonneg.mpr ha.le)]
  simp [finrank_euclideanSpace, smul_eq_mul]

lemma scaledWindow_mass (g : 𝓢(Space,ℝ)) {a : ℝ} (ha : 0 < a) :
    (∫ x : Space, scaledWindow g a ha.ne' x^2) = ∫ x : Space, g x^2 := by
  simp only [scaledWindow_apply,mul_pow,inv_pow]
  rw [Real.sq_sqrt (by positivity), integral_const_mul,space_integral_inv_smul (fun x => g x^2) ha]
  field_simp

lemma scaledWindow_fderiv (g : 𝓢(Space,ℝ)) {a : ℝ} (ha : 0 < a) (x v : Space) :
    fderiv ℝ (scaledWindow g a ha.ne') x v =
      (Real.sqrt (a^3))⁻¹*a⁻¹*(fderiv ℝ g (a⁻¹ • x) v) := by
  have hd := (g.differentiableAt (x := a⁻¹ • x)).hasFDerivAt.comp x
    ((a⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt)
  have H := (hd.const_mul (Real.sqrt (a^3))⁻¹).fderiv
  change fderiv ℝ (fun z => (Real.sqrt (a^3))⁻¹*g (a⁻¹ • z)) x v = _
  simp only [Function.comp_def] at H
  rw [H]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.map_smul,smul_eq_mul]
  ring

lemma scaledWindow_kinetic (g : 𝓢(Space,ℝ)) {a : ℝ} (ha : 0 < a) :
    (∑ b : Fin 3, ∫ x : Space, (fderiv ℝ (scaledWindow g a ha.ne') x (EuclideanSpace.single b 1))^2) =
      (∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2)/a^2 := by
  simp only [scaledWindow_fderiv g ha,mul_pow,inv_pow]
  rw [Real.sq_sqrt (by positivity)]
  simp_rw [integral_const_mul]
  have hi (b : Fin 3) := space_integral_inv_smul
    (fun x => (fderiv ℝ g x (EuclideanSpace.single b 1))^2) ha
  simp_rw [hi, ←mul_assoc]
  rw [←Finset.mul_sum]
  field_simp

lemma scaledWindow_support (g : 𝓢(Space,ℝ)) (hgs : ∀ z, 1 < ‖z‖ → g z = 0)
    {a : ℝ} (ha : 0 < a) (x : Space) (hx : a < ‖x‖) :
    scaledWindow g a ha.ne' x = 0 := by
  rw [scaledWindow_apply,hgs,mul_zero]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
  exact (one_lt_inv_mul₀ ha).2 hx

lemma scaledWindow_compactSupport (g : 𝓢(Space,ℝ))
    (hgs : ∀ z, 1 < ‖z‖ → g z = 0) {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (scaledWindow g a ha.ne' : Space → ℝ) := by
  apply HasCompactSupport.intro (K := Metric.closedBall 0 a) (isCompact_closedBall 0 a)
  intro x hx
  exact scaledWindow_support g hgs ha x (by simpa [Metric.mem_closedBall] using hx)

lemma scaledWindow_radial (g : 𝓢(Space,ℝ))
    (hrad : ∀ z, g z = g (EuclideanSpace.single 0 ‖z‖)) {a : ℝ} (ha : 0 < a) (x : Space) :
    scaledWindow g a ha.ne' x = scaledWindow g a ha.ne' (EuclideanSpace.single 0 ‖x‖) := by
  simp only [scaledWindow_apply]
  congr 1
  rw [hrad (a⁻¹ • x)]
  congr 1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
  symm
  ext i
  simp only [PiLp.smul_apply,PiLp.single_apply,smul_eq_mul]
  split <;> simp_all

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise ContDiff
namespace Coulomb

lemma windowSeed_mass_pos : 0 < ∫ x : Space, windowSeed x^2 := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (windowSeed_smooth.continuous.pow 2)
    ((windowSeed_smooth.continuous.pow 2).integrable_of_hasCompactSupport (by simpa only [pow_two] using (windowSeed_compact.mul_left (f := windowSeed))))
    (fun x => sq_nonneg _) (x := 0)
  norm_num [windowSeed, Real.smoothTransition.one_of_one_le]

lemma unitWindow_apply (x : Space) : unitWindow x =
    (Real.sqrt (∫ z : Space, windowSeed z^2))⁻¹*windowSeed x := rfl

lemma unitWindow_mass : (∫ x : Space, unitWindow x^2) = 1 := by
  simp only [unitWindow_apply,mul_pow,inv_pow]
  rw [Real.sq_sqrt windowSeed_mass_pos.le,integral_const_mul,inv_mul_cancel₀ windowSeed_mass_pos.ne']

lemma unitWindow_support (x : Space) (hx : 1 < ‖x‖) : unitWindow x = 0 := by
  rw [unitWindow_apply,windowSeed_support x hx.le,mul_zero]

lemma unitWindow_radial (x : Space) : unitWindow x = unitWindow (EuclideanSpace.single 0 ‖x‖) := by
  simp [unitWindow_apply,windowSeed,PiLp.norm_single]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma restrictedOutPotential_measurable_configuration {n : ℕ} {A : Set Space}
    (hA : MeasurableSet A) (y : Space) : Measurable (fun x : Configuration n => restrictedOutPotential x A y) := by
  apply Finset.measurable_fun_sum
  intro i hi
  apply Measurable.ite (hA.preimage (continuous_position i).measurable) _ measurable_const
  simp only [coulombKernel]
  have hm : Measurable (fun x : Configuration n => position x i) := (continuous_position i).measurable
  fun_prop

lemma rawSignedField_measurable {n : ℕ} (V : ℝ) {A : Set Space} (hA : MeasurableSet A) (y : Space) :
    Measurable (rawSignedField (n:=n) V A y) :=
  measurable_const.sub (restrictedOutPotential_measurable_configuration hA y)

lemma rawSignedField_abs_le {n : ℕ} (V : ℝ) (A : Set Space) (y : Space)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) (x : Configuration n) :
    |rawSignedField V A y x| ≤ |V|+(n:ℝ)/r := by
  have H := restrictedOutPotential_le x A hr y hsep
  have H0 := restrictedOutPotential_nonneg x A y
  unfold rawSignedField
  calc
    _ ≤ |V|+|restrictedOutPotential x A y| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg H0]; linarith

lemma potentialForm_restrictedOutPotential {n : ℕ} (u : H1Vector n) {A : Set Space}
    (hA : MeasurableSet A) (y : Space) :
    potentialForm (fun x => restrictedOutPotential x A y) u=restrictedCorePotential u A y := by
  apply Finset.sum_congr rfl
  intro s hs
  unfold restrictedOutPotential
  simp only [Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only; split_ifs <;> simp)
  · intro i hi
    exact (restrictedCore_integrable u hA s i y).congr (Eventually.of_forall (fun x => by dsimp only; split_ifs <;> simp))

lemma potentialForm_rawSignedField {n : ℕ} (u : H1Vector n) (V : ℝ) {A : Set Space}
    (hA : MeasurableSet A) (y : Space) {r : ℝ} (hr : 0 < r) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) :
    potentialForm (rawSignedField V A y) u=V*mass u-restrictedCorePotential u A y := by
  rw [←potentialForm_const,←potentialForm_restrictedOutPotential u hA y]
  unfold potentialForm rawSignedField
  simp only [sub_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_sub]
  · exact ((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul V
  · exact boundedObservable_integrable u _ (restrictedOutPotential_measurable_configuration hA y)
      (fun x => by rw [abs_of_nonneg (restrictedOutPotential_nonneg x A y)]; exact restrictedOutPotential_le x A hr y hsep) s

lemma potentialForm_labelCut {n : ℕ} {L : Type*} [Fintype L] (u : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (W : Configuration n → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) :
    (∑ p : Fin n → L, potentialForm W (u.labelCut χ hχ hp D hD hd p))=potentialForm W u := by
  unfold potentialForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  exact potential_smooth_partition u _ (tensorCut_contDiff χ hχ) 1 D (tensorCut_abs_le_one χ hp)
    (tensorCut_partial_bound χ hχ hp hD hd) (tensorCut_partition χ hp) W s
    (fun p => boundedObservable_integrable (u.labelCut χ hχ hp D hD hd p) W hW hB s)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_RadialCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff
namespace Coulomb

lemma cutSeed_one (x : Space) (hx : ‖x‖ ≤ 1) : cutSeed x=1 := by
  apply Real.smoothTransition.one_of_one_le
  nlinarith [norm_nonneg x]
lemma radialCut_core_zero (y : Space) {r : ℝ} (hr : 0 < r) (x : Space) (hx : ‖x-y‖ ≤ r) :
    radialCut y r 1 x=0 := by
  have hs : ‖r⁻¹ • (x-y)‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).2 hx
  simp [radialCut,cutAngle,cutSeed_one _ hs,Real.cos_pi_div_two]
lemma radialCut_out_zero (y : Space) {r : ℝ} (hr : 0 < r) (x : Space) (hx : 2*r ≤ ‖x-y‖) :
    radialCut y r 0 x=0 := by
  have hs : 2 ≤ ‖r⁻¹ • (x-y)‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (le_inv_mul_iff₀ hr).2 (by simpa only [mul_comm] using hx)
  simp [radialCut,cutAngle,cutSeed_zero _ hs]

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CountMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma localCount_weight_integrable {n : ℕ} (ψ : H1Vector n) {A : Set Space}
    (hA : MeasurableSet A) (s : Spins n) (q : ℕ) :
    Integrable (fun x => (localCount A x)^q*‖ψ.value s x‖^2) := by
  have hw := (ψ.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)
  apply (hw.const_mul ((n:ℝ)^q)).mono'
    (((localCount_measurable hA).pow_const q).aestronglyMeasurable.mul hw.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(localCount A x)^q*‖ψ.value s x‖^2‖ ≤ (n:ℝ)^q*‖ψ.value s x‖^2
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (localCount_nonneg A x) _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (localCount_nonneg A x) (localCount_le A x) q) (sq_nonneg _)

def localCountSecondMoment {n : ℕ} (ψ : H1Vector n) (A : Set Space) : ℝ :=
  ∑ s : Spins n, ∫ x, (localCount A x)^2*‖ψ.value s x‖^2

lemma localCountSecondMoment_nonneg {n : ℕ} (ψ : H1Vector n) (A : Set Space) :
    0 ≤ localCountSecondMoment ψ A :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

lemma localCountSecondMoment_le {n : ℕ} (ψ : H1Vector n) (A : Set Space) :
    localCountSecondMoment ψ A ≤ (n:ℝ)^2*mass ψ := by
  unfold localCountSecondMoment mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [] with x
    positivity
  · exact ((ψ.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul _
  · filter_upwards [] with x
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (localCount_nonneg A x) (localCount_le A x) 2) (sq_nonneg _)

lemma expectedPopulation_sq_le {n : ℕ} (ψ : H1Vector n) {A : Set Space}
    (hA : MeasurableSet A) (hmass : mass ψ=1) :
    (expectedPopulation ψ A)^2 ≤ localCountSecondMoment ψ A := by
  let c := expectedPopulation ψ A
  have hn : 0 ≤ ∑ s : Spins n, ∫ x, (localCount A x-c)^2*‖ψ.value s x‖^2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hi (s : Spins n) :
      (∫ x, (localCount A x-c)^2*‖ψ.value s x‖^2) =
      (∫ x, (localCount A x)^2*‖ψ.value s x‖^2)-2*c*(∫ x, localCount A x*‖ψ.value s x‖^2)+
      c^2*(∫ x, ‖ψ.value s x‖^2) := by
    have h1 : Integrable (fun x => localCount A x*‖ψ.value s x‖^2) := by
      simpa using localCount_weight_integrable ψ hA s 1
    have h2 := localCount_weight_integrable ψ hA s 2
    have h0 := (ψ.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)
    have hsub : Integrable (fun x => (localCount A x)^2*‖ψ.value s x‖^2-(2*c)*(localCount A x*‖ψ.value s x‖^2)) := by
      exact h2.sub (h1.const_mul (2*c))
    calc
      _ = ∫ x, ((localCount A x)^2*‖ψ.value s x‖^2-(2*c)*(localCount A x*‖ψ.value s x‖^2))+c^2*‖ψ.value s x‖^2 :=
        integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = _ := by
        rw [integral_add hsub (h0.const_mul _),integral_sub h2 (h1.const_mul _),
          integral_const_mul,integral_const_mul]
  simp only [hi,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hn
  rw [← expectedPopulation_eq ψ hA] at hn
  change 0 ≤ localCountSecondMoment ψ A-2*c*expectedPopulation ψ A+c^2*mass ψ at hn
  rw [hmass] at hn
  dsimp [c] at hn
  nlinarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SortedObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma restrictedOutPotential_reindex {m n : ℕ} (e : Fin m ≃ Fin n)
    (x : Configuration m) (A : Set Space) (y : Space) :
    restrictedOutPotential (reindexConfiguration e x) A y=restrictedOutPotential x A y := by
  change (∑ i : Fin n, if position x (e.symm i) ∈ A then coulombKernel (position x (e.symm i)-y) else 0)=_
  exact Equiv.sum_comp e.symm (fun i => if position x i ∈ A then coulombKernel (position x i-y) else 0)

lemma rawSignedField_reindex {m n : ℕ} (e : Fin m ≃ Fin n)
    (V : ℝ) (A : Set Space) (y : Space) (x : Configuration m) :
    rawSignedField V A y (reindexConfiguration e x)=rawSignedField V A y x := by
  simp only [rawSignedField,restrictedOutPotential_reindex]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_AppendJensen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma mass_appendCut {m n : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) :
    mass (u.appendCut χ hχ hp D hD hd p e)=mass (u.labelCut χ hχ hp D hD hd p) := by
  simp only [H1Vector.appendCut,mass_reindex]

lemma potentialForm_appendCut {m n : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n)
    (W : Configuration (m+n) → ℝ) :
    potentialForm (W ∘ reindexConfiguration (coreReindex m e) ∘ reindexConfiguration (recordAssoc m q k))
      (u.appendCut χ hχ hp D hD hd p e)=potentialForm W (u.labelCut χ hχ hp D hD hd p) := by
  change potentialForm ((W ∘ reindexConfiguration (coreReindex m e)) ∘ reindexConfiguration (recordAssoc m q k))
    (((u.labelCut χ hχ hp D hD hd p).reindex (coreReindex m e)).reindex (recordAssoc m q k))=_
  rw [potentialForm_reindex,potentialForm_reindex]

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_H1VectorL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff BigOperators
noncomputable section
namespace Coulomb
namespace H1Vector
variable {n:ℕ}
def valueL2 (u:H1Vector n) (s:Spins n) : Lp ℂ 2 (volume:Measure (Configuration n)) :=
  (u.value_L2 s).toLp (u.value s)
def gradientL2 (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3) : Lp ℂ 2 (volume:Measure (Configuration n)) :=
  (u.partial_L2 s a).toLp (u.gradient s a)
lemma valueL2_ae (u:H1Vector n) (s:Spins n) : (u.valueL2 s:Configuration n → ℂ)=ᵐ[volume]u.value s :=
  (u.value_L2 s).coeFn_toLp

def ofL2 (v:Spins n → Lp ℂ 2 (volume:Measure (Configuration n)))
    (g:Spins n → (Fin n × Fin 3) → Lp ℂ 2 (volume:Measure (Configuration n)))
    (hw:∀ s a (φ:Configuration n → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ)*v s x)=-(∫ x,(φ x:ℂ)*g s a x)) : H1Vector n where
  value:=fun s => v s
  gradient:=fun s a => g s a
  value_L2:=fun s => Lp.memLp (v s)
  partial_L2:=fun s a => Lp.memLp (g s a)
  weak_partial:=by
    intro s a φ hφ hc
    simpa only [mul_comm] using hw s a φ hφ hc
end H1Vector

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L2MultiplierContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate BigOperators
noncomputable section
namespace Coulomb
variable {n:ℕ}
lemma H1Vector.hardy_multiplier_memLp (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i) :
    MemLp (fun x => (hardyCoulomb i R x:ℂ)*u.valueL2 s x) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (((measurable_hardyCoulomb i R).complex_ofReal.aestronglyMeasurable).mul
      (Lp.memLp (u.valueL2 s)).aestronglyMeasurable)).mpr
  apply (u.hardy s i R).1.congr
  filter_upwards [u.valueL2_ae s] with x hx
  change (blockRadiusSq i R x)⁻¹*‖u.value s x‖^2 = ‖(hardyCoulomb i R x:ℂ)*u.valueL2 s x‖^2
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,hardyCoulomb_sq,hx]

def H1Vector.hardyMultiplier (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i) :
    Lp ℂ 2 (volume:Measure (Configuration n)) :=
  (u.hardy_multiplier_memLp s i R).toLp _
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_JointSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma potentialForm_coreSlice_joint_aestronglyMeasurable {m k : ℕ}
    (ψ : H1Vector (m+k)) (s : Spins m)
    (W : (Configuration m × Space) × Configuration k → ℝ) (hW : Measurable W) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      potentialForm (fun v => W (z,v)) (ψ.coreSlice s z.1)) (volume.prod volume) := by
  have hreg : ∀ᵐ z : Configuration m × Space ∂volume.prod volume, ψ.CoreSliceRegular s z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ψ.coreSliceRegular_ae s)
  apply AEStronglyMeasurable.congr _
    (show (fun z : Configuration m × Space => ∑ t : Spins k, ∫ v,
        W (z,v)*‖ψ.value (Fin.append s t) (joinConfiguration m k (z.1,v))‖^2) =ᵐ[volume.prod volume]
        (fun z => potentialForm (fun v => W (z,v)) (ψ.coreSlice s z.1)) from ?_)
  · apply Finset.aestronglyMeasurable_fun_sum
    intro t ht
    have hψ := ((ψ.value_L2 (Fin.append s t)).aestronglyMeasurable.comp_measurePreserving
      (joinConfiguration_measurePreserving m k)).norm.pow 2
    have hp : MeasurePreserving (fun z : (Configuration m × Space) × Configuration k =>
        ((z.1.1,z.2),z.1.2)) ((volume.prod volume).prod volume) ((volume.prod volume).prod volume) := by
      have h1 := measurePreserving_prodAssoc (volume : Measure (Configuration m))
        (volume : Measure Space) (volume : Measure (Configuration k))
      have h2 := (MeasurePreserving.id (volume : Measure (Configuration m))).prod
        (Measure.measurePreserving_swap (μ := (volume : Measure Space)) (ν := (volume : Measure (Configuration k))))
      have h3 := (measurePreserving_prodAssoc (volume : Measure (Configuration m))
        (volume : Measure (Configuration k)) (volume : Measure Space)).symm MeasurableEquiv.prodAssoc
      exact h3.comp (h2.comp h1)
    have hl := (hψ.comp_fst (ν := (volume : Measure Space))).comp_measurePreserving hp
    exact (hW.aestronglyMeasurable.mul hl).integral_prod_right'
  · filter_upwards [hreg] with z hz
    simp only [potentialForm, ψ.coreSlice_value s hz]

lemma potentialForm_normalized_coreSlice_joint_aestronglyMeasurable {m k : ℕ}
    (ψ : H1Vector (m+k)) (s : Spins m)
    (W : (Configuration m × Space) × Configuration k → ℝ) (hW : Measurable W) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      potentialForm (fun v => W (z,v)) (ψ.coreSlice s z.1).normalized) (volume.prod volume) := by
  simp only [potentialForm_normalized_eq]
  exact ((mass_coreSlice_integrable ψ s).aestronglyMeasurable.comp_fst).inv₀.mul
    (potentialForm_coreSlice_joint_aestronglyMeasurable ψ s W hW)

lemma restrictedOutPotential_joint_measurable {m : ℕ} {A : Set Space} (hA : MeasurableSet A) :
    Measurable (fun z : Configuration m × Space => restrictedOutPotential z.1 A z.2) := by
  apply Finset.measurable_fun_sum
  intro i hi
  apply Measurable.ite (hA.preimage ((continuous_position i).measurable.comp measurable_fst)) _ measurable_const
  simp only [coulombKernel]
  exact (((continuous_position i).measurable.comp measurable_fst).sub measurable_snd).norm.inv

lemma restrictedCorePotential_normalized_slice_joint {m k : ℕ} (u : H1Vector (m+k))
    (s : Spins m) {A : Set Space} (hA : MeasurableSet A) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      restrictedCorePotential (u.coreSlice s z.1).normalized A z.2) (volume.prod volume) := by
  have hW : Measurable (fun z : (Configuration m × Space) × Configuration k =>
      restrictedOutPotential z.2 A z.1.2) :=
    (restrictedOutPotential_joint_measurable hA).comp (measurable_snd.prodMk measurable_fst.snd)
  have H := potentialForm_normalized_coreSlice_joint_aestronglyMeasurable u s _ hW
  simpa only [potentialForm_restrictedOutPotential _ hA] using H

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_OutCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma positive_square_ballCloud_integral_le {J : ℕ} (S : Nuclei J) (f : Space → ℝ)
    (hm : AEStronglyMeasurable f volume) (hbound : ∀ z, f z ≤ attraction S z)
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    (∫ z, (max (f z) 0)^2*ballCloud y a 1 z) ≤ (totalCharge S/a)^2 := by
  calc
    _ ≤ ∫ z, (totalCharge S/a)^2*ballCloud y a 1 z := by
      apply integral_mono (positive_square_ballCloud_integrable S f hm hbound ha y hnuc)
        ((ballCloud_integrable a 1 y).const_mul _)
      intro z
      by_cases hz : z-y ∈ Metric.ball (0:Space) a
      · have hdist : ‖z-y‖ < a := by simpa only [Metric.mem_ball,dist_zero_right] using hz
        have hsep (j : Fin J) : a ≤ ‖z-S.position j‖ := by
          have ht : ‖S.position j-y‖ ≤ ‖S.position j-z‖+‖z-y‖ := by
            simpa only [dist_eq_norm] using dist_triangle (S.position j) z y
          rw [norm_sub_rev (S.position j) z] at ht
          linarith [hnuc j]
        have hP : max (f z) 0 ≤ totalCharge S/a :=
          (max_le (hbound z) (attraction_nonneg S z)).trans (attraction_le_totalCharge_div S ha z hsep)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_right _ _) hP 2)
          (uniformBall_nonneg ha zero_le_one (z-y))
      · simp only [ballCloud,uniformBall,indicator_of_notMem hz,mul_zero,le_refl]
    _ = _ := by rw [integral_const_mul,ballCloud_mass ha,mul_one]

def localFarCap {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) (a : ℝ) : ℝ :=
  Real.sqrt (8*(∫ v, (max (recordedFarField S u x {z | 4*a ≤ ‖z-y‖} v) 0)^2*
    ballCloud y (2*a) 1 v))

lemma localFarCap_nonneg {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) (a : ℝ) : 0 ≤ localFarCap S u x y a := Real.sqrt_nonneg _

lemma localFarCap_sq {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) {a : ℝ} (ha : 0 < a) :
    (localFarCap S u x y a)^2=8*(∫ v,
      (max (recordedFarField S u x {z | 4*a ≤ ‖z-y‖} v) 0)^2*ballCloud y (2*a) 1 v) := by
  apply Real.sq_sqrt
  apply mul_nonneg (by norm_num)
  exact integral_nonneg (fun v => mul_nonneg (sq_nonneg _) (uniformBall_nonneg (by linarith) zero_le_one (v-y)))

lemma pairPotential_nonneg_pointwise {m : ℕ} (x : Configuration m) : 0 ≤ pairPotential x := by
  unfold pairPotential
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact le_rfl

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_EnsembleCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma slice_ensemble_cauchy {P : Type*} [Fintype P]
    (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (F G : (p : P) → Spins (m p) → Configuration (m p) → ℝ)
    (hF : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2))
    (hG : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(G p s x)^2))
    (hFG : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x*G p s x))) :
    (∑ p, sliceExpectation (u p) (fun s x => F p s x*G p s x))^2 ≤
      (∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2))*
      (∑ p, sliceExpectation (u p) (fun s x => (G p s x)^2)) := by
  let A : ℝ := ∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2)
  let B : ℝ := ∑ p, sliceExpectation (u p) (fun s x => (G p s x)^2)
  let C : ℝ := ∑ p, sliceExpectation (u p) (fun s x => F p s x*G p s x)
  have hn (t : ℝ) : 0 ≤ A*(t*t)+(-2*C)*t+B := by
    have hp : 0 ≤ ∑ p, ∑ s : Spins (m p), ∫ x,
        mass ((u p).coreSlice s x)*(t*F p s x-G p s x)^2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
        integral_nonneg (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
    have he (p) (s : Spins (m p)) :
        (∫ x, mass ((u p).coreSlice s x)*(t*F p s x-G p s x)^2) =
        t^2*(∫ x, mass ((u p).coreSlice s x)*(F p s x)^2)-
          (2*t)*(∫ x, mass ((u p).coreSlice s x)*(F p s x*G p s x))+
            (∫ x, mass ((u p).coreSlice s x)*(G p s x)^2) := by
      have hi : Integrable (fun x => t^2*(mass ((u p).coreSlice s x)*(F p s x)^2)-
          (2*t)*(mass ((u p).coreSlice s x)*(F p s x*G p s x))) :=
        ((hF p s).const_mul (t^2)).sub ((hFG p s).const_mul (2*t))
      calc
        _ = ∫ x, (t^2*(mass ((u p).coreSlice s x)*(F p s x)^2)-
            (2*t)*(mass ((u p).coreSlice s x)*(F p s x*G p s x)))+
            mass ((u p).coreSlice s x)*(G p s x)^2 :=
          integral_congr_ae (Eventually.of_forall (fun x => by ring))
        _ = _ := by
          rw [integral_add hi (hG p s),integral_sub ((hF p s).const_mul _) ((hFG p s).const_mul _),integral_const_mul,integral_const_mul]
    simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hp
    change 0 ≤ t^2*A-2*t*C+B at hp
    nlinarith
  have h := discrim_le_zero hn
  unfold discrim at h
  change C^2 ≤ A*B
  nlinarith

lemma slice_ensemble_mul_le_sqrt {P : Type*} [Fintype P]
    (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (F G : (p : P) → Spins (m p) → Configuration (m p) → ℝ)
    (hF : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2))
    (hG : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(G p s x)^2))
    (hFG : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x*G p s x))) :
    (∑ p, sliceExpectation (u p) (fun s x => F p s x*G p s x)) ≤
      Real.sqrt ((∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2))*
      (∑ p, sliceExpectation (u p) (fun s x => (G p s x)^2))) :=
  Real.le_sqrt_of_sq_le (slice_ensemble_cauchy m k u F G hF hG hFG)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScaledTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

def countTestEnergy : ℝ := ∫ x, testCharge cutSeed x*cutSeed x

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_FineCountTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def patchRetained {n : ℕ} (y : Space) (t b : ℝ) (x : Configuration n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ‖position x i-y‖<t-7*b)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_LpParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology
namespace Coulomb

lemma aestronglyMeasurable_of_dist {α B : Type*} [MeasurableSpace α]
    {μ : Measure α} [MetricSpace B] [CompleteSpace B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B] [Nonempty B] (f : α → B)
    (h : ∀ b, AEMeasurable (fun x => dist (f x) b) μ) : AEStronglyMeasurable f μ := by
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq B
  let e : B → ℕ → ℝ := fun b n => dist b (v n)
  have he : Continuous e := continuous_pi (fun n => continuous_id.dist continuous_const)
  have hei : Function.Injective e := by
    intro a b hab
    have H : (fun z => dist a z)=(fun z => dist b z) :=
      Continuous.ext_on hv (continuous_const.dist continuous_id)
        (continuous_const.dist continuous_id) (by
          rintro _ ⟨n,rfl⟩
          exact congrFun hab n)
    have HH := congrFun H b
    simpa only [dist_self,dist_eq_zero] using HH
  have hem := he.measurableEmbedding hei
  apply (hem.aemeasurable_comp_iff.mp (AEMeasurable.of_eval (fun index => h (v index)))).aestronglyMeasurable

lemma tfField_parameter_aestronglyMeasurable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {Ω : Set Space} [IsFiniteMeasure (volume.restrict Ω)]
    (W : A → TFLq (volume.restrict Ω)) (Φ : A × Space → ℝ)
    (hΦ : AEStronglyMeasurable Φ (μ.prod (volume.restrict Ω)))
    (hW : ∀ᵐ a ∂μ, W a =ᵐ[volume.restrict Ω] fun y => Φ (a,y)) :
    AEStronglyMeasurable W μ := by
  have : Fact (TFFieldExponent ≠ ∞) := ⟨by simp [TFFieldExponent]⟩
  let : MeasurableSpace (TFLq (volume.restrict Ω)) := borel _
  let : BorelSpace (TFLq (volume.restrict Ω)) := ⟨rfl⟩
  apply aestronglyMeasurable_of_dist
  intro g
  have hD := hΦ.sub ((Lp.aestronglyMeasurable g).comp_snd (μ := μ))
  have hI := (hD.enorm.pow_const (5/2:ℝ)).lintegral_prod_right'
  have hM := (hI.pow_const (2/5:ℝ)).ennreal_toReal
  apply hM.congr
  filter_upwards [hW] with a ha
  rw [Lp.dist_def]
  have he : (⇑(W a)-⇑g) =ᵐ[volume.restrict Ω] fun y => Φ (a,y)-g y := by
    filter_upwards [ha] with y hy
    simp only [Pi.sub_apply,hy]
  rw [eLpNorm_congr_ae he]
  have hmeas := ((Lp.aestronglyMeasurable (W a)).sub (Lp.aestronglyMeasurable g)).congr he
  norm_num [eLpNorm,eLpNorm',TFFieldExponent,hmeas]

end Coulomb

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

lemma continuous_tfEnergy_joint (c : ℝ) :
    Continuous (fun z : TFLq (volume.restrict Ω) × TFLp (volume.restrict Ω) => tfEnergy hΩ c z.1 z.2) := by
  unfold tfEnergy tfFunctional
  apply (((continuous_snd.norm.rpow_const (fun _ => Or.inr (by norm_num : (0:ℝ)≤5/3))).const_mul c).sub
    tfFieldContinuous.continuous₂).add
  exact ((tfCoulombContinuous hΩ).continuous₂.comp (continuous_snd.prodMk continuous_snd)).div_const 2

lemma continuous_tfMass : Continuous (fun f : TFLp (volume.restrict Ω) => ∫ x in Ω, f x) := by
  let h1 : MemLp (fun _ : Space => (1:ℝ)) TFFieldExponent (volume.restrict Ω) := memLp_const 1
  let W : TFLq (volume.restrict Ω) := h1.toLp _
  have he : (fun f : TFLp (volume.restrict Ω) => ∫ x in Ω, f x) = tfFieldContinuous W := by
    funext f
    rw [tfFieldContinuous_apply]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp] with x hx
    simp only [W,hx,one_mul]
  rw [he]
  exact (tfFieldContinuous W).continuous

omit [IsFiniteMeasure (volume.restrict Ω)] in
include hΩ in
lemma integral_tfDensity [IsFiniteMeasure (volume.restrict Ω)]
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    (∫ x, tfDensity Ω f x)=∫ x in Ω, f x := by
  rw [integral_congr_ae (tfDensity_ae_tfExtend hΩ hf)]
  exact integral_indicator hΩ

lemma localTFEnergy_nonpos (W : TFLq (volume.restrict Ω)) :
    tfEnergy hΩ thomasFermiKineticConstant W (localTFMinimizer hΩ W)≤0 := by
  have H := localTFMinimizer_minimizes hΩ W (f := 0) (by
    filter_upwards [Lp.coeFn_zero ℝ TFExponent (volume.restrict Ω)] with x hx
    simp only [hx,Pi.zero_apply,le_refl])
  simpa only [tfEnergy,tfFunctional,norm_zero,Real.zero_rpow (by norm_num : (5/3:ℝ)≠0),
    mul_zero,map_zero,sub_zero,_root_.zero_apply,zero_div,add_zero] using H

lemma localTFEnergy_abs_bound {D F : ℝ} (hD : 0<D) (_ : 0≤F)
    (hd : ∀ x∈Ω, ∀ y∈Ω, ‖x-y‖≤D) (W : TFLq (volume.restrict Ω))
    (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F) :
    |tfEnergy hΩ thomasFermiKineticConstant W (localTFMinimizer hΩ W)|≤D*F^2/2 := by
  have H := tfEnergy_mass_lower hΩ (c := thomasFermiKineticConstant) hD hd W hW
    (localTFMinimizer_nonneg hΩ W)
  have hp : 0≤thomasFermiKineticConstant*‖localTFMinimizer hΩ W‖^(5/3:ℝ) :=
    mul_nonneg thomasFermiKineticConstant_pos.le (Real.rpow_nonneg (norm_nonneg _) _)
  rw [abs_of_nonpos (localTFEnergy_nonpos hΩ W)]
  have hs := sq_nonneg ((∫ x in Ω, localTFMinimizer hΩ W x)-D*F)
  have hh := mul_le_mul_of_nonneg_left H (show 0≤2*D by positivity)
  field_simp at hh
  nlinarith

lemma localTFMass_bound {D F : ℝ} (hD : 0<D) (hF : 0≤F)
    (hd : ∀ x∈Ω, ∀ y∈Ω, ‖x-y‖≤D) (W : TFLq (volume.restrict Ω))
    (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F) :
    0≤(∫ y, localTFDensity hΩ W y) ∧ (∫ y, localTFDensity hΩ W y)≤2*D*F := by
  rw [localTFDensity,integral_tfDensity hΩ (localTFMinimizer_nonneg hΩ W)]
  exact ⟨tfMass_nonneg (localTFMinimizer_nonneg hΩ W),
    (tfEnergy_sublevel_mass_bound hΩ hD thomasFermiKineticConstant_pos hF hd W hW
      (localTFMinimizer_nonneg hΩ W) (localTFEnergy_nonpos hΩ W)).1⟩

lemma conditional_localTF_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (W : A → TFLq (volume.restrict Ω)) (hWm : AEStronglyMeasurable W μ)
    (w F : A → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hF : ∀ᵐ x ∂μ, 0≤F x) (hFi : Integrable (fun x => w x*(F x)^2) μ)
    {D : ℝ} (hD : 0<D) (hd : ∀ x∈Ω, ∀ y∈Ω, ‖x-y‖≤D)
    (hcap : ∀ᵐ x ∂μ, ∀ᵐ y ∂volume.restrict Ω, W x y≤F x) :
    Integrable (fun x => w x*(∫ y, localTFDensity hΩ (W x) y)) μ ∧
    Integrable (fun x => w x*tfEnergy hΩ thomasFermiKineticConstant (W x) (localTFMinimizer hΩ (W x))) μ := by
  have hf := (continuous_localTFMinimizer hΩ).comp_aestronglyMeasurable hWm
  have hm : AEStronglyMeasurable (fun x => ∫ y, localTFDensity hΩ (W x) y) μ := by
    have he : (fun x => ∫ y, localTFDensity hΩ (W x) y)=
        (fun x => ∫ y in Ω, localTFMinimizer hΩ (W x) y) := by
      funext x
      exact integral_tfDensity hΩ (localTFMinimizer_nonneg hΩ (W x))
    rw [he]
    exact (continuous_tfMass).comp_aestronglyMeasurable hf
  have he := (continuous_tfEnergy_joint hΩ thomasFermiKineticConstant).comp_aestronglyMeasurable
    (hWm.prodMk hf)
  constructor
  · apply ((hw.add hFi).const_mul D).mono' (hw.aestronglyMeasurable.mul hm)
    filter_upwards [hw0,hF,hcap] with x hx hf hc
    have H := localTFMass_bound hΩ hD hf hd (W x) hc
    dsimp only [Pi.mul_apply, Pi.add_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx H.1)]
    have HH := mul_le_mul_of_nonneg_left H.2 hx
    have hsq := mul_nonneg hx (sq_nonneg (F x-1))
    have hmul := mul_nonneg hD.le hsq
    nlinarith
  · apply (hFi.const_mul (D/2)).mono' (hw.aestronglyMeasurable.mul he)
    filter_upwards [hw0,hF,hcap] with x hx hf hc
    dsimp only [Pi.mul_apply]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hx,Real.norm_eq_abs]
    have H := mul_le_mul_of_nonneg_left (localTFEnergy_abs_bound hΩ hD hf hd (W x) hc) hx
    calc
      _ ≤ w x*(D*F x^2/2) := H
      _ = _ := by ring

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff SchwartzMap Pointwise
noncomputable section
namespace Coulomb

instance finite_volume_ball (y : Space) (r : ℝ) : IsFiniteMeasure (volume.restrict (Metric.ball y r)) :=
  isFiniteMeasure_restrict.mpr ((measure_mono Metric.ball_subset_closedBall).trans_lt
    (isCompact_closedBall y r).measure_lt_top).ne

lemma patch_nucleus_separation {J : ℕ} (S : Nuclei J) {a b t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t≤6*a) (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖) :
    ∀ j x, x∈Metric.ball y (t-4*b) → a≤‖x-S.position j‖ := by
  intro j x hx
  have hh : ‖x-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have H := norm_sub_le_norm_sub_add_norm_sub (S.position j) x y
  rw [norm_sub_rev (S.position j) x] at H
  linarith [hn j]

def tfInteriorCountConstant : ℝ :=
  (tfInteriorConstant thomasFermiKineticConstant/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)*(27*(Real.pi*4/3))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_PatchComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap
noncomputable section
namespace Coulomb

lemma patch_diameter {a b t : ℝ} (_ : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space) :
    ∀ x∈Metric.ball y (t-4*b), ∀ z∈Metric.ball y (t-4*b), ‖x-z‖≤12*a := by
  intro x hx z hz
  have hx' : ‖x-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hz' : ‖z-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have hh := norm_sub_le_norm_sub_add_norm_sub x y z
  rw [norm_sub_rev y z] at hh
  linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_PatchErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
noncomputable section
namespace Coulomb

def unitWindowKinetic : ℝ := ∑ j : Fin 3, ∫ z : Space, (fderiv ℝ unitWindow z (EuclideanSpace.single j 1))^2
lemma unitWindowKinetic_nonneg : 0≤unitWindowKinetic := unitWindow_kinetic_nonneg

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_AtomicMesh
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma atomicCellScale_nucleus_far (y : Space) : 4*atomicCellScale y ≤ ‖(0:Space)-y‖ := by
  rw [zero_sub,norm_neg]
  have h := atomicCellScale_norm y
  have hz := atomicCellScale_nonneg y
  linarith

lemma atomicPatchMesh_covers (w : Space) (hw : ‖w‖ ≤ 80) :
    ∃ z∈atomicPatchMesh, ‖w-z‖ < 1/4 := (Classical.choose_spec exists_atomic_patch_mesh).2 w hw

lemma atomicMeshCenter_comparable (y z : Space) (hz : z∈atomicPatchMesh) :
    atomicCellScale y/2 ≤ atomicCellScale (atomicMeshCenter y z) ∧
      atomicCellScale (atomicMeshCenter y z) ≤ 2*atomicCellScale y :=
  atomicCellScale_comparable (by nlinarith [atomicMeshCenter_distance y z hz,atomicCellScale_nonneg y])

theorem atomicMesh_cover {y : Space} (hy : y≠0) (w : Space)
    (hw : ‖w-y‖ ≤ 80*atomicCellScale y) :
    ∃ z∈atomicPatchMesh, ‖w-atomicMeshCenter y z‖ ≤ atomicCellScale (atomicMeshCenter y z) := by
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have hnorm : ‖a⁻¹ • (w-y)‖ ≤ 80 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    exact (inv_mul_le_iff₀ ha).2 (by simpa only [mul_comm] using hw)
  obtain ⟨z,hz,hclose⟩ := atomicPatchMesh_covers (a⁻¹ • (w-y)) hnorm
  have he : w-atomicMeshCenter y z = a • (a⁻¹ • (w-y)-z) := by
    simp only [smul_sub,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,atomicMeshCenter]
    change w-(y+a • z)=w-y-a • z
    abel
  have hdist : ‖w-atomicMeshCenter y z‖ < a/4 := by
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    nlinarith
  refine ⟨z,hz,?_⟩
  have H := (atomicMeshCenter_comparable y z hz).1
  dsimp [a] at hdist
  linarith [atomicCellScale_nonneg y]

lemma atomic_raw_exclusion_subset {z v : Space}
    (hv : ‖v-z‖ ≤ 2*atomicCellScale z) :
    {w : Space | 40*atomicCellScale v ≤ ‖w-v‖} ⊆ {w : Space | 4*atomicCellScale z ≤ ‖w-z‖} := by
  have H := (atomicCellScale_comparable (show ‖v-z‖ ≤ 82*atomicCellScale z by nlinarith [atomicCellScale_nonneg z])).1
  intro w hw
  change 40*atomicCellScale v ≤ ‖w-v‖ at hw
  change 4*atomicCellScale z ≤ ‖w-z‖
  have ht : ‖w-v‖ ≤ ‖w-z‖+‖v-z‖ := by
    simpa only [dist_eq_norm,norm_sub_rev z v] using dist_triangle w z v
  linarith [atomicCellScale_nonneg z]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CountUnits
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma localCount_cover {n : ℕ} {C : Type*} [Fintype C] {B : Set Space} (A : C → Set Space)
    (hc : B ⊆ ⋃ c, A c) (x : Configuration n) : localCount B x ≤ ∑ c, localCount (A c) x := by
  unfold localCount
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : position x i∈B
  · obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (hc hx)
    rw [indicator_of_mem hx]
    calc
      1=(A c).indicator (fun _ => (1:ℝ)) (position x i) := by rw [indicator_of_mem hc]
      _ ≤ _ := Finset.single_le_sum (fun d _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.mem_univ c)
  · rw [indicator_of_notMem hx]
    exact Finset.sum_nonneg (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

lemma expectedPopulation_cover {n : ℕ} (ψ : H1Vector n) {C : Type*} [Fintype C]
    {B : Set Space} (hB : MeasurableSet B) (A : C → Set Space) (hA : ∀ c, MeasurableSet (A c))
    (hc : B ⊆ ⋃ c, A c) : expectedPopulation ψ B ≤ ∑ c, expectedPopulation ψ (A c) := by
  rw [expectedPopulation_eq ψ hB]
  simp_rw [expectedPopulation_eq ψ (hA _)]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_finsetSum _ (fun c _ => by simpa using localCount_weight_integrable ψ (hA c) s 1)]
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (localCount_nonneg _ _) (sq_nonneg _))
  · exact integrable_finsetSum _ (fun c _ => by simpa using localCount_weight_integrable ψ (hA c) s 1)
  · exact Eventually.of_forall (fun x => by
      dsimp only
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (localCount_cover A hc x) (sq_nonneg _))

def screenCountRatio {n : ℕ} (ψ : H1Vector n) (δ : ℝ) (y : Space) : ℝ :=
  if y=0 then 0 else localCountSecondMoment ψ (Metric.closedBall y (atomicCellScale y))/(screenMass δ (atomicCellScale y))^2

def screenCountParameter {n : ℕ} (ψ : H1Vector n) (δ : ℝ) : ℝ :=
  max 1 (sSup (Set.range (screenCountRatio ψ δ)))

lemma screenCountRatio_le {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) (δ : ℝ) (y : Space) :
    screenCountRatio ψ δ y ≤ (n:ℝ)^2 := by
  unfold screenCountRatio
  split_ifs
  · positivity
  · rw [div_le_iff₀ (sq_pos_of_pos (screenMass_pos δ _))]
    have H := localCountSecondMoment_le ψ (Metric.closedBall y (atomicCellScale y))
    rw [hm,mul_one] at H
    exact H.trans (le_mul_of_one_le_right (sq_nonneg _) (by nlinarith [screenMass_ge_one δ (atomicCellScale y)]))

lemma screenCountParameter_ge_one {n : ℕ} (ψ : H1Vector n) (δ : ℝ) :
    1 ≤ screenCountParameter ψ δ := le_max_left _ _

lemma screenCountParameter_le {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) (δ : ℝ) :
    screenCountParameter ψ δ ≤ max 1 ((n:ℝ)^2) := by
  unfold screenCountParameter
  apply max_le (le_max_left _ _)
  exact (csSup_le (Set.range_nonempty _) (fun _ ⟨y,hy⟩ => hy ▸ screenCountRatio_le ψ hm δ y)).trans (le_max_right _ _)

lemma screenCountParameter_controls {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) (δ : ℝ)
    {y : Space} (hy : y≠0) :
    localCountSecondMoment ψ (Metric.closedBall y (atomicCellScale y)) ≤
      screenCountParameter ψ δ*(screenMass δ (atomicCellScale y))^2 := by
  have hb : BddAbove (Set.range (screenCountRatio ψ δ)) :=
    ⟨(n:ℝ)^2,fun _ ⟨z,hz⟩ => hz ▸ screenCountRatio_le ψ hm δ z⟩
  have H := (le_csSup hb (Set.mem_range_self y)).trans (le_max_right 1 (sSup (Set.range (screenCountRatio ψ δ))))
  change screenCountRatio ψ δ y ≤ screenCountParameter ψ δ at H
  simpa only [screenCountRatio,ite_eq_right hy,div_le_iff₀ (sq_pos_of_pos (screenMass_pos δ _))] using H

lemma atomicPatch_population {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ P : ℝ} (hδ : 0 ≤ δ) (hP : 0 ≤ P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) {y : Space} (hy : y≠0) :
    expectedPopulation ψ (Metric.closedBall y (80*atomicCellScale y)) ≤
      (Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8*Real.sqrt P*screenMass δ (atomicCellScale y) := by
  let A := fun z : {z : Space // z∈atomicPatchMesh} =>
    Metric.closedBall (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val))
  have hcover : Metric.closedBall y (80*atomicCellScale y) ⊆ ⋃ z, A z := by
    intro x hx
    obtain ⟨z,hz,hzx⟩ := atomicMesh_cover hy x (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,by simpa only [A,Metric.mem_closedBall,dist_eq_norm] using hzx⟩
  have HB := expectedPopulation_cover ψ measurableSet_closedBall A (fun _ => measurableSet_closedBall) hcover
  have HE (z : {z : Space // z∈atomicPatchMesh}) : expectedPopulation ψ (A z) ≤
      8*Real.sqrt P*screenMass δ (atomicCellScale y) := by
    have hz : atomicMeshCenter y z.val≠0 := atomicCellScale_near_nonzero hy
      (by nlinarith [atomicMeshCenter_distance y z.val z.property,atomicCellScale_nonneg y])
    have hs := expectedPopulation_sq_le ψ (A:=A z) measurableSet_closedBall hm
    have HC := hc (atomicMeshCenter y z.val) hz
    have hu := atomicMeshCenter_comparable y z.val z.property
    have Hm := screenMass_comparable hδ (atomicCellScale_pos hy) (show (1:ℝ) ≤ 2 by norm_num) hu.1 (by linarith [hu.2])
    norm_num at Hm
    have hsq : (expectedPopulation ψ (A z))^2 ≤ (Real.sqrt P*screenMass δ (atomicCellScale (atomicMeshCenter y z.val)))^2 := by
      rw [mul_pow,Real.sq_sqrt hP]
      exact hs.trans HC
    have hp : expectedPopulation ψ (A z) ≤ Real.sqrt P*screenMass δ (atomicCellScale (atomicMeshCenter y z.val)) :=
      (sq_le_sq₀ (show 0 ≤ expectedPopulation ψ (A z) from Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _))))) (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le)).mp hsq
    exact hp.trans (by nlinarith [mul_le_mul_of_nonneg_left Hm (Real.sqrt_nonneg P)])
  calc
    _ ≤ ∑ z, expectedPopulation ψ (A z) := HB
    _ ≤ ∑ _z : {z : Space // z∈atomicPatchMesh}, 8*Real.sqrt P*screenMass δ (atomicCellScale y) :=
      Finset.sum_le_sum (fun z _ => HE z)
    _ = _ := by simp; ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ShellChoice
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma localCountSecondMoment_cover {n : ℕ} {C : Type*} [Fintype C] (ψ : H1Vector n)
    {B : Set Space} (A : C → Set Space) (hA : ∀ c, MeasurableSet (A c)) (hcover : B⊆⋃ c, A c) :
    localCountSecondMoment ψ B≤(Fintype.card C:ℝ)*∑ c, localCountSecondMoment ψ (A c) := by
  unfold localCountSecondMoment
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_finsetSum _ (fun c _ => localCount_weight_integrable ψ (hA c) s 2),←integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · exact (integrable_finsetSum _ (fun c _ => localCount_weight_integrable ψ (hA c) s 2)).const_mul _
  · filter_upwards [] with x
    rw [←Finset.sum_mul,←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (pow_le_pow_left₀ (localCount_nonneg B x) (localCount_cover A hcover x) 2).trans
      (by simpa only [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun c => localCount (A c) x))

lemma localCount_disjoint_sum_le {n : ℕ} {C : Type*} [Fintype C] {B : Set Space}
    (A : C → Set Space) (hsub : ∀ c, A c⊆B)
    (hdis : Pairwise (fun c d => Disjoint (A c) (A d))) (x : Configuration n) :
    (∑ c, localCount (A c) x)≤localCount B x := by
  unfold localCount
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : ∃ c, position x i∈A c
  · obtain ⟨c,hc⟩ := hx
    rw [indicator_of_mem (hsub c hc)]
    have he : ∑ d, (A d).indicator (fun _ => (1:ℝ)) (position x i)=1 := by
      rw [Finset.sum_eq_single c]
      · exact indicator_of_mem hc _
      · intro d hd hdc
        apply indicator_of_notMem
        intro hd'
        exact Set.disjoint_left.mp (hdis hdc) hd' hc
      · simp
    exact he.le
  · have hn (c : C) : position x i∉A c := fun hc => hx ⟨c,hc⟩
    simp only [indicator_of_notMem (hn _),Finset.sum_const_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma localCountSecondMoment_disjoint_sum_le {n : ℕ} {C : Type*} [Fintype C] (ψ : H1Vector n)
    {B : Set Space} (hB : MeasurableSet B) (A : C → Set Space) (hA : ∀ c, MeasurableSet (A c))
    (hsub : ∀ c, A c⊆B) (hdis : Pairwise (fun c d => Disjoint (A c) (A d))) :
    (∑ c, localCountSecondMoment ψ (A c))≤localCountSecondMoment ψ B := by
  unfold localCountSecondMoment
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_finsetSum _ (fun c _ => localCount_weight_integrable ψ (hA c) s 2)]
  apply integral_mono_ae (integrable_finsetSum _ (fun c _ => localCount_weight_integrable ψ (hA c) s 2))
    (localCount_weight_integrable ψ hB s 2)
  filter_upwards [] with x
  rw [←Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun c _ => localCount_nonneg (A c) x)).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun c _ => localCount_nonneg (A c) x))
      (localCount_disjoint_sum_le A hsub hdis x) 2)

def deletedShell (y : Space) (t b : ℝ) : Set Space := {z | t-7*b≤‖z-y‖ ∧ ‖z-y‖≤t+b}

lemma deletedShell_measurable (y : Space) (t b : ℝ) : MeasurableSet (deletedShell y t b) := by
  change MeasurableSet ({z : Space | t-7*b≤‖z-y‖} ∩ {z : Space | ‖z-y‖≤t+b})
  exact (isClosed_le continuous_const (by fun_prop)).measurableSet.inter
    (isClosed_le (by fun_prop) continuous_const).measurableSet

lemma deletedShell_disjoint {y : Space} {t u b : ℝ} (h : t+8*b<u) :
    Disjoint (deletedShell y t b) (deletedShell y u b) := by
  apply Set.disjoint_left.mpr
  intro z hz ht
  have := hz.2
  have := ht.1
  linarith

theorem exists_deletedShell_small {n : ℕ} (ψ : H1Vector n) (y : Space)
    {a b : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) :
    ∃ t∈Set.Icc (5*a) (6*a), localCountSecondMoment ψ (deletedShell y t b)≤
      (18*b/a)*localCountSecondMoment ψ (Metric.closedBall y (7*a)) := by
  let N : ℕ := ⌊a/(9*b)⌋₊
  have hq : 2≤a/(9*b) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hfloor : (N:ℝ)≤a/(9*b) := Nat.floor_le (by positivity)
  have hlt : a/(9*b)<(N:ℝ)+1 := Nat.lt_floor_add_one _
  have hNp : 0<N := by
    have : (1:ℝ)<(N:ℝ) := by linarith
    exact_mod_cast (lt_trans zero_lt_one this)
  have hN : a/(18*b)≤(N:ℝ) := by
    have hN1 : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hNp
    have he : a/(9*b)=2*(a/(18*b)) := by ring
    linarith
  let t : Fin N → ℝ := fun j => 5*a+9*b*(j.val:ℝ)
  have ht (j : Fin N) : t j∈Set.Icc (5*a) (6*a) := by
    have hj : (j.val:ℝ)≤(N:ℝ) := by exact_mod_cast (Nat.le_of_lt j.isLt)
    have hh : 9*b*(N:ℝ)≤a := by nlinarith [(le_div_iff₀ (by positivity : 0<9*b)).mp hfloor]
    dsimp [t]
    constructor
    · have hj0 : (0:ℝ)≤ j.val := Nat.cast_nonneg _
      nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left hj (by positivity : 0≤9*b)]
  let A : Fin N → Set Space := fun j => deletedShell y (t j) b
  have hsub (j : Fin N) : A j⊆Metric.closedBall y (7*a) := by
    intro z hz
    change t j-7*b≤‖z-y‖ ∧ ‖z-y‖≤t j+b at hz
    rw [Metric.mem_closedBall,dist_eq_norm]
    linarith [(ht j).2]
  have hdis : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij|hji
    · apply deletedShell_disjoint (y:=y) (t:=t i) (u:=t j) (b:=b)
      have hv : (i.val:ℝ)+1≤ j.val := by exact_mod_cast (show i.val+1≤ j.val from hij)
      dsimp [t]
      nlinarith
    · have H : t j+8*b<t i := by
        have hv : (j.val:ℝ)+1≤ i.val := by exact_mod_cast (show j.val+1≤ i.val from hji)
        dsimp [t]
        nlinarith
      exact (deletedShell_disjoint (y:=y) H).symm
  have HS := localCountSecondMoment_disjoint_sum_le ψ measurableSet_closedBall A
    (fun j => deletedShell_measurable y (t j) b) hsub hdis
  have hsome : ∃ j : Fin N, localCountSecondMoment ψ (A j)≤
      localCountSecondMoment ψ (Metric.closedBall y (7*a))/(N:ℝ) := by
    by_contra hn
    push Not at hn
    have : Nonempty (Fin N) := ⟨⟨0,hNp⟩⟩
    have H := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ) Finset.univ_nonempty (fun j _ => hn j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
    rw [mul_div_cancel₀ _ (show (N:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt hNp))] at H
    linarith
  obtain ⟨j,hj⟩ := hsome
  refine ⟨t j,ht j,hj.trans ?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hNp : (0:ℝ)<N)).mpr
  have hprod : a≤18*b*(N:ℝ) := by
    have H := (div_le_iff₀ (by positivity : 0<18*b)).mp hN
    nlinarith
  have hr : 1≤18*b/a*(N:ℝ) := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ ha).mpr (by simpa using hprod)
  nlinarith [mul_le_mul_of_nonneg_right hr (localCountSecondMoment_nonneg ψ (Metric.closedBall y (7*a)))]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ThinCut
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

def thinAngle (y : Space) (t b : ℝ) (x : Space) : ℝ :=
  (Real.pi/2)*Real.smoothTransition (((t+b)^2-‖x-y‖^2)/((t+b)^2-t^2))

lemma thinAngle_smooth (y : Space) (t b : ℝ) : ContDiff ℝ ∞ (thinAngle y t b) := by
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).div_const _))

lemma thinAngle_fderiv (y : Space) (t b : ℝ) (x v : Space) :
    fderiv ℝ (thinAngle y t b) x v =
      -Real.pi*deriv Real.smoothTransition (((t+b)^2-‖x-y‖^2)/((t+b)^2-t^2))*
        inner ℝ (x-y) v/((t+b)^2-t^2) := by
  have Hf := (((((hasFDerivAt_id x).sub_const y).norm_sq).const_sub ((t+b)^2)).const_mul ((t+b)^2-t^2)⁻¹)
  have Hfun : (fun z : Space => ((t+b)^2-t^2)⁻¹ * ((t+b)^2-‖id z-y‖^2)) =
      (fun z : Space => ((t+b)^2-‖z-y‖^2)/((t+b)^2-t^2)) := by
    funext z
    simp only [id_eq,div_eq_mul_inv,mul_comm]
  rw [Hfun] at Hf
  have Hg := (((Real.smoothTransition.contDiff (n:=1)).differentiable (by simp) _).hasDerivAt.comp_hasFDerivAt x Hf).const_mul (Real.pi/2)
  have H := congrArg (fun L : Space →L[ℝ] ℝ => L v) Hg.fderiv
  change fderiv ℝ (thinAngle y t b) x v = _ at H
  rw [H]
  simp only [smul_apply,neg_apply,
    smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    innerSL_apply_apply,id_eq]
  ring

lemma thinAngle_core (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (x : Space) (hx : ‖x-y‖≤t) : thinAngle y t b x=Real.pi/2 := by
  have hd : 0<(t+b)^2-t^2 := by nlinarith
  unfold thinAngle
  rw [Real.smoothTransition.one_of_one_le]
  · ring
  · rw [le_div_iff₀ hd]
    nlinarith [norm_nonneg (x-y)]

lemma thinAngle_exterior (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (x : Space) (hx : t+b≤‖x-y‖) : thinAngle y t b x=0 := by
  have hd : 0<(t+b)^2-t^2 := by nlinarith
  unfold thinAngle
  rw [Real.smoothTransition.zero_of_nonpos,mul_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (x-y)]) hd.le

lemma thinAngle_fderiv_exterior (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    {x : Space} (hx : t+b<‖x-y‖) : fderiv ℝ (thinAngle y t b) x=0 := by
  have H : thinAngle y t b =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    have hh : ∀ᶠ z in 𝓝 x, t+b < ‖z-y‖ :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hx
    filter_upwards [hh] with z hz
    exact thinAngle_exterior y ht hb z hz.le
  rw [H.fderiv_eq]
  simp

lemma thinAngle_derivative_bound (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (i : Fin 3) (x : Space) :
    |fderiv ℝ (thinAngle y t b) x (EuclideanSpace.single i 1)| ≤ thinCutCoefficient/b := by
  by_cases hx : ‖x-y‖≤t+b
  · have hd : 0<(t+b)^2-t^2 := by nlinarith
    rw [thinAngle_fderiv,abs_div,abs_mul,abs_mul,abs_neg,abs_of_pos Real.pi_pos,abs_of_pos hd]
    have hi : |inner ℝ (x-y) (EuclideanSpace.single i 1)|≤‖x-y‖ := by
      simpa only [PiLp.norm_single,norm_one,mul_one] using abs_real_inner_le_norm (x-y) (EuclideanSpace.single i 1)
    calc
      _ ≤ Real.pi*transitionDerivativeBound*‖x-y‖/((t+b)^2-t^2) := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left (transition_derivative_bound _) Real.pi_pos.le)
          hi (abs_nonneg _) (mul_nonneg Real.pi_pos.le transitionDerivativeBound_pos.le)
      _ ≤ thinCutCoefficient/b := by
        rw [div_le_div_iff₀ hd hb]
        unfold thinCutCoefficient
        have hc := thinCutCoefficient_pos.le
        unfold thinCutCoefficient at hc
        have hh : ‖x-y‖*b≤(t+b)^2-t^2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hh hc]
  · rw [thinAngle_fderiv_exterior y ht hb (lt_of_not_ge hx)]
    simp only [zero_apply,abs_zero]
    exact div_nonneg thinCutCoefficient_pos.le hb.le

def thinCut (y : Space) (t b : ℝ) (l : Fin 2) (x : Space) : ℝ :=
  if l=0 then Real.sin (thinAngle y t b x) else Real.cos (thinAngle y t b x)
lemma thinCut_smooth (y : Space) (t b : ℝ) (l : Fin 2) : ContDiff ℝ ∞ (thinCut y t b l) := by
  unfold thinCut
  split_ifs
  · exact (thinAngle_smooth y t b).sin
  · exact (thinAngle_smooth y t b).cos
lemma thinCut_partition (y : Space) (t b : ℝ) (x : Space) : ∑ l : Fin 2, thinCut y t b l x^2=1 := by
  simp [Fin.sum_univ_two,thinCut]
lemma thinCut_core_zero (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (x : Space) (hx : ‖x-y‖≤t) : thinCut y t b 1 x=0 := by
  simp only [thinCut,show (1:Fin 2)≠0 by decide,ite_false,thinAngle_core y ht hb x hx,Real.cos_pi_div_two]
lemma thinCut_out_zero (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (x : Space) (hx : t+b≤‖x-y‖) : thinCut y t b 0 x=0 := by
  simp [thinCut,thinAngle_exterior y ht hb x hx]
lemma thinCut_derivative_bound (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (l : Fin 2) (i : Fin 3) (x : Space) :
    |fderiv ℝ (thinCut y t b l) x (EuclideanSpace.single i 1)| ≤ thinCutCoefficient/b := by
  have H := thinAngle_derivative_bound y ht hb i x
  unfold thinCut
  split_ifs
  · rw [fderiv_sin ((thinAngle_smooth y t b).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans (by simpa using H)
  · rw [fderiv_cos ((thinAngle_smooth y t b).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans (by simpa using H)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ThinIMS
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

lemma thinCut_fderiv_zero (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b) (l : Fin 2)
    (x : Space) (hx : t+b < ‖x-y‖) : fderiv ℝ (thinCut y t b l) x=0 := by
  have he : thinCut y t b l =ᶠ[𝓝 x] (fun _ => if l=0 then (0:ℝ) else 1) := by
    have hh : ∀ᶠ z in 𝓝 x, t+b < ‖z-y‖ :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hx
    filter_upwards [hh] with z hz
    simp only [thinCut,thinAngle_exterior y ht hb z hz.le,Real.sin_zero,Real.cos_zero]
  rw [he.fderiv_eq]
  simp

lemma thinCut_gradient_bound (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b) (i : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (thinCut y t b l) x (EuclideanSpace.single i 1))^2) ≤
      (2*(thinCutCoefficient/b)^2) * (Metric.closedBall y (t+b)).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x ∈ Metric.closedBall y (t+b)
  · rw [indicator_of_mem hx,mul_one]
    calc
      _ ≤ ∑ _l : Fin 2, (thinCutCoefficient/b)^2 := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg thinCutCoefficient_pos.le hb.le)).2
          (thinCut_derivative_bound y ht hb l i x)
      _ = _ := by simp
  · rw [indicator_of_notMem hx,mul_zero]
    have hd := thinCut_fderiv_zero y ht hb
    have hh : t+b < ‖x-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hx
    simp only [hd _ x hh,zero_apply,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      zero_pow,Finset.sum_const_zero,le_refl]

theorem form_thin_labelCut {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (thinCut y t b) (thinCut_smooth y t b)
      (thinCut_partition y t b) (thinCutCoefficient/b) (div_nonneg thinCutCoefficient_pos.le hb.le)
      (thinCut_derivative_bound y ht hb) p)) ≤
      form S ψ+3*(thinCutCoefficient/b)^2*expectedPopulation ψ (Metric.closedBall y (t+b)) := by
  rw [form_labelCut]
  apply add_le_add_right
  let c : ℝ := 2*(thinCutCoefficient/b)^2
  have hi s i := population_integrable ψ (Metric.closedBall y (t+b)) measurableSet_closedBall s i
  have H (s : Spins n) (a : Fin n × Fin 3) :
      (∫ x, (∑ l, (fderiv ℝ (thinCut y t b l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2) ≤
      c*(∫ x, (Metric.closedBall y (t+b)).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · filter_upwards [] with x
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
    · exact (hi s a.1).const_mul c
    · filter_upwards [] with x
      simpa only [c,mul_assoc] using mul_le_mul_of_nonneg_right (thinCut_gradient_bound y ht hb a.2 (position x a.1)) (sq_nonneg ‖ψ.value s x‖)
  calc
    _ ≤ (1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, c*(∫ x,
          (Metric.closedBall y (t+b)).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun a _ => H s a))) (by norm_num)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← Finset.mul_sum,expectedPopulation,c]
      ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoveredOutCost
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma sliceCount_weight_integrable {m k : ℕ} (u : H1Vector (m+k))
    {A : Set Space} (hA : MeasurableSet A) (s : Spins m) (q : ℕ) :
    Integrable (fun x => mass (u.coreSlice s x)*(localCount A x)^q) := by
  apply ((mass_coreSlice_integrable u s).mul_const ((m:ℝ)^q)).mono'
    ((mass_coreSlice_integrable u s).aestronglyMeasurable.mul
      ((localCount_measurable hA).pow_const q).aestronglyMeasurable)
  filter_upwards [] with x
  dsimp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (mass_nonneg _) (pow_nonneg (localCount_nonneg _ _) _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (localCount_nonneg _ _) (localCount_le _ _) q) (mass_nonneg _)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RecordedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma potentialForm_mono_bounded {n : ℕ} (u : H1Vector n)
    (F G : Configuration n → ℝ) (hF : Measurable F) (hG : Measurable G)
    {B C : ℝ} (hFB : ∀ x, |F x| ≤ B) (hGC : ∀ x, |G x| ≤ C)
    (hFG : ∀ x, F x ≤ G x) : potentialForm F u ≤ potentialForm G u := by
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono (boundedObservable_integrable u F hF hFB s) (boundedObservable_integrable u G hG hGC s)
  intro x
  exact mul_le_mul_of_nonneg_right (hFG x) (sq_nonneg _)

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RecordedEnsemble
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

attribute [instance] RecordedEnsemble.finite

namespace RecordedEnsemble
variable {n J : ℕ}

lemma Conserves.secondMoment {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) :
    (∑ p, localCountSecondMoment (T.vector p) A)=localCountSecondMoment ψ A := by
  have hb (x : Configuration n) : |(localCount A x)^2|≤(n:ℝ)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (localCount_nonneg _ _) (localCount_le _ _) 2
  have H := hT (fun x => (localCount A x)^2) ((localCount_measurable hA).pow_const 2) ⟨_,hb⟩
  simpa only [Function.comp_def,localCount_reindex,potentialForm,localCountSecondMoment] using H

end RecordedEnsemble
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_EnsembleMoments
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb
namespace RecordedEnsemble

def initial {n : ℕ} (ψ : H1Vector n) : RecordedEnsemble n where
  index := Unit
  finite := inferInstance
  out := fun _ => 0
  core := fun _ => n
  vector := fun _ => ψ.reindex (finCongr (Nat.zero_add n))
  labels := fun _ => finCongr (Nat.zero_add n)

lemma initial_conserves {n : ℕ} (ψ : H1Vector n) : (initial ψ).Conserves ψ := by
  intro W hW hB
  change (∑ p : Unit, potentialForm (W ∘ reindexConfiguration (finCongr (Nat.zero_add n)))
    (ψ.reindex (finCongr (Nat.zero_add n))))=potentialForm W ψ
  simp only [potentialForm_reindex]
  simp

lemma initial_fermionic {n : ℕ} (ψ : H1Vector n) (hψ : Antisymmetric ψ) :
    (initial ψ).CoreFermionic := by
  intro p
  exact (hψ.reindex _).partly _

lemma initial_supported {n : ℕ} (ψ : H1Vector n) : (initial ψ).OutSupported ∅ := by
  intro p s
  exact Eventually.of_forall (fun x i hi => by obtain ⟨j,hj⟩ := hi; exact Fin.elim0 j)

lemma initial_mass {n : ℕ} (ψ : H1Vector n) : (initial ψ).totalMass=mass ψ := by
  change (∑ p : Unit, mass (ψ.reindex (finCongr (Nat.zero_add n))))=mass ψ
  simp [mass_reindex]
lemma initial_form {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) : (initial ψ).totalForm S=form S ψ := by
  change (∑ p : Unit, form S (ψ.reindex (finCongr (Nat.zero_add n))))=form S ψ
  simp [form_reindex]

lemma count_cover_le {m : ℕ} {C : Type*} [Fintype C] (A : C → Set Space)
    (x : Configuration m) (hcover : ∀ i, ∃ c, position x i∈A c) :
    (m:ℝ)≤∑ c, localCount (A c) x := by
  calc
    _ = ∑ i : Fin m, (1:ℝ) := by simp
    _ ≤ ∑ i : Fin m, ∑ c : C, (A c).indicator (fun _ => (1:ℝ)) (position x i) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨c,hc⟩ := hcover i
      calc
        1=(A c).indicator (fun _ => (1:ℝ)) (position x i) := by rw [indicator_of_mem hc]
        _≤_ := Finset.single_le_sum (fun c _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.mem_univ c)
    _ = _ := Finset.sum_comm

end RecordedEnsemble
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_EnsembleCoveredCost
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma sliceExpectation_localCount_le {m k : ℕ} (u : H1Vector (m+k))
    {A : Set Space} (hA : MeasurableSet A) :
    sliceExpectation u (fun _ x => localCount A x) ≤ (m:ℝ)*mass u := by
  rw [←integral_mass_coreSlice u,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_const_mul]
  apply integral_mono
  · simpa only [pow_one] using sliceCount_weight_integrable u hA s 1
  · exact (mass_coreSlice_integrable u s).const_mul _
  · intro x
    dsimp only
    nlinarith [mul_le_mul_of_nonneg_left (localCount_le A x) (mass_nonneg (u.coreSlice s x))]

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_AtomicHistory
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma atomicPatchRegion_snoc {j : ℕ} (y : Fin j → Space) (z : Space) :
    atomicPatchRegion (Fin.snoc y z)=atomicPatchRegion y∪Metric.closedBall z (80*atomicCellScale z) := by
  unfold atomicPatchRegion
  rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
  simp only [Function.comp_def,Fin.snoc_castSucc,Fin.snoc_last]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RawCap
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma RecordedEnsemble.rawSquare_nonneg {n J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J)
    (y : Space) (a : ℝ) : 0 ≤ T.rawSquare S y a := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))

lemma attraction_atomic {J : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0) (y : Space) :
    attraction S y=totalCharge S/‖y‖ := by
  simp only [attraction,hatom,sub_zero,coulombKernel,div_eq_mul_inv,totalCharge,Finset.sum_mul]

lemma localCount_mono {n : ℕ} {A B : Set Space} (h : A ⊆ B) (x : Configuration n) :
    localCount A x ≤ localCount B x := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : position x i∈A
  · simp [hx,h hx]
  · simp only [indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma localCountSecondMoment_mono {n : ℕ} (ψ : H1Vector n) {A B : Set Space}
    (hB : MeasurableSet B) (h : A ⊆ B) :
    localCountSecondMoment ψ A ≤ localCountSecondMoment ψ B := by
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · exact localCount_weight_integrable ψ hB s 2
  · exact Eventually.of_forall (fun x => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (localCount_nonneg A x) (localCount_mono h x) 2) (sq_nonneg _))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_ScreenBox
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def AtomicScaleWindow (a q : ℝ) (y : Space) : Prop :=
  a ≤ q*atomicCellScale y ∧ atomicCellScale y ≤ q*a

lemma AtomicScaleWindow.nonzero {a q : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (ha : 0<a) : y≠0 := by
  intro hy
  subst y
  have hz : atomicCellScale (0:Space)=0 := by norm_num [atomicCellScale]
  dsimp [AtomicScaleWindow] at h
  rw [hz,mul_zero] at h
  linarith [h.1]

lemma AtomicScaleWindow.div_lower {a q : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (hq : 0<q) : a/q ≤ atomicCellScale y := by
  rw [div_le_iff₀ hq]
  simpa only [mul_comm] using h.1

lemma AtomicScaleWindow.enlarge {a q r : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (ha : 0 ≤ a) (hqr : q ≤ r) : AtomicScaleWindow a r y :=
  ⟨h.1.trans (mul_le_mul_of_nonneg_right hqr (atomicCellScale_nonneg _)),
    h.2.trans (mul_le_mul_of_nonneg_right hqr ha)⟩

lemma AtomicScaleWindow.near {a q : ℝ} {y z : Space} (h : AtomicScaleWindow a q y)
    (hq : 0 ≤ q) (hnear : ‖z-y‖ ≤ 82*atomicCellScale y) : AtomicScaleWindow a (2*q) z := by
  have H := atomicCellScale_comparable hnear
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left H.1 hq,h.1]
  · nlinarith [h.2]

lemma AtomicScaleWindow.mesh {a q : ℝ} {y z : Space} (h : AtomicScaleWindow a q y)
    (hq : 0 ≤ q) (hz : z∈atomicPatchMesh) : AtomicScaleWindow a (2*q) (atomicMeshCenter y z) :=
  h.near hq (by nlinarith [atomicMeshCenter_distance y z hz,atomicCellScale_nonneg y])

lemma AtomicScaleWindow.mesh_near {a q : ℝ} {y z v : Space} (h : AtomicScaleWindow a q y)
    (hq : 0 ≤ q) (hz : z∈atomicPatchMesh)
    (hv : ‖v-atomicMeshCenter y z‖ ≤ 2*atomicCellScale (atomicMeshCenter y z)) :
    AtomicScaleWindow a (4*q) v := by
  have H := (h.mesh hq hz).near (by positivity)
    (show ‖v-atomicMeshCenter y z‖ ≤ 82*atomicCellScale (atomicMeshCenter y z) by
      nlinarith [atomicCellScale_nonneg (atomicMeshCenter y z)])
  convert H using 1 <;> first | rfl | ring

lemma AtomicScaleWindow.mass {a q δ : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (ha : 0<a) (hq : 1 ≤ q) (hδ : 0 ≤ δ) :
    screenMass δ (atomicCellScale y) ≤ q^3*screenMass δ a :=
  screenMass_comparable hδ ha hq (h.div_lower (by linarith)) (by simpa only [mul_comm] using h.2)

lemma AtomicScaleWindow.energy {a q δ : ℝ} {y : Space} (h : AtomicScaleWindow a q y)
    (ha : 0<a) (hq : 1 ≤ q) (hδ : 0 ≤ δ) :
    screenEnergy δ (atomicCellScale y) ≤ q^7*screenEnergy δ a :=
  screenEnergy_comparable hδ ha hq (h.div_lower (by linarith)) (by simpa only [mul_comm] using h.2)

lemma totalCharge_nonneg {J : ℕ} (S : Nuclei J) : 0 ≤ totalCharge S :=
  Finset.sum_nonneg (fun i _ => le_trans (by norm_num) (S.charge_ge_one i))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScreenNumeric
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def atomicIMSConstant : ℝ := 24*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*(radialCutCoefficient/40)^2
lemma atomicIMSConstant_nonneg : 0 ≤ atomicIMSConstant := by unfold atomicIMSConstant; positivity

lemma atomicIMS_le_units {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ P : ℝ} (hδ : 0 ≤ δ) (hP : 1 ≤ P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) {y : Space} (hy : y≠0) :
    atomicIMS ψ y ≤ atomicIMSConstant*P*screenEnergy δ (atomicCellScale y) := by
  have ha := atomicCellScale_pos hy
  have HB := atomicPatch_population ψ hm hδ (by linarith) hc hy
  change 3*(radialCutCoefficient/(40*atomicCellScale y))^2*expectedPopulation ψ _ ≤ _
  calc
    _ ≤ 3*(radialCutCoefficient/(40*atomicCellScale y))^2*
        ((Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8*Real.sqrt P*screenMass δ (atomicCellScale y)) :=
      mul_le_mul_of_nonneg_left HB (by positivity)
    _ = atomicIMSConstant*(Real.sqrt P*screenMass δ (atomicCellScale y)/(atomicCellScale y)^2) := by
      unfold atomicIMSConstant
      field_simp
      ring
    _ ≤ atomicIMSConstant*(P*(screenMass δ (atomicCellScale y))^2/atomicCellScale y) :=
      mul_le_mul_of_nonneg_left (screening_ims_units hP ha (screenMass_pos _ _).le (screenMass_scale δ ha)) atomicIMSConstant_nonneg
    _ = _ := by unfold screenEnergy; ring

lemma atomic_cell_cost_units {n : ℕ} {C : Type*} [Fintype C] (ψ : H1Vector n)
    {δ P a q G : ℝ} (hδ : 0 ≤ δ) (hP : 1 ≤ P) (ha : 0<a) (hq : 1 ≤ q) (hG : 0 ≤ G)
    (z : C → Space) (hz : ∀ c, AtomicScaleWindow a q (z c))
    (hc : ∀ v : Space, v≠0 → localCountSecondMoment ψ (Metric.closedBall v (atomicCellScale v)) ≤
      P*(screenMass δ (atomicCellScale v))^2) :
    (∑ c, (Real.sqrt (localCountSecondMoment ψ (Metric.closedBall (z c) (atomicCellScale (z c)))*
        (8*(screenFieldUnit δ P a*G)^2))+
        ((Fintype.card C:ℝ)*(∑ d, localCountSecondMoment ψ (Metric.closedBall (z d) (atomicCellScale (z d)))))/
          (3*atomicCellScale (z c)))) ≤
      P*q^7*screenEnergy δ a*(3*(Fintype.card C:ℝ)*G+(Fintype.card C:ℝ)^3) := by
  have hp0 : 0 ≤ P := by linarith
  have hq0 : 0<q := by linarith
  have he : 0 < screenEnergy δ a := screenEnergy_pos δ ha
  have hw : 0 < screenFieldUnit δ P a := screenFieldUnit_pos hP ha
  have hm0 : 0 < screenMass δ a := screenMass_pos δ a
  have hq37 : q^3 ≤ q^7 := pow_le_pow_right₀ hq (by omega)
  let L : ℝ := Fintype.card C
  let M : ℝ := screenMass δ a
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hM : 0<M := hm0
  have hmom (c) : localCountSecondMoment ψ (Metric.closedBall (z c) (atomicCellScale (z c))) ≤ P*q^6*M^2 := by
    have H := (hz c).mass ha hq hδ
    have HH := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (screenMass_pos _ _).le H 2) hp0
    calc
      _ ≤ P*(screenMass δ (atomicCellScale (z c)))^2 := hc _ ((hz c).nonzero ha)
      _ ≤ P*(q^3*M)^2 := HH
      _ = _ := by ring
  have hsum : (∑ d, localCountSecondMoment ψ (Metric.closedBall (z d) (atomicCellScale (z d)))) ≤ L*(P*q^6*M^2) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,L] using Finset.sum_le_sum (fun c (_ : c∈Finset.univ) => hmom c)
  have hsqrt (c) : Real.sqrt (localCountSecondMoment ψ (Metric.closedBall (z c) (atomicCellScale (z c)))*
      (8*(screenFieldUnit δ P a*G)^2)) ≤ 3*P*q^7*screenEnergy δ a*G := by
    have H := sqrt_count_raw_product hp0 (screenMass_pos δ (atomicCellScale (z c))).le hw.le hG
      (hc _ ((hz c).nonzero ha))
    calc
      _ ≤ 3*Real.sqrt P*screenMass δ (atomicCellScale (z c))*screenFieldUnit δ P a*G := H
      _ ≤ 3*Real.sqrt P*(q^3*M)*screenFieldUnit δ P a*G := by
        gcongr
        exact (hz c).mass ha hq hδ
      _ = 3*q^3*(P*screenEnergy δ a)*G := by
        have hu := screenFieldUnit_product (δ:=δ) (a:=a) hp0
        dsimp [M]
        calc
          _ = 3*q^3*(Real.sqrt P*screenMass δ a*screenFieldUnit δ P a)*G := by ring
          _ = _ := by rw [hu]
      _ ≤ _ := by
        have HH := mul_le_mul_of_nonneg_right hq37 (show 0 ≤ 3*P*screenEnergy δ a*G by positivity)
        nlinarith
  have hother (c) : (L*(∑ d, localCountSecondMoment ψ (Metric.closedBall (z d) (atomicCellScale (z d)))))/
      (3*atomicCellScale (z c)) ≤ L^2*P*q^7*screenEnergy δ a := by
    calc
      _ ≤ (L*(L*(P*q^6*M^2)))/(a/q) := by
        apply div_le_div₀
        · positivity
        · exact mul_le_mul_of_nonneg_left hsum hL
        · exact div_pos ha hq0
        · have H := (hz c).div_lower hq0
          linarith [atomicCellScale_nonneg (z c)]
      _ = _ := by unfold screenEnergy; dsimp [M]; field_simp
  calc
    _ ≤ ∑ _c : C, (3*P*q^7*screenEnergy δ a*G+L^2*P*q^7*screenEnergy δ a) :=
      Finset.sum_le_sum (fun c _ => add_le_add (hsqrt c) (hother c))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [L]; ring

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_AtomicBudgetScreening
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def atomicBudgetRawValues {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (B a w : ℝ) (j : ℕ) : Set ℝ :=
  insert 0 {r | ∃ k ≤ j, ∃ T : AtomicBudgetHistory S ψ B k,
    (∀ i, AtomicScaleWindow a (4^j) (T.target i)) ∧
    ∃ y, AtomicScaleWindow a (4^j) y ∧ r=Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y))/w}

def atomicBudgetRawSup {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (B a w : ℝ) (j : ℕ) : ℝ :=
  sSup (atomicBudgetRawValues S ψ B a w j)

lemma atomicBudgetRawValues_nonempty {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (B a w : ℝ) (j : ℕ) :
    (atomicBudgetRawValues S ψ B a w j).Nonempty := ⟨0,Set.mem_insert _ _⟩

def atomicBudgetRecursionA : ℝ := max 1 (16*ballTrialCoefficient*
  (2+atomicIMSConstant+4*ballTrialCoefficient+
    3*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)+
    (Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)^3))

def atomicBudgetRecursionC : ℝ := atomicBudgetRecursionA*524288

lemma atomicBudgetRecursionC_ge_four : 4 ≤ atomicBudgetRecursionC := by
  have h : 1 ≤ atomicBudgetRecursionA := le_max_left _ _
  unfold atomicBudgetRecursionC
  linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_BinaryEnsemble
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff
noncomputable section
namespace Coulomb

namespace RecordedEnsemble

def OutFermionic {n : ℕ} (T : RecordedEnsemble n) : Prop :=
  ∀ p, PartlyAntisymmetric (T.vector p) (outIndexSet (T.out p) (T.core p))
def CoreSupported {n : ℕ} (T : RecordedEnsemble n) (A : Set Space) : Prop :=
  ∀ p, PartlySupported (T.vector p) (coreIndexSet (T.out p) (T.core p)) A

theorem binary_localization {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ ∞ (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)|≤D)
    (A B : Set Space) (hA : ∀ z∉A, χ 0 z=0) (hB : ∀ z∉B, χ 1 z=0) :
    ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.OutFermionic ∧
      T.CoreSupported B ∧ T.OutSupported A ∧ T.totalMass=mass ψ ∧
      T.totalForm S=∑ p : Fin n → Fin 2, form S (ψ.labelCut χ hχ hp D hD hd p) := by
  have H (p : Fin n → Fin 2) := exists_binary_order p
  choose m k e he0 he1 using H
  let v (p : Fin n → Fin 2) := (ψ.labelCut χ hχ hp D hD hd p).reindex (e p)
  let T : RecordedEnsemble n := {
    index := Fin n → Fin 2
    finite := inferInstance
    out := m
    core := k
    vector := v
    labels := e }
  have hanti (p : Fin n → Fin 2) (I : Set (Fin (m p+k p))) (l : Fin 2)
      (hi : ∀ i∈I, p (e p i)=l) : PartlyAntisymmetric (v p) I := by
    let K : Set (Fin n) := {i | p i=l}
    have hc := (hψ.partly (Set.univ : Set (Fin n))).labelCut χ hχ hp D hD hd p K
      (Set.subset_univ _) l (fun _ h => h)
    exact hc.reindex (e p) I hi
  have hsupp (p : Fin n → Fin 2) (I : Set (Fin (m p+k p))) (l : Fin 2)
      (hi : ∀ i∈I, p (e p i)=l) (C : Set Space) (hC : ∀ z∉C, χ l z=0) :
      PartlySupported (v p) I C := by
    let K : Set (Fin n) := {i | p i=l}
    have hc := labelCut_partlySupported ψ χ hχ hp D hD hd p K l (fun _ h => h) C hC
    exact hc.reindex (e p) I hi
  refine ⟨T,?_,?_,?_,?_,?_,?_,?_⟩
  · intro W hW hbound
    dsimp [T,v]
    simp only [potentialForm_reindex]
    obtain ⟨M,hM⟩ := hbound
    exact potentialForm_labelCut ψ χ hχ hp D hD hd W hW hM
  · intro p
    exact hanti p (coreIndexSet (m p) (k p)) 1 (by rintro _ ⟨i,rfl⟩; exact he1 p i)
  · intro p
    exact hanti p (outIndexSet (m p) (k p)) 0 (by rintro _ ⟨i,rfl⟩; exact he0 p i)
  · intro p
    exact hsupp p (coreIndexSet (m p) (k p)) 1 (by rintro _ ⟨i,rfl⟩; exact he1 p i) B hB
  · intro p
    exact hsupp p (outIndexSet (m p) (k p)) 0 (by rintro _ ⟨i,rfl⟩; exact he0 p i) A hA
  · dsimp [totalMass,T,v]
    simp only [mass_reindex]
    exact mass_labelCut ψ χ hχ hp D hD hd
  · dsimp [totalForm,T,v]
    simp only [form_reindex]

end RecordedEnsemble
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ThinEnsemble
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma expectedPopulation_nonneg {n : ℕ} (ψ : H1Vector n) (A : Set Space) :
    0≤expectedPopulation ψ A := by
  apply Finset.sum_nonneg
  intro s hs
  apply Finset.sum_nonneg
  intro i hi
  exact integral_nonneg (fun x => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _))

lemma expectedPopulation_mono {n : ℕ} (ψ : H1Vector n) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A⊆B) :
    expectedPopulation ψ A≤expectedPopulation ψ B := by
  rw [expectedPopulation_eq ψ hA,expectedPopulation_eq ψ hB]
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun x => mul_nonneg (localCount_nonneg _ _) (sq_nonneg _))
  · simpa only [pow_one] using localCount_weight_integrable ψ hB s 1
  · exact Eventually.of_forall (fun x => mul_le_mul_of_nonneg_right (localCount_mono hAB x) (sq_nonneg _))

def thinIMS {n : ℕ} (ψ : H1Vector n) (y : Space) (t b : ℝ) : ℝ :=
  3*(thinCutCoefficient/b)^2*expectedPopulation ψ (Metric.closedBall y (t+b))

theorem thin_localization {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b) :
    ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.OutFermionic ∧
      T.CoreSupported {z | t≤‖z-y‖} ∧ T.OutSupported (Metric.closedBall y (t+b)) ∧
      T.totalMass=mass ψ ∧ T.totalForm S≤form S ψ+thinIMS ψ y t b := by
  obtain ⟨T,hC,hc,ho,hcs,hos,hm,hf⟩ := RecordedEnsemble.binary_localization S ψ hψ
    (thinCut y t b) (thinCut_smooth y t b) (thinCut_partition y t b)
    (thinCutCoefficient/b) (div_nonneg thinCutCoefficient_pos.le hb.le)
    (thinCut_derivative_bound y ht hb) (Metric.closedBall y (t+b)) {z | t≤‖z-y‖}
    (fun z hz => thinCut_out_zero y ht hb z (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using (show t+b≤‖z-y‖ from le_of_lt (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hz))))
    (fun z hz => thinCut_core_zero y ht hb z (le_of_lt (by simpa only [Set.mem_ofPred_eq,not_le] using hz)))
  refine ⟨T,hC,hc,ho,hcs,hos,hm,?_⟩
  rw [hf]
  exact form_thin_labelCut S ψ y ht hb

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_AtomicThinCounts
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def atomicPatchCountFactor : ℝ := (Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)^2*64
lemma atomicPatchCountFactor_nonneg : 0≤atomicPatchCountFactor := by unfold atomicPatchCountFactor; positivity

lemma atomicPatch_secondMoment {n : ℕ} (ψ : H1Vector n)
    {δ P : ℝ} (hδ : 0≤δ) (hP : 0≤P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z))≤
      P*(screenMass δ (atomicCellScale z))^2) {y : Space} (hy : y≠0) :
    localCountSecondMoment ψ (Metric.closedBall y (80*atomicCellScale y))≤
      atomicPatchCountFactor*P*(screenMass δ (atomicCellScale y))^2 := by
  let A := fun z : {z : Space // z∈atomicPatchMesh} =>
    Metric.closedBall (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val))
  have hcover : Metric.closedBall y (80*atomicCellScale y) ⊆ ⋃ z, A z := by
    intro x hx
    obtain ⟨z,hz,hzx⟩ := atomicMesh_cover hy x (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,by simpa only [A,Metric.mem_closedBall,dist_eq_norm] using hzx⟩
  have HE (z : {z : Space // z∈atomicPatchMesh}) : localCountSecondMoment ψ (A z)≤
      64*P*(screenMass δ (atomicCellScale y))^2 := by
    have hz : atomicMeshCenter y z.val≠0 := atomicCellScale_near_nonzero hy
      (by nlinarith [atomicMeshCenter_distance y z.val z.property,atomicCellScale_nonneg y])
    have hu := atomicMeshCenter_comparable y z.val z.property
    have Hm := screenMass_comparable hδ (atomicCellScale_pos hy) (show (1:ℝ)≤2 by norm_num) hu.1 (by linarith [hu.2])
    norm_num at Hm
    apply (hc _ hz).trans
    have HS := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (screenMass_pos δ _).le Hm 2) hP
    nlinarith
  calc
    _≤(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*∑ z, localCountSecondMoment ψ (A z) :=
      localCountSecondMoment_cover ψ A (fun _ => measurableSet_closedBall) hcover
    _≤(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*∑ _ : {z : Space // z∈atomicPatchMesh},
        64*P*(screenMass δ (atomicCellScale y))^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => HE z)) (Nat.cast_nonneg _)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,atomicPatchCountFactor]; ring

lemma exists_atomic_deletedShell {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ : ℝ} (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y) :
    ∃ t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
      localCountSecondMoment ψ (deletedShell y t b)≤
        18*atomicPatchCountFactor*(b/atomicCellScale y)*screenCountParameter ψ δ*
          (screenMass δ (atomicCellScale y))^2 := by
  obtain ⟨t,ht,H⟩ := exists_deletedShell_small ψ y (atomicCellScale_pos hy) hb hsmall
  refine ⟨t,ht,H.trans ?_⟩
  have HP := atomicPatch_secondMoment ψ hδ (le_trans zero_le_one (screenCountParameter_ge_one ψ δ))
    (fun _ hz => screenCountParameter_controls ψ hm δ hz) hy
  have HM := localCountSecondMoment_mono ψ (A:=Metric.closedBall y (7*atomicCellScale y)) measurableSet_closedBall
    (Metric.closedBall_subset_closedBall (show 7*atomicCellScale y≤80*atomicCellScale y by nlinarith [atomicCellScale_nonneg y]))
  have Hmul := mul_le_mul_of_nonneg_left (HM.trans HP)
    (show 0≤18*b/atomicCellScale y from div_nonneg (by positivity) (atomicCellScale_nonneg y))
  convert Hmul using 1
  all_goals try with_reducible_and_instances rfl
  ring

def thinReserveFactor : ℝ := max 1 (3*thinCutCoefficient^2*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8)
lemma thinReserveFactor_ge_one : 1≤ thinReserveFactor := le_max_left _ _
lemma thinReserveFactor_nonneg : 0≤ thinReserveFactor := le_trans zero_le_one thinReserveFactor_ge_one

lemma thinIMS_budget {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ P : ℝ} (hδ : 0≤δ) (hP : 1≤P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z))≤
      P*(screenMass δ (atomicCellScale z))^2)
    {y : Space} (hy : y≠0) {t b : ℝ} (hb : 0<b) (hwidth : t+b≤80*atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt P*screenMass δ (atomicCellScale y)) :
    thinIMS ψ y t b≤ thinReserveFactor*P*screenEnergy δ (atomicCellScale y) := by
  have hP0 : 0≤P := le_trans zero_le_one hP
  have ha := atomicCellScale_pos hy
  have hm0 := screenMass_pos δ (atomicCellScale y)
  have H := (expectedPopulation_mono ψ measurableSet_closedBall measurableSet_closedBall
    (Metric.closedBall_subset_closedBall hwidth)).trans (atomicPatch_population ψ hm hδ hP0 hc hy)
  have Hims := mul_le_mul_of_nonneg_left H (show 0≤3*(thinCutCoefficient/b)^2 by positivity)
  have HC : 3*thinCutCoefficient^2*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8≤ thinReserveFactor := le_max_right _ _
  have HU : 3*(thinCutCoefficient/b)^2*((Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8*Real.sqrt P*screenMass δ (atomicCellScale y))≤
      thinReserveFactor*(Real.sqrt P*screenMass δ (atomicCellScale y)/b^2) := by
    calc
      _=(3*thinCutCoefficient^2*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8)*
          (Real.sqrt P*screenMass δ (atomicCellScale y)/b^2) := by rw [div_pow]; ring
      _≤_ := mul_le_mul_of_nonneg_right HC (by positivity)
  have Hscale : Real.sqrt P*screenMass δ (atomicCellScale y)/b^2≤P*screenEnergy δ (atomicCellScale y) := by
    apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
    rw [screenEnergy,←mul_div_assoc,div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    have Hc := mul_le_mul_of_nonneg_right hcond (mul_nonneg (Real.sqrt_nonneg P) hm0.le)
    have Hr : (Real.sqrt P*screenMass δ (atomicCellScale y))^2=P*(screenMass δ (atomicCellScale y))^2 := by
      rw [mul_pow,Real.sq_sqrt hP0]
    nlinarith [mul_le_mul_of_nonneg_left Hr.le (sq_nonneg b),
      mul_le_mul_of_nonneg_left Hr.ge (sq_nonneg b)]
  exact Hims.trans (HU.trans (by nlinarith [mul_le_mul_of_nonneg_left Hscale thinReserveFactor_nonneg]))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_AtomicThinScreening
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def RecordedEnsemble.deletedSquare {n : ℕ} (T : RecordedEnsemble n) (y : Space) (t b : ℝ) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount {z | t-7*b≤‖z-y‖} x)^2)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ExactRecordedCount
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma localCount_eq_zero_of_allPositions {n : ℕ} {A B : Set Space} (hAB : Disjoint A B)
    {x : Configuration n} (hx : x∈allPositions A) : localCount B x=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply indicator_of_notMem
  exact fun h => Set.disjoint_left.mp hAB (hx i) h

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_PhysicalEnsemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma PartlyAntisymmetric.outer_symmetry {m k : ℕ} {u : H1Vector (m+k)}
    (hu : PartlyAntisymmetric u (outIndexSet m k))
    (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m) :
    ∀ᵐ z, u.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
      (((outerPerm k p).sign:ℤ):ℂ)*u.value (outerAppend s t) z := by
  apply hu
  intro i
  refine Fin.addCases (fun j hi => ?_) (fun j _ => ?_) i
  · exact False.elim (hi ⟨j,rfl⟩)
  · exact outerPerm_right k p j

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_AnnularCut
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

def annularAngle (u : ℝ) (x : Space) : ℝ := cutAngle 0 (2*u) x-cutAngle 0 (u/2) x

def annularCut (u : ℝ) (l : Fin 2) (x : Space) : ℝ :=
  if l=0 then Real.sin (annularAngle u x) else Real.cos (annularAngle u x)

lemma annularAngle_smooth (u : ℝ) : ContDiff ℝ ∞ (annularAngle u) :=
  (cutAngle_smooth 0 (2*u)).sub (cutAngle_smooth 0 (u/2))

lemma annularCut_smooth (u : ℝ) (l : Fin 2) : ContDiff ℝ ∞ (annularCut u l) := by
  unfold annularCut
  split_ifs
  · exact (annularAngle_smooth u).sin
  · exact (annularAngle_smooth u).cos

lemma annularCut_partition (u : ℝ) (x : Space) : ∑ l : Fin 2, annularCut u l x^2=1 := by
  simp [Fin.sum_univ_two,annularCut]

lemma cutAngle_derivative_bound (y : Space) {r : ℝ} (hr : 0 < r) (b : Fin 3) (x : Space) :
    |fderiv ℝ (cutAngle y r) x (EuclideanSpace.single b 1)| ≤ radialCutCoefficient/r := by
  rw [cutAngle_fderiv,abs_mul,abs_of_pos (mul_pos (by positivity) (inv_pos.mpr hr))]
  have H := ((fderiv ℝ cutSeed (r⁻¹ • (x-y))).le_opNorm (EuclideanSpace.single b 1)).trans
    (mul_le_mul_of_nonneg_right (norm_cutSeed_derivative _) (norm_nonneg _))
  simp only [PiLp.norm_single,norm_one,mul_one,Real.norm_eq_abs] at H
  calc
    _ ≤ (Real.pi/2)*r⁻¹*cutSeedDerivativeBound := mul_le_mul_of_nonneg_left H (by positivity)
    _ = _ := by unfold radialCutCoefficient; ring

lemma annularAngle_derivative_bound {u : ℝ} (hu : 0<u) (b : Fin 3) (x : Space) :
    |fderiv ℝ (annularAngle u) x (EuclideanSpace.single b 1)| ≤ 3*radialCutCoefficient/u := by
  have h1 := cutAngle_derivative_bound 0 (by positivity : 0<2*u) b x
  have h2 := cutAngle_derivative_bound 0 (by positivity : 0<u/2) b x
  have hd1 := (cutAngle_smooth 0 (2*u)).differentiable (by simp) x
  have hd2 := (cutAngle_smooth 0 (u/2)).differentiable (by simp) x
  change |fderiv ℝ (cutAngle 0 (2*u) - cutAngle 0 (u/2)) x _|≤_
  rw [fderiv_sub hd1 hd2,sub_apply]
  have H := (abs_sub _ _).trans (add_le_add h1 h2)
  have he : radialCutCoefficient/(2*u)+radialCutCoefficient/(u/2)=(5/2)*radialCutCoefficient/u := by ring
  rw [he] at H
  simp only [mul_div_assoc] at H ⊢
  nlinarith [div_nonneg radialCutCoefficient_pos.le hu.le]

lemma annularCut_derivative_bound {u : ℝ} (hu : 0<u) (l : Fin 2) (b : Fin 3) (x : Space) :
    |fderiv ℝ (annularCut u l) x (EuclideanSpace.single b 1)| ≤ 3*radialCutCoefficient/u := by
  have hb := annularAngle_derivative_bound hu b x
  unfold annularCut
  split_ifs
  · rw [fderiv_sin ((annularAngle_smooth u).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans (by simpa using hb)
  · rw [fderiv_cos ((annularAngle_smooth u).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans (by simpa using hb)

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalBridge
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

def flattenConfiguration (n : ℕ) : Configuration n ≃L[ℝ] Coulomb.Configuration n :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => WithLp.toLp 2 (fun ia => x ia.1 ia.2)
    invFun := fun x i => Coulomb.position x i
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }

@[simp] lemma flattenConfiguration_apply (n : ℕ) (x : Configuration n) (i : Fin n) (a : Fin 3) :
    flattenConfiguration n x (i,a) = x i a := rfl
@[simp] lemma flattenConfiguration_symm_apply (n : ℕ) (x : Coulomb.Configuration n) (i : Fin n) :
    (flattenConfiguration n).symm x i = Coulomb.position x i := rfl

@[simp] lemma position_flattenConfiguration {n : ℕ} (x : Configuration n) (i : Fin n) :
    Coulomb.position (flattenConfiguration n x) i = x i := rfl

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_TailMoment
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def radialTailKernel (r : ℝ) (x : Space) : ℝ := if r ≤ ‖x‖ then ‖x‖⁻¹ else 0

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_AtomicPatchCap
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def atomicPatchCap {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) : ℝ :=
  Real.sqrt (∑ z : {z : Space // z∈atomicPatchMesh},
    (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2)+
      2*(m:ℝ)/(3*atomicCellScale y)

lemma atomicPatchCap_nonneg {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {y : Space} (hy : y≠0) : 0≤atomicPatchCap S u x y := by
  have ha := atomicCellScale_pos hy
  unfold atomicPatchCap
  positivity

lemma atomicPatchCap_square_le {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) : (atomicPatchCap S u x y)^2≤
      2*∑ z : {z : Space // z∈atomicPatchMesh},
        (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2+
      8*(m:ℝ)^2/(9*(atomicCellScale y)^2) := by
  have hs := Real.sq_sqrt (x := ∑ z : {z : Space // z∈atomicPatchMesh},
    (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2)
    (Finset.sum_nonneg (fun z _ => sq_nonneg
    (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))))
  unfold atomicPatchCap
  have H := sq_nonneg (Real.sqrt (∑ z : {z : Space // z∈atomicPatchMesh},
    (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2)-
      2*(m:ℝ)/(3*atomicCellScale y))
  rw [show 8*(m:ℝ)^2/(9*(atomicCellScale y)^2)=2*(2*(m:ℝ)/(3*atomicCellScale y))^2 by ring]
  nlinarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_SharpThinScreening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

theorem thin_localization_history_sharp {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    {y : Space} (hy : y≠0) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (hwidth : t+b≤80*atomicCellScale y) :
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      (∀ i, T.target i=y) ∧ T.ensemble.OutFermionic ∧
      T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t b := by
  obtain ⟨U,hC,hc,ho,hcs,hos,hm,hf⟩ := thin_localization S ψ hψ y ht hb
  let T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1 := {
    ensemble := U
    target := fun _ => y
    nonzero := fun _ => hy
    law := hC
    fermionic := hc
    support := by
      intro p
      apply (hos p).mono_space
      intro z hz
      apply Set.mem_iUnion.mpr
      refine ⟨0,?_⟩
      exact Metric.closedBall_subset_closedBall hwidth hz
    mass_eq := hm
    energy := by
      apply hf.trans
      apply le_add_of_nonneg_right
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (expectedPopulation_nonneg _ _)) }
  exact ⟨T,fun _ => rfl,ho,hcs,hos,hf⟩

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

def atomicPhysicalCapConstant : ℝ :=
  16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
    (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor)^2+8*atomicPatchCountFactor/9

lemma atomicPhysicalCapConstant_nonneg : 0≤atomicPhysicalCapConstant := by
  unfold atomicPhysicalCapConstant
  positivity [atomicPatchCountFactor_nonneg]

def atomicComparisonExpression (δ P a b : ℝ) : ℝ :=
  2*(tfInteriorCountConstant/a^3)^2+6*a*max countTestEnergy 0*
    ((δ+thinReserveFactor*(Real.sqrt P*screenMass δ a/b^2))+
      12*a*unitWindowKinetic/b^2*Real.sqrt (atomicPhysicalCapConstant*P*(screenMass δ a)^2/a^2)+
      Real.sqrt ((atomicPhysicalCapConstant*P*(screenMass δ a)^2/a^2)*
        (18*atomicPatchCountFactor*(b/a)*P*(screenMass δ a)^2))+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(atomicPatchCountFactor*P*(screenMass δ a)^2)^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (atomicPatchCountFactor*P*(screenMass δ a)^2))

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CountScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

def countBootstrapA : ℝ := 2*tfInteriorCountConstant^2+6*max countTestEnergy 0
 def countBootstrapB : ℝ := 6*max countTestEnergy 0*Real.sqrt (18*atomicPhysicalCapConstant*atomicPatchCountFactor)
 def countBootstrapC : ℝ := 6*max countTestEnergy 0*(thinReserveFactor+12*unitWindowKinetic*Real.sqrt atomicPhysicalCapConstant)
 def countBootstrapD : ℝ := 3*max countTestEnergy 0*(2*Real.pi+1)*Real.sqrt atomicPatchCountFactor
 def countBootstrapE : ℝ := 6*max countTestEnergy 0*((Real.pi^2/2)*neumannBoundary)*atomicPatchCountFactor^(2/3:ℝ)

def countBootstrapMajorant (β P : ℝ) : ℝ := countBootstrapA+countBootstrapB*Real.sqrt β*P+
  (countBootstrapC/β^2+countBootstrapD/β)*Real.sqrt P+countBootstrapE/β^2*P^(2/3:ℝ)

lemma atomicComparisonExpression_le_majorant {δ P a β : ℝ} (hδ : 0 ≤ δ) (hP : 0 ≤ P)
    (ha : 0 < a) (hβ : 0 < β) :
    atomicComparisonExpression δ P a (β*a) ≤ countBootstrapMajorant β P*(screenMass δ a)^2 := by
  let m := screenMass δ a
  let M := max countTestEnergy 0
  let C := atomicPhysicalCapConstant
  let D := atomicPatchCountFactor
  have hm : 0  <  m := screenMass_pos δ a
  have hM : 0 ≤ M := le_max_right _ _
  have hC : 0 ≤ C := atomicPhysicalCapConstant_nonneg
  have hD : 0 ≤ D := atomicPatchCountFactor_nonneg
  have hK : 0 ≤ unitWindowKinetic := unitWindowKinetic_nonneg
  have hN : 0 ≤ neumannBoundary := neumannBoundary_nonneg
  have hR : 0 ≤ thinReserveFactor := thinReserveFactor_nonneg
  have h1 : 2*(tfInteriorCountConstant/a^3)^2 ≤ 2*tfInteriorCountConstant^2*m^2 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ (a^3)⁻¹)
      (screenMass_inv_cube_le δ a) 2) (show 0 ≤ 2*tfInteriorCountConstant^2 by positivity)
    simpa only [m, div_pow, div_eq_mul_inv, inv_pow, mul_pow, mul_assoc] using H
  have h2 : 6*a*M*δ ≤ 6*M*m^2 := by
    have H := (le_div_iff₀ ha).mp (screenEnergy_ge_offset hδ ha)
    change δ*a ≤ m^2 at H
    nlinarith [mul_le_mul_of_nonneg_left H (show 0 ≤ 6*M by positivity)]
  have h3 := mul_le_mul_of_nonneg_left (screenMass_pairscale δ ha)
    (show 0 ≤ 6*M*thinReserveFactor/β^2*Real.sqrt P by positivity)
  have h4 := mul_le_mul_of_nonneg_left (screenMass_pairscale δ ha)
    (show 0 ≤ 72*M*unitWindowKinetic*Real.sqrt C/β^2*Real.sqrt P by positivity)
  have h5 := mul_le_mul_of_nonneg_left (screenMass_kinetic_scale δ ha)
    (show 0 ≤ 6*M*((Real.pi^2/2)*neumannBoundary)*D^(2/3:ℝ)/β^2*P^(2/3:ℝ) by positivity)
  have h6 := mul_le_mul_of_nonneg_left (screenMass_square_ge δ a)
    (show 0 ≤ 3*M*(2*Real.pi+1)*Real.sqrt D/β*Real.sqrt P by positivity [Real.pi_pos])
  have he : atomicComparisonExpression δ P a (β*a)=
      2*(tfInteriorCountConstant/a^3)^2+6*a*M*δ+
      (6*M*thinReserveFactor/β^2*Real.sqrt P)*(m/a)+
      (72*M*unitWindowKinetic*Real.sqrt C/β^2*Real.sqrt P)*(m/a)+
      (6*M*Real.sqrt (18*C*D)*Real.sqrt β*P)*m^2+
      (6*M*((Real.pi^2/2)*neumannBoundary)*D^(2/3:ℝ)/β^2*P^(2/3:ℝ))*(m^(4/3:ℝ)/a)+
      (3*M*(2*Real.pi+1)*Real.sqrt D/β*Real.sqrt P)*m := by
    unfold atomicComparisonExpression
    rw [sqrt_cap_expression hC hP hm.le ha,sqrt_deleted_expression hC hD hP hm.le ha hβ.le,
      sqrt_out_expression hD hP hm.le,fine_count_expression hD hP hm.le]
    dsimp only [M,C,D,m]
    field_simp
    ring
  rw [he]
  have HH := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) (le_refl ((6*M*Real.sqrt (18*C*D)*Real.sqrt β*P)*m^2))) h5) h6
  apply HH.trans_eq
  unfold countBootstrapMajorant countBootstrapA countBootstrapB countBootstrapC countBootstrapD countBootstrapE
  dsimp only [M,C,D,m]
  ring

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_UniformCountConsequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma atomicCellScale_smul {u : ℝ} (hu : 0 ≤ u) (z : Space) :
    atomicCellScale (u • z)=u*atomicCellScale z := by
  simp only [atomicCellScale,norm_smul,Real.norm_eq_abs,abs_of_nonneg hu]
  ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_UniformScreening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def AtomicBudgetHistory.initial {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) : AtomicBudgetHistory S ψ 0 0 where
  ensemble := RecordedEnsemble.initial ψ
  target := Fin.elim0
  nonzero := fun i => Fin.elim0 i
  law := RecordedEnsemble.initial_conserves ψ
  fermionic := RecordedEnsemble.initial_fermionic ψ hψ
  support := by simpa only [atomicPatchRegion,Set.iUnion_of_empty] using RecordedEnsemble.initial_supported ψ
  mass_eq := RecordedEnsemble.initial_mass ψ
  energy := by simp only [RecordedEnsemble.initial_form,Finset.univ_eq_empty,Finset.sum_empty,add_zero,le_refl]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RecordedStatistic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def arrayStatistic {n : ℕ} (χ : Space → ℝ) (x : Configuration n) : ℝ :=
  ∑ i, χ (position x i)

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_AnnularAddback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def annularAddbackKernel (h u : ℝ) (z : Space) : ℝ :=
  (5000/u)*{v : Space | h≤‖v‖ ∧ ‖v‖<8*u}.indicator (fun _ => (1:ℝ)) z+
    2*radialTailKernel (8*u) z

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_AnnularIMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

def annularBand (u : ℝ) : Set Space := {x | u/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 4*u}

def annularIMSCost {n : ℕ} (ψ : H1Vector n) (u : ℝ) : ℝ :=
  3*(3*radialCutCoefficient/u)^2*expectedPopulation ψ (annularBand u)

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalRMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

namespace RecordedEnsemble
variable {n : ℕ}
def dataRMS (T : RecordedEnsemble n)
    (F : (p : T.index) → Spins (T.out p) → Configuration (T.out p) → ℝ) : ℝ :=
  Real.sqrt (∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))

end RecordedEnsemble
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_InnerFieldRMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

namespace RecordedEnsemble
variable {n : ℕ}

def innerSquare {J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J) (h : ℝ) (y : Space) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun s x =>
    (max (coreConditionalObservable (T.vector p)
      (rawSignedField (attraction S y) (Metric.ball 0 h) y) s x) 0)^2)

end RecordedEnsemble
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_InnerMeshCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

namespace RecordedEnsemble
variable {n J : ℕ}

structure InnerEnvelope (T : RecordedEnsemble n) (S : Nuclei J) (h u : ℝ) where
  value : (p : T.index) → Spins (T.out p) → Configuration (T.out p) → ℝ
  nonneg : ∀ p s x, 0≤value p s x
  measurable : ∀ p s, AEStronglyMeasurable (value p s) volume
  integrable : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*value p s x)
  square_integrable : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(value p s x)^2)
  dominates : ∀ p s x w, u≤‖w‖ → ‖w‖≤2*u →
    max (recordedFarField S ((T.vector p).coreSlice s x).normalized x (Metric.ball 0 h) w) 0 ≤ value p s x

end RecordedEnsemble
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_BinaryDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

namespace RecordedEnsemble

def totalCoreForm {J n : ℕ} (T : RecordedEnsemble n) (S : Nuclei J) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun s x => form S ((T.vector p).coreSlice s x).normalized)

end RecordedEnsemble
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoreCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

namespace RecordedEnsemble

def coreMean {n : ℕ} (T : RecordedEnsemble n) : ℝ := ∑ p, (T.core p:ℝ)*mass (T.vector p)
def coreDeficitMoment {n : ℕ} (T : RecordedEnsemble n) (Z : ℝ) : ℝ :=
  ∑ p, (max (Z-(T.core p:ℝ)) 0)^2*mass (T.vector p)
def favorableMass {n : ℕ} (T : RecordedEnsemble n) (Z : ℝ) : ℝ :=
  ∑ p, if (T.core p:ℝ)<Z then mass (T.vector p) else 0

end RecordedEnsemble
end Coulomb
end

end

end OAI
end


