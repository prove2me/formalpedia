-- Prove2me | Definitions.Def_OAIQ062C006
-- name    : OAIQ062C006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:05:22.536992+00:00
-- url     : https://prove2.me/theorems/307ec41b-4e7e-4c3f-ae7a-ef048e4807ea
-- title:
--   Definitions bundle OAIQ062C006 of the split of OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 225 declarations of OpenAI's Lean: 6 definitions, 1 instance and 218 theorems. The definitions and types are `OAI.Coulomb.atomicWeight`, `OAI.Coulomb.conditionalEnergy`, `OAI.Coulomb.coreTFField`, `OAI.Coulomb.fineDensityPower`, `OAI.Coulomb.rotatedFlatDensity`, `OAI.Coulomb.tfGradientField`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombRadii_FieldAnalysis_AtomicWeighted`, `CoulombRadii_FieldAnalysis_ComplexMollify`, `CoulombRadii_FieldAnalysis_CoreCoulombPotential`, `CoulombRadii_FieldAnalysis_CubeLabelEquiv`, `CoulombRadii_FieldAnalysis_CubeMeasure`, `CoulombRadii_FieldAnalysis_DeterminantWave`, `CoulombRadii_FieldAnalysis_FarSubmean`, `CoulombRadii_FieldAnalysis_FieldSubmean`, `CoulombRadii_FieldAnalysis_GroupFermionicCoefficients`, `CoulombRadii_FieldAnalysis_IntegrableIntegralAeTendsto`, `CoulombRadii_FieldAnalysis_JoinSpins`, `CoulombRadii_FieldAnalysis_LeftPotential`, `CoulombRadii_FieldAnalysis_NormSqSumCosets`, `CoulombRadii_FieldAnalysis_OuterJoinConfiguration`, `CoulombRadii_FieldAnalysis_PositiveField`, `CoulombRadii_FieldAnalysis_RawObservable`, `CoulombRadii_FieldAnalysis_RawThomasFermiEnergy`, `CoulombRadii_FieldAnalysis_RetainedFineDensity`, `CoulombRadii_FieldAnalysis_RetainedFineDensityConfigurationMeasurable`, `CoulombRadii_FieldAnalysis_RetainedFinePower`, `CoulombRadii_FieldAnalysis_RotatedDensityPower`, `CoulombRadii_FieldAnalysis_Rotation`, `CoulombRadii_FieldAnalysis_SliceExpectation`, `CoulombRadii_FieldAnalysis_SpinMode`, `CoulombRadii_FieldAnalysis_SumSpinDuplicate`, `CoulombRadii_FieldAnalysis_UnitNucleus`, `CoulombRadii_FieldAnalysis_WedgeMultiplicity`, `CoulombRadii_FieldAnalysis_WeightedExchangeAlgebra`, `CoulombRadii_FormDomain_BallTrial`, `CoulombRadii_FormDomain_CoreKinetic`, `CoulombRadii_FormDomain_OrbitalHilbertBasis`, `CoulombRadii_FormDomain_PatchErrors`, `CoulombRadii_FormDomain_PhysicalEnsemble`, `CoulombRadii_FormDomain_Pullback`, `CoulombRadii_FormDomain_SmoothCompact`, `CoulombRadii_FormDomain_TfGradientField`, `CoulombRadii_Localization_DeletedLabels`, `CoulombRadii_Localization_DensityCut`, `CoulombRadii_Localization_Partial`, `CoulombRadii_Localization_RadialAppend`, `CoulombRadii_Packets_CoreScreenedFieldPacketIntegral`, `CoulombRadii_Packets_FineKernelShiftCoulombIntegrable`, `CoulombRadii_Packets_PacketDensityReal`, `CoulombRadii_Packets_PacketIndex`, `CoulombRadii_Packets_PacketSynthesisIndicator`, `CoulombRadii_Packets_PacketWindowed`, `CoulombRadii_Packets_WindowCoulomb`, `CoulombRadii_Propagation_EnsembleMoments`, `CoulombRadii_Propagation_NuclearPotential`, `CoulombRadii_Propagation_NuclearPotentialSplitJoin`, `CoulombRadii_RandomFields_AtomicThinScreening`, `CoulombRadii_RandomFields_ConditionalEnergy`, `CoulombRadii_RandomFields_ConditionalPositiveField`, `CoulombRadii_RandomFields_EnsembleCoveredCost`, `CoulombRadii_RandomFields_ExactRecordedCount`, `CoulombRadii_RandomFields_JointSlice`, `CoulombRadii_RandomFields_LocalizedEnsemble`, `CoulombRadii_RandomFields_RawCap`, `CoulombRadii_RandomFields_RecordedCount`, `CoulombRadii_RandomFields_RecordedEnsemble`, `CoulombRadii_Screening_AtomicBudgetHistory`, `CoulombRadii_Screening_AtomicBudgetScreening`, `CoulombRadii_Screening_AtomicCapRaw`, `CoulombRadii_Screening_AtomicPatchCap`, `CoulombRadii_Screening_CoreScreenedField`, `CoulombRadii_Screening_CoveredOutCost`, `CoulombRadii_Screening_FineCountTest`, `CoulombRadii_Screening_OutCap`, `CoulombRadii_Screening_PatchComparison`, `CoulombRadii_Screening_ScaledTest`, `CoulombRadii_Screening_SharpThinScreening`, `CoulombRadii_SpectralTheory_SectorFormBottom`, `CoulombRadii_ThomasFermi_LpParameter`, `CoulombRadii_ThomasFermi_PacketFrame`, `CoulombRadii_ThomasFermi_PhysicalCount`, `CoulombRadii_ThomasFermi_TFCountTest`, `CoulombRadii_ThomasFermi_TFInterior`, `CoulombRadii_ThomasFermi_TfExtendNonneg`, `CoulombRadii_ThomasFermi_TfPotential`.
--
--   **Imports.** It imports the bundles `OAIQ062C003`, `OAIQ062C004` and `OAIQ062C005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ062C008`; the proofs of `OAI.Coulomb.strictly_bound_sequence_tight` and `OAI.NeutralAtom.atomic_global_master_potential`.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ062C003
import Definitions.Def_OAIQ062C004
import Definitions.Def_OAIQ062C005

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_OrbitalHilbertBasis
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

lemma spinOrbital_orthonormal {ι : Type*} (v : ι → Space → ℂ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x) = if i = j then (1 : ℂ) else 0) :
    ∀ i j : ι × Fin 2, (∑ s, ∫ x, star (spinOrbital v i x s) * spinOrbital v j x s) =
      if i = j then (1 : ℂ) else 0 := by
  intro i j
  by_cases ht : i.2 = j.2
  · have hm : ∀ s x, star (spinOrbital v i x s) * spinOrbital v j x s =
        if s = i.2 then star (v i.1 x) * v j.1 x else 0 := by
      intro s x
      by_cases hs : s = i.2 <;> simp [spinOrbital, ← ht, hs]
    simp_rw [hm]
    have hi : ∀ s : Fin 2, (∫ x, if s = i.2 then star (v i.1 x) * v j.1 x else 0) =
        if s = i.2 then (∫ x, star (v i.1 x) * v j.1 x) else 0 := by
      intro s
      split_ifs <;> simp
    simp_rw [hi]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [ho]
    congr 1
    exact propext ⟨fun h => Prod.ext h ht, fun h => congrArg Prod.fst h⟩
  · have he : i ≠ j := fun h => ht (congrArg Prod.snd h)
    rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hi : s = i.2
    · have hj : s ≠ j.2 := by rwa [hi]
      simp only [spinOrbital, ite_eq_left hi, ite_eq_right hj, mul_zero, integral_zero]
    · simp only [spinOrbital, ite_eq_right hi, star_zero, zero_mul, integral_zero]

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_DeterminantWave
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
namespace Coulomb

lemma determinantWave_norm_sq {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    (∫ x, ‖determinantWave v x‖^2 ∂(Measure.pi fun _ : Fin n => μ)) = n.factorial := by
  let T (p : Equiv.Perm (Fin n)) : Lp ℂ 2 (Measure.pi fun _ : Fin n => μ) :=
    (scalarTensor_memLp v hv p).toLp (fun x : Fin n → A => ∏ i, v (p i) (x i))
  have hT : Orthonormal ℂ T := by
    rw [orthonormal_iff_ite]
    intro p q
    change inner ℂ ((scalarTensor_memLp v hv p).toLp _)
      ((scalarTensor_memLp v hv q).toLp _) = _
    rw [inner_toLp_complex]
    rw [scalarTensor_orthonormal v (fun i j => by
      by_cases h : i = j
      · simpa only [ite_eq_left h] using ho i j
      · simpa only [ite_eq_right h] using ho i j)]
    by_cases h : p = q
    · subst q; simp
    · have hfun : (p : Fin n → Fin n) ≠ q := fun he => h (Equiv.ext (congrFun he))
      simp only [ite_eq_right h, ite_eq_right hfun]
  let hD := determinantWave_memLp v hv
  have hsum : hD.toLp (determinantWave v) =
      ∑ p, (((p.sign : ℤ) : ℂ)) • T p := by
    apply Lp.ext
    filter_upwards [hD.coeFn_toLp, Lp.coeFn_fun_finsetSum
      (s := Finset.univ) (f := fun p : Equiv.Perm (Fin n) => (((p.sign : ℤ) : ℂ)) • T p),
      ae_all_iff.mpr (fun p : Equiv.Perm (Fin n) =>
        (scalarTensor_memLp v hv p).coeFn_toLp),
      ae_all_iff.mpr (fun p : Equiv.Perm (Fin n) =>
        Lp.coeFn_smul (((p.sign : ℤ) : ℂ)) (T p))] with x hx hsum ht hsmul
    rw [hx, hsum, determinantWave_expansion]
    apply Finset.sum_congr rfl
    intro p _
    rw [hsmul p]
    simp only [Pi.smul_apply, smul_eq_mul, T, ht p]
  apply Complex.ofReal_injective
  rw [← norm_toLp_sq_complex hD]
  calc
    (↑(‖hD.toLp (determinantWave v)‖^2) : ℂ) =
        inner ℂ (hD.toLp (determinantWave v)) (hD.toLp (determinantWave v)) := by
      simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    _ = ∑ p : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((p.sign : ℤ) : ℂ)) := by
      rw [hsum]
      exact hT.inner_sum _ _ Finset.univ
    _ = ↑(n.factorial : ℝ) := by
      simp only [sign_star_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      norm_cast
      simpa only [Fintype.card_fin] using (Fintype.card_perm (α := Fin n))

lemma slaterWave_normalized {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    (∫ x, ‖slaterWave v x‖^2 ∂(Measure.pi fun _ : Fin n => μ)) = 1 := by
  have hn : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  simp only [slaterWave, norm_mul, mul_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), integral_const_mul,
    determinantWave_norm_sq v hv ho, inv_pow, Real.sq_sqrt hn.le]
  exact inv_mul_cancel₀ hn.ne'

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

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

theorem cube_smooth_axis_spectral_lower {d : ℕ} {b : ℝ} (hb : 0 < b)
    (i : Fin (d+1)) {f g : (Fin (d+1) → ℝ) → ℂ}
    (hf : MemLp f 2 (cubeMeasure b (d+1)))
    (hg : MemLp g 2 (cubeMeasure b (d+1)))
    (hd : ∀ᵐ x ∂(cubeMeasure b d), ∀ t ∈ Icc 0 b,
      HasDerivAt (fun v => f (Fin.insertNth i v x)) (g (Fin.insertNth i t x)) t)
    (s : Finset ((Fin d → ℕ) × ℕ)) :
    ∑ q ∈ s, ((((q.2 : ℝ) + 1) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b (Fin.insertNth i (q.2+1) q.1) x) * f x
        ∂(cubeMeasure b (d+1))‖^2) ≤
      ∫ x, ‖g x‖^2 ∂(cubeMeasure b (d+1)) := by
  classical
  have hp := splitCube_measurePreserving (b := b) i
  have hps := MeasurePreserving.symm (splitCube i) hp
  have hm : ∀ q : Fin d → ℕ, MemLp (cubeMode b q) 2 (cubeMeasure b d) :=
    fun q => scalarTensor_memLp (neumannMode b) (neumannMode_memLp b) q
  have ho : ∀ q r : Fin d → ℕ,
      (∫ x, star (cubeMode b q x) * cubeMode b r x ∂(cubeMeasure b d)) =
        if q = r then (1 : ℂ) else 0 :=
    by
      intro q r
      have h := scalarTensor_orthonormal (μ := volume.restrict (Ioc 0 b)) (neumannMode b)
        (by intro m n; by_cases h : m = n <;>
             simpa only [h, ite_true, ite_false] using neumannMode_orthonormal hb m n) q r
      by_cases he : q = r <;>
         simpa only [cubeMode, cubeMeasure, he, ite_true, ite_false] using h
  have H := neumann_tensor_smooth_spectral_lower hb (cubeMode b) hm ho
    (hf.comp_measurePreserving hps) (hg.comp_measurePreserving hps)
    (by simpa only [Function.comp_apply, splitCube_symm_apply] using hd) s
  have he (q : (Fin d → ℕ) × ℕ) :
      (∫ z, star (cubeMode b q.1 z.1 * neumannMode b (q.2+1) z.2) *
        f ((splitCube i).symm z) ∂((cubeMeasure b d).prod (volume.restrict (Ioc 0 b)))) =
      ∫ x, star (cubeMode b (Fin.insertNth i (q.2+1) q.1) x) * f x
        ∂(cubeMeasure b (d+1)) := by
    have hh := hp.integral_comp' (fun z => star (cubeMode b q.1 z.1 *
      neumannMode b (q.2+1) z.2) * f ((splitCube i).symm z))
    simpa only [(splitCube i).symm_apply_apply, ← cubeMode_insertNth] using hh.symm
  simp only [Function.comp_apply] at H
  simp_rw [he] at H
  rw [hps.integral_comp' (fun x => ‖g x‖^2)] at H
  exact H

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

theorem cube_weak_axis_spectral_lower {d : ℕ} {b : ℝ} (hb : 0 < b)
    (i : Fin (d+1)) {u g : EuclideanSpace ℝ (Fin (d+1)) → ℂ}
    (hu : MemLp u 2) (hg : MemLp g 2)
    (hw : ∀ φ : EuclideanSpace ℝ (Fin (d+1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g x * (φ x : ℂ)))
    (s : Finset ((Fin d → ℕ) × ℕ)) :
    ∑ q ∈ s, ((((q.2 : ℝ) + 1) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b (Fin.insertNth i (q.2+1) q.1) x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2) ≤
      ∫ x, ‖g (WithLp.toLp 2 x)‖^2 ∂(cubeMeasure b (d+1)) := by
  classical
  let f : (Fin (d+1) → ℝ) → ℂ := fun x => u (WithLp.toLp 2 x)
  let h : (Fin (d+1) → ℝ) → ℂ := fun x => g (WithLp.toLp 2 x)
  let F : ℕ → (Fin (d+1) → ℝ) → ℂ := fun k x => complexMollify k u (WithLp.toLp 2 x)
  let G : ℕ → (Fin (d+1) → ℝ) → ℂ := fun k x => complexMollify k g (WithLp.toLp 2 x)
  have hp := PiLp.volume_preserving_toLp (Fin (d+1))
  have hf : MemLp f 2 volume := hu.comp_measurePreserving hp
  have hh : MemLp h 2 volume := hg.comp_measurePreserving hp
  have hF : ∀ k, MemLp (F k) 2 volume := fun k => (complexMollify_memLp k hu).comp_measurePreserving hp
  have hG : ∀ k, MemLp (G k) 2 volume := fun k => (complexMollify_memLp k hg).comp_measurePreserving hp
  have hFl : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2) atTop (nhds 0) := by
    have he (k : ℕ) : (∫ x, ‖F k x - f x‖^2) = ∫ x, ‖complexMollify k u x - u x‖^2 :=
      by
        simpa only [F, f] using hp.integral_comp
          ((PiLp.homeomorph 2 (fun _ : Fin (d+1) => ℝ)).symm.measurableEmbedding)
          (fun x => ‖complexMollify k u x - u x‖^2)
    simp_rw [he]
    exact complexMollify_L2_tendsto hu
  have hGl : Tendsto (fun k => ∫ x, ‖G k x - h x‖^2) atTop (nhds 0) := by
    have he (k : ℕ) : (∫ x, ‖G k x - h x‖^2) = ∫ x, ‖complexMollify k g x - g x‖^2 :=
      by
        simpa only [G, h] using hp.integral_comp
          ((PiLp.homeomorph 2 (fun _ : Fin (d+1) => ℝ)).symm.measurableEmbedding)
          (fun x => ‖complexMollify k g x - g x‖^2)
    simp_rw [he]
    exact complexMollify_L2_tendsto hg
  have hFb := integral_sq_sub_restrict_tendsto (cubeMeasure_le_volume (b := b)) hf hF hFl
  have hGb := integral_sq_sub_restrict_tendsto (cubeMeasure_le_volume (b := b)) hh hG hGl
  have hfc := hf.mono_measure (cubeMeasure_le_volume (b := b))
  have hhc := hh.mono_measure (cubeMeasure_le_volume (b := b))
  have hFc := fun k => (hF k).mono_measure (cubeMeasure_le_volume (b := b))
  have hGc := fun k => (hG k).mono_measure (cubeMeasure_le_volume (b := b))
  have hk (k : ℕ) := cube_smooth_axis_spectral_lower hb i (hFc k) (hGc k)
    (Eventually.of_forall (fun x t _ => by
      have H := euclidean_hasDerivAt_insertNth i x t ((complexMollify_contDiff k hu).differentiable (by simp))
      rw [complexMollify_fderiv k hu hg (EuclideanSpace.single i 1) hw] at H
      exact H)) s
  apply le_of_tendsto_of_tendsto _ (integral_norm_sq_tendsto_of_L2 hhc hGc hGb)
    (Eventually.of_forall hk)
  apply tendsto_finsetSum
  intro q hq
  apply Tendsto.const_mul
  apply Tendsto.pow
  apply Tendsto.norm
  exact integral_coefficient_tendsto_of_L2 hfc
    (scalarTensor_memLp (neumannMode b) (neumannMode_memLp b) _) hFc hFb

theorem cube_weak_axis_all_frequencies {d : ℕ} {b : ℝ} (hb : 0 < b)
    (i : Fin (d+1)) {u g : EuclideanSpace ℝ (Fin (d+1)) → ℂ}
    (hu : MemLp u 2) (hg : MemLp g 2)
    (hw : ∀ φ : EuclideanSpace ℝ (Fin (d+1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g x * (φ x : ℂ)))
    (s : Finset (Fin (d+1) → ℕ)) :
    ∑ q ∈ s, (((q i : ℝ) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2) ≤
      ∫ x, ‖g (WithLp.toLp 2 x)‖^2 ∂(cubeMeasure b (d+1)) := by
  classical
  let p : (Fin (d+1) → ℕ) → ((Fin d → ℕ) × ℕ) :=
    fun q => (i.removeNth q, q i - 1)
  have hrec (q : Fin (d+1) → ℕ) (hq : 0 < q i) :
      Fin.insertNth i ((p q).2 + 1) (p q).1 = q := by
    apply Fin.insertNth_eq_iff.mpr
    exact ⟨Nat.sub_add_cancel (by omega), rfl⟩
  have hinj : Set.InjOn p ↑(s.filter (fun q => 0 < q i)) := by
    intro q hq r hr he
    rw [← hrec q (Finset.mem_filter.mp hq).2, ← hrec r (Finset.mem_filter.mp hr).2, he]
  have H := cube_weak_axis_spectral_lower hb i hu hg hw
    ((s.filter (fun q => 0 < q i)).image p)
  rw [Finset.sum_image hinj] at H
  have he : (∑ q ∈ s.filter (fun q => 0 < q i),
      ((q i : ℝ) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2) =
      ∑ q ∈ s, ((q i : ℝ) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2 := by
    apply Finset.sum_filter_of_ne
    intro q _ hn
    by_contra hh
    have hz : q i = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_mul, zero_div, zero_pow (by omega : 2 ≠ 0)] at hn
    exact hn rfl
  rw [← he]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro q hq
  have hqi : 0 < q i := (Finset.mem_filter.mp hq).2
  have hp : (((p q).2 : ℝ) + 1) = (q i : ℝ) := by
    change ((q i - 1 : ℕ) : ℝ) + 1 = (q i : ℝ)
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ q i) : q i - 1 + 1 = q i)
  rw [hrec q (Finset.mem_filter.mp hq).2, hp]

theorem cube_weak_spectral_lower {d : ℕ} {b : ℝ} (hb : 0 < b)
    {u : EuclideanSpace ℝ (Fin (d+1)) → ℂ}
    {g : Fin (d+1) → EuclideanSpace ℝ (Fin (d+1)) → ℂ}
    (hu : MemLp u 2) (hg : ∀ i, MemLp (g i) 2)
    (hw : ∀ i (φ : EuclideanSpace ℝ (Fin (d+1)) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g i x * (φ x : ℂ)))
    (s : Finset (Fin (d+1) → ℕ)) :
    ∑ q ∈ s, ((∑ i, ((q i : ℝ) * Real.pi / b)^2) *
      ‖∫ x, star (cubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2) ≤
      ∑ i, ∫ x, ‖g i (WithLp.toLp 2 x)‖^2 ∂(cubeMeasure b (d+1)) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun i _ => cube_weak_axis_all_frequencies hb i hu (hg i) (hw i) s)

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinMode
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

section IndexBridge
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem finiteCube_weak_spectral_lower {d : ℕ} (e : I ≃ Fin (d+1))
    {b : ℝ} (hb : 0 < b)
    {u : EuclideanSpace ℝ I → ℂ} {g : I → EuclideanSpace ℝ I → ℂ}
    (hu : MemLp u 2) (hg : ∀ i, MemLp (g i) 2)
    (hw : ∀ i (φ : EuclideanSpace ℝ I → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g i x * (φ x : ℂ))) (s : Finset (I → ℕ)) :
    ∑ q ∈ s, ((∑ i, ((q i : ℝ) * Real.pi / b)^2) *
      ‖∫ x, star (finiteCubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(finiteCubeMeasure b I)‖^2) ≤
      ∑ i, ∫ x, ‖g i (WithLp.toLp 2 x)‖^2 ∂(finiteCubeMeasure b I) := by
  classical
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm
  let p : (I → ℕ) → (Fin (d+1) → ℕ) := fun q => q ∘ e.symm
  have hp : Function.Injective p := by
    intro q r h
    funext i
    simpa only [p, Function.comp_apply, e.symm_apply_apply] using congrFun h (e i)
  have H := cube_weak_spectral_lower hb
    (hu.comp_measurePreserving L.measurePreserving)
    (fun j => (hg (e.symm j)).comp_measurePreserving L.measurePreserving)
    (euclidean_weak_reindex e hw) (s.image p)
  rw [Finset.sum_image hp.injOn] at H
  have HC (q : I → ℕ) :
      (∫ x, star (cubeMode b (p q) x) * (u ∘ L) (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))) =
      ∫ x, star (finiteCubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(finiteCubeMeasure b I) := finiteCube_coefficient_reindex b e u q
  simp_rw [HC] at H
  have HS (q : I → ℕ) :
      (∑ j : Fin (d+1), (((p q) j : ℝ) * Real.pi / b)^2) =
      ∑ i, ((q i : ℝ) * Real.pi / b)^2 :=
    Equiv.sum_comp e.symm (fun i => ((q i : ℝ) * Real.pi / b)^2)
  simp_rw [HS] at H
  have HG (j : Fin (d+1)) :
      (∫ x, ‖((g (e.symm j)) ∘ L) (WithLp.toLp 2 x)‖^2 ∂(cubeMeasure b (d+1))) =
      ∫ x, ‖g (e.symm j) (WithLp.toLp 2 x)‖^2 ∂(finiteCubeMeasure b I) :=
    finiteCube_integral_reindex b e (fun x => ‖g (e.symm j) x‖^2)
  simp_rw [HG] at H
  rw [Equiv.sum_comp e.symm (fun i => ∫ x, ‖g i (WithLp.toLp 2 x)‖^2 ∂(finiteCubeMeasure b I))] at H
  exact H

end IndexBridge

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

lemma cubeFermionCoefficient_finite_energy {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) (s : Finset (Fin n → SpinMode)) :
    ∑ a ∈ s, cubeSpectralWeight b a * ‖cubeFermionCoefficient ψ b a‖^2 ≤
      cubeKinetic ψ b := by
  classical
  let e := cubeLabelEquiv n
  let Q := s.image (fun a => (e a).2)
  let F : Spins n × ((Fin n × Fin 3) → ℕ) → ℝ := fun sq =>
    ((1/2 : ℝ) * ∑ i, ((sq.2 i : ℝ) * Real.pi / b)^2) *
      ‖∫ x, star (finiteCubeMode b sq.2 x) * ψ.value sq.1 (WithLp.toLp 2 x)
        ∂(finiteCubeMeasure b (Fin n × Fin 3))‖^2
  have he : ∑ a ∈ s, cubeSpectralWeight b a * ‖cubeFermionCoefficient ψ b a‖^2 =
      ∑ sq ∈ s.image e, F sq := by
    rw [Finset.sum_image e.injective.injOn]
    rfl
  have hsub : s.image e ⊆ Finset.univ.product Q := by
    intro sq hsq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hsq
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩
  have hF (sq) : 0 ≤ F sq := by dsimp only [F]; positivity
  obtain ⟨E⟩ := configuration_nonempty_equiv hn
  calc
    _ = ∑ sq ∈ s.image e, F sq := he
    _ ≤ ∑ sq ∈ Finset.univ.product Q, F sq :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun sq _ _ => hF sq)
    _ = ∑ t : Spins n, ∑ q ∈ Q, F (t,q) := Finset.sum_product _ _ _
    _ ≤ ∑ t : Spins n, (1/2 : ℝ) * ∑ i, ∫ x,
        ‖ψ.gradient t i (WithLp.toLp 2 x)‖^2 ∂(finiteCubeMeasure b (Fin n × Fin 3)) := by
      apply Finset.sum_le_sum
      intro t _
      have H := finiteCube_weak_spectral_lower E hb (ψ.value_L2 t) (ψ.partial_L2 t)
        (ψ.weak_partial t) Q
      have hh := mul_le_mul_of_nonneg_left H (show (0:ℝ) ≤ 1/2 by norm_num)
      simpa only [F, mul_assoc, ← Finset.mul_sum] using hh
    _ = cubeKinetic ψ b := by simp only [cubeKinetic, Finset.mul_sum]

lemma cubeFermionCoefficient_energy_summable {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) :
    Summable (fun a => cubeSpectralWeight b a * ‖cubeFermionCoefficient ψ b a‖^2) := by
  exact summable_of_sum_le (fun a => mul_nonneg (cubeSpectralWeight_nonneg b a) (sq_nonneg _))
    (fun s => cubeFermionCoefficient_finite_energy hn ψ hb s)

lemma cubeFermionCoefficient_energy_le {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) :
    (∑' a, cubeSpectralWeight b a * ‖cubeFermionCoefficient ψ b a‖^2) ≤
      cubeKinetic ψ b := by
  exact Real.tsum_le_of_sum_le (fun a => mul_nonneg (cubeSpectralWeight_nonneg b a) (sq_nonneg _))
    (fun s => cubeFermionCoefficient_finite_energy hn ψ hb s)

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

lemma cubeState_full_mass {n : ℕ} (ψ : H1Vector n) :
    (∫ z, ‖cubeState ψ z‖^2 ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = mass ψ := by
  change (∫ z, ‖ψ.value ((spinCubeEquiv n) z).1 (WithLp.toLp 2 ((spinCubeEquiv n) z).2)‖^2
    ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = mass ψ
  rw [(spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => ‖ψ.value sx.1 (WithLp.toLp 2 sx.2)‖^2)]
  rw [integral_prod _ ψ.spinSpace_memLp.norm.integrable_sq, integral_count]
  unfold mass
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume from
    PiLp.volume_preserving_toLp _).integral_comp' (fun x => ‖ψ.value s x‖^2)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SmoothCompact
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb

lemma slaterState_antisymmetric {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) :
    Antisymmetric (slaterState v hv hC) := by
  intro p s
  filter_upwards [] with x
  change slaterConfiguration v (s ∘ p) (permute p x) = _ * slaterConfiguration v s x
  have he : (fun i => ((s ∘ p) i, position (permute p x) i)) =
      (fun i => (s i, position x i)) ∘ p := by
    funext i
    simp only [Function.comp_apply, position_permute]
  simp only [slaterConfiguration, slaterWave, he, determinantWave_permute]
  ring

lemma slaterState_normalized {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s))
    (ho : ∀ i j, (∑ s : Fin 2, ∫ x : Space, star (v i x s) * v j x s) =
      if i = j then (1:ℂ) else 0) : mass (slaterState v hv hC) = 1 := by
  have hV (i : Fin n) (s : Fin 2) : MemLp (fun x => v i x s) 2 volume :=
    (hv i s).continuous.memLp_of_hasCompactSupport (hC i s)
  rw [← cubeState_full_mass, slaterState_cubeState]
  apply slaterWave_normalized (fun i => flatSpinOrbital (v i))
    (fun i => flatSpinOrbital_memLp (v i) (hV i))
  intro i j
  rw [flatSpinOrbital_inner (v i) (v j) (hV i) (hV j)]
  by_cases h : i = j
  · simpa only [ite_eq_left h] using ho i j
  · simpa only [ite_eq_right h] using ho i j

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GroupFermionicCoefficients
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

lemma grouped_fermionic_cube_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {g : Fin n → ι}
    (hψ : GroupAntisymmetric ψ g) {b : ℝ} (hb : 0 < b) :
    groupNeumannLower g b * cubeMass ψ b ≤ cubeKinetic ψ b := by
  rw [← cubeFermionCoefficient_parseval ψ hb]
  exact (GroupFermionicCoefficients.spectral_lower
    (cubeFermionCoefficient_group_antisymmetric hψ b) hb
    (cubeFermionCoefficient_summable ψ hb)
    (cubeFermionCoefficient_energy_summable hn ψ hb)).trans
      (cubeFermionCoefficient_energy_le hn ψ hb)

lemma assigned_cube_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin n → ι) (center : ι → Space) {b : ℝ} (hb : 0 < b) :
    groupNeumannLower g b *
      cubeMass (ψ.translate (WithLp.toLp 2 (fun ij => center (g ij.1) ij.2))) b ≤
      cubeKinetic (ψ.translate (WithLp.toLp 2 (fun ij => center (g ij.1) ij.2))) b :=
  grouped_fermionic_cube_kinetic_lower hn _ (translate_group_antisymmetric hψ g center) hb

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Rotation
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.instIsHaarMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulLeftInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulRightInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsProbabilityMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1
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

lemma fineKernel_measurable (b : ℝ) : Measurable (fineKernel b) :=
  (rotated_flatKernel_continuous b).stronglyMeasurable.integral_prod_left'.measurable

noncomputable def rotatedFlatDensity {n : ℕ} (b : ℝ) (Q : Rotation) (x : Fin n → Space) (y : Space) : ℝ :=
  ∑ i, flatFineKernel b (rotationIsometry Q (y-x i)).ofLp

lemma fineDensity_nonneg {n : ℕ} (b : ℝ) (x : Fin n → Space) (y : Space) :
    0 ≤ fineDensity b x y := Finset.sum_nonneg (fun _ _ => fineKernel_nonneg ..)
lemma fineDensity_le {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) (y : Space) :
    fineDensity b x y ≤ n*(b⁻¹)^3 := by
  calc
    _ ≤ ∑ _ : Fin n, (b⁻¹)^3 := Finset.sum_le_sum (fun _ _ => fineKernel_le hb _)
    _ = _ := by simp
lemma rotatedFlatDensity_nonneg {n : ℕ} (b : ℝ) (Q : Rotation) (x : Fin n → Space) (y : Space) :
    0 ≤ rotatedFlatDensity b Q x y := Finset.sum_nonneg (fun _ _ => flatFineKernel_nonneg ..)
lemma rotatedFlatDensity_le {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Fin n → Space) (y : Space) :
    rotatedFlatDensity b Q x y ≤ n*(b⁻¹)^3 := by
  calc
    _ ≤ ∑ _ : Fin n, (b⁻¹)^3 := Finset.sum_le_sum (fun _ _ => flatFineKernel_le hb _)
    _ = _ := by simp

lemma fineDensity_measurable {n : ℕ} (b : ℝ) (x : Fin n → Space) :
    Measurable (fineDensity b x) :=
  Finset.measurable_sum _ (fun _ _ => (fineKernel_measurable b).comp (measurable_id.sub_const _))

lemma rotatedFlatDensity_continuous {n : ℕ} (b : ℝ) (x : Fin n → Space) :
    Continuous (fun p : Rotation × Space => rotatedFlatDensity b p.1 x p.2) := by
  apply continuous_finsetSum
  intro i _
  have hs : Continuous (fun p : Rotation × Space => (p.1, p.2 - x i)) :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hc := (rotated_flatKernel_continuous b).comp hs
  dsimp only [Function.comp_def] at hc
  exact hc

lemma fineDensity_integrable {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    Integrable (fineDensity b x) := by
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_sub_right volume (x i)).integrable_comp_of_integrable (fineKernel_integrable hb)

lemma rotatedFlatDensity_integrable {n : ℕ} (b : ℝ) (Q : Rotation) (x : Fin n → Space) :
    Integrable (rotatedFlatDensity b Q x) := by
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_sub_right volume (x i)).integrable_comp_of_integrable
    (rotated_flatKernel_space_integrable b Q)

lemma rotatedFlatDensity_integral {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Fin n → Space) :
    (∫ y, rotatedFlatDensity b Q x y) = (n : ℝ) := by
  have hi (i : Fin n) : Integrable (fun y : Space => flatFineKernel b (rotationIsometry Q (y-x i)).ofLp) :=
    (measurePreserving_sub_right volume (x i)).integrable_comp_of_integrable
      (rotated_flatKernel_space_integrable b Q)
  unfold rotatedFlatDensity
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have hrot (i : Fin n) : (∫ y : Space, flatFineKernel b (rotationIsometry Q (y-x i)).ofLp) = 1 := by
    change (∫ y : Space, (fun z : Space => flatFineKernel b (rotationIsometry Q z).ofLp) (y-x i)) = 1
    exact (integral_sub_right_eq_self (fun z : Space => flatFineKernel b (rotationIsometry Q z).ofLp) (x i)).trans
      (rotated_flatKernel_space_integral hb Q)
  simp_rw [hrot]
  simp

lemma rotatedFlatDensity_power_integrable {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Fin n → Space) :
    Integrable (fun y => rotatedFlatDensity b Q x y ^ (5/3 : ℝ)) := by
  apply ((rotatedFlatDensity_integrable b Q x).const_mul ((n*(b⁻¹)^3)^(2/3:ℝ))).mono'
  · exact (((rotatedFlatDensity_continuous b x).comp (continuous_const.prodMk continuous_id)).measurable.pow_const _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _)]
      exact rpow_five_thirds_le_linear (rotatedFlatDensity_nonneg ..) (rotatedFlatDensity_le hb ..))

lemma rotatedFlatDensity_power_integral_le {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Fin n → Space) :
    (∫ y, rotatedFlatDensity b Q x y ^ (5/3 : ℝ)) ≤ ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n := by
  calc
    _ ≤ ∫ y, ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ) * rotatedFlatDensity b Q x y :=
      integral_mono (rotatedFlatDensity_power_integrable hb Q x)
        ((rotatedFlatDensity_integrable b Q x).const_mul _) (fun _ =>
          rpow_five_thirds_le_linear (rotatedFlatDensity_nonneg ..) (rotatedFlatDensity_le hb ..))
    _ = _ := by rw [integral_const_mul, rotatedFlatDensity_integral hb]

lemma rotatedFlatDensity_power_integrable_prod {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    Integrable (fun p : Rotation × Space => rotatedFlatDensity b p.1 x p.2^(5/3:ℝ))
      (rotationMeasure.prod volume) := by
  have hm := (rotatedFlatDensity_continuous b x).measurable.pow_const (5/3:ℝ)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun Q => rotatedFlatDensity_power_integrable hb Q x)
  · simp_rw [Real.norm_of_nonneg (Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _)]
    apply (integrable_const (((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n)).mono'
      hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun Q => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _))]
      exact rotatedFlatDensity_power_integral_le hb Q x)

lemma fineDensity_eq_angularAverage {n : ℕ} (b : ℝ) (x : Fin n → Space) (y : Space) :
    fineDensity b x y = ∫ Q, rotatedFlatDensity b Q x y ∂rotationMeasure := by
  unfold fineDensity fineKernel rotatedFlatDensity
  exact (integral_finsetSum _ (fun _ _ => rotated_flatKernel_integrable b _)).symm

lemma rotatedFlatDensity_angular_integrable {n : ℕ} (b : ℝ) (x : Fin n → Space) (y : Space) :
    Integrable (fun Q => rotatedFlatDensity b Q x y) rotationMeasure :=
  integrable_finsetSum _ (fun _ _ => rotated_flatKernel_integrable b _)

lemma rotatedFlatDensity_power_angular_integrable {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) (y : Space) :
    Integrable (fun Q => rotatedFlatDensity b Q x y^(5/3:ℝ)) rotationMeasure := by
  apply (integrable_const (((n:ℝ)*(b⁻¹)^3)^(5/3:ℝ))).mono'
  · exact (((rotatedFlatDensity_continuous b x).comp (continuous_id.prodMk continuous_const)).measurable.pow_const _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun Q => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _)]
      exact Real.rpow_le_rpow (rotatedFlatDensity_nonneg ..) (rotatedFlatDensity_le hb ..) (by norm_num))

lemma fineDensity_Jensen {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) (y : Space) :
    fineDensity b x y^(5/3:ℝ) ≤ ∫ Q, rotatedFlatDensity b Q x y^(5/3:ℝ) ∂rotationMeasure := by
  rw [fineDensity_eq_angularAverage]
  exact (convexOn_rpow (by norm_num : (1:ℝ) ≤ 5/3)).map_integral_le
    (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 5/3)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun _ => rotatedFlatDensity_nonneg ..))
    (rotatedFlatDensity_angular_integrable b x y)
    (rotatedFlatDensity_power_angular_integrable hb x y)

noncomputable def fineDensityPower {n : ℕ} (b : ℝ) (x : Fin n → Space) : ℝ :=
  ∫ y, fineDensity b x y^(5/3:ℝ)

lemma fineDensityPower_le_angularAverage {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    fineDensityPower b x ≤ ∫ Q, ∫ y, rotatedFlatDensity b Q x y^(5/3:ℝ) ∂volume ∂rotationMeasure := by
  have hi := rotatedFlatDensity_power_integrable_prod hb x
  have hm := (fineDensity_measurable b x).pow_const (5/3:ℝ)
  have hl := hi.integral_prod_right.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (fineDensity_nonneg ..) _)]
      exact fineDensity_Jensen hb x y))
  exact (integral_mono hl hi.integral_prod_right (fun y => fineDensity_Jensen hb x y)).trans_eq
    (integral_integral_swap hi).symm

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketWindowed
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
lemma packetAnalysis_measurable (g h : 𝓢(Space,ℂ)) :
    StronglyMeasurable (fun yp : Space × Space => packetAnalysis g h yp.1 yp.2) := by
  simp only [packetAnalysis_integral]
  let k : (Space × Space) × Space → ℂ := fun z =>
    Complex.exp ((-2*Real.pi*inner ℝ z.2 z.1.2 : ℝ)*Complex.I)*
      (conj (g (z.2-z.1.1))*h z.2)
  have hk : Continuous k := by
    exact (((Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_snd.inner continuous_fst.snd)))).mul
      continuous_const).cexp).mul
        (((Complex.continuous_conj.comp (g.continuous.comp (continuous_snd.sub continuous_fst.fst)))).mul
          (h.continuous.comp continuous_snd))
  exact hk.stronglyMeasurable.integral_prod_right'
lemma packetAnalysis_integrable (g h : 𝓢(Space,ℂ)) :
    Integrable (fun yp : Space × Space => ‖packetAnalysis g h yp.1 yp.2‖^2)
      (volume.prod volume) := by
  apply (integrable_prod_iff ((packetAnalysis_measurable g h).norm.pow 2).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (packetAnalysis_momentum_integrable g h),?_⟩
  change Integrable (fun y : Space => ∫ p : Space, ‖‖packetAnalysis g h y p‖^2‖)
  simp only [Real.norm_of_nonneg (sq_nonneg _),packetAnalysis_momentum]
  exact (packetWindowed_joint_integrable g h).integral_prod_left
lemma packetAnalysis_resolution (g h : 𝓢(Space,ℂ)) :
    (∫ yp : Space × Space,‖packetAnalysis g h yp.1 yp.2‖^2 ∂volume.prod volume) =
      (∫ x : Space,‖g x‖^2)*(∫ x : Space,‖h x‖^2) := by
  rw [integral_prod _ (packetAnalysis_integrable g h)]
  simp only [packetAnalysis_momentum]
  rw [←integral_prod _ (packetWindowed_joint_integrable g h)]
  exact packetWindowed_joint_integral g h
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PacketFrame
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb

lemma packetFrame_schwartz_quadratic_le (g h : 𝓢(Space,ℂ))
    (hg : (∫ x : Space, ‖g x‖^2) = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume.prod volume) :
    (inner ℂ (h.toLp 2 volume) (packetFrame g μ (h.toLp 2 volume))).re ≤
      ‖h.toLp 2 volume‖^2 := by
  rw [packetFrame, frameOperator_quadratic (packetState_toL2_memLp g μ)]
  simp only [packetState_inner]
  calc
    _ ≤ ∫ yp : Space × Space, ‖packetAnalysis g h yp.1 yp.2‖^2 ∂volume.prod volume :=
      integral_mono_measure hμ (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (packetAnalysis_integrable g h)
    _ = ‖h.toLp 2 volume‖^2 := by
      rw [packetAnalysis_resolution, hg, one_mul, schwartz_toL2_norm_sq]

lemma packetFrame_quadratic_le (g : 𝓢(Space,ℂ))
    (hg : (∫ x : Space, ‖g x‖^2) = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume.prod volume)
    (u : Lp ℂ 2 (volume : Measure Space)) :
    (inner ℂ u (packetFrame g μ u)).re ≤ ‖u‖^2 := by
  refine DenseRange.induction_on
    (p := fun w : Lp ℂ 2 (volume : Measure Space) =>
      (inner ℂ w (packetFrame g μ w)).re ≤ ‖w‖^2)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := Space)
      (p := 2) (μ := (volume : Measure Space)) (by simp)) u ?_ ?_
  · exact isClosed_le (Complex.continuous_re.comp
      (continuous_id.inner (packetFrame g μ).continuous)) (continuous_norm.pow 2)
  · intro h
    exact packetFrame_schwartz_quadratic_le g h hg μ hμ

lemma packetFrame_complement_positive (g : 𝓢(Space,ℂ))
    (hg : (∫ x : Space, ‖g x‖^2) = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume.prod volume) :
    (ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure Space)) - packetFrame g μ).toLinearMap.IsPositive := by
  apply id_sub_frameOperator_positive (packetState_toL2_memLp g μ)
  intro u
  rw [← frameOperator_quadratic (packetState_toL2_memLp g μ)]
  exact packetFrame_quadratic_le g hg μ hμ u

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketSynthesisIndicator
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
lemma packetSynthesis_indicator_eq (g : 𝓢(Space,ℂ)) (A : Set (Space × Space))
    (hA : MeasurableSet A) (c : Space × Space → ℂ) (x : Space) :
    packetSynthesis g (A.indicator c) x =
      ∫ yp : Space × Space, c yp * packetState g yp.1 yp.2 x ∂(volume.restrict A) := by
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [] with yp
  by_cases hy : yp ∈ A <;> simp [packetState_apply, hy]

lemma packetState_joint_continuous (g : 𝓢(Space,ℂ)) :
    Continuous (fun z : (Space × Space) × Space => packetState g z.1.1 z.1.2 z.2) := by
  simp only [packetState_apply]
  fun_prop

open scoped Pointwise
lemma packetFrame_smooth_range_supported (g : 𝓢(Space,ℂ)) (hgc : HasCompactSupport (g : Space → ℂ))
    (A : Set (Space × Space)) (hA : MeasurableSet A)
    (K : Set Space) (hK : IsCompact K) (P : ℝ)
    (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P)
    (u : Lp ℂ 2 (volume : Measure Space)) :
    ∃ F : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      (packetFrame g (volume.restrict A) u : Space → ℂ) =ᵐ[volume] F ∧
      (∀ x, x ∉ K + tsupport (g : Space → ℂ) → F x = 0) := by
  let μ : Measure (Space × Space) := volume.restrict A
  let := compactPhase_finite A K hK P hAK hAP
  let c : Space × Space → ℂ := fun yp => inner ℂ ((packetState g yp.1 yp.2).toLp 2 volume) u
  have hc : Continuous c := (packetState_toL2_continuous g).inner continuous_const
  let C : ℝ := ‖g.toLp 2 volume‖ * ‖u‖
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcb (yp : Space × Space) : ‖c yp‖ ≤ C := by
    calc
      _ ≤ ‖(packetState g yp.1 yp.2).toLp 2 volume‖ * ‖u‖ := norm_inner_le_norm _ _
      _ = C := by rw [packetState_toL2_norm]
  let f := A.indicator c
  have hf : LocallyIntegrable f volume := by
    apply (locallyIntegrable_const C).mono (hc.aestronglyMeasurable.indicator hA)
    filter_upwards [] with yp
    rw [Real.norm_of_nonneg hC]
    by_cases hy : yp ∈ A
    · simpa [f, hy] using hcb yp
    · simp [hy, hC]
  have hpf (yp : Space × Space) (hy : f yp ≠ 0) : ‖yp.2‖ ≤ P := by
    apply hAP yp
    by_contra hn
    exact hy (by simp [f, hn])
  have hfk (yp : Space × Space) (hy : yp.1 ∉ K) : f yp = 0 := by
    have hn : yp ∉ A := by intro h; exact hy (hAK yp h)
    simp [f, hn]
  let F := packetSynthesis g f
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := packetSynthesis_contDiff g (g.smooth ⊤) hgc f hf P hpf
  have hFc : HasCompactSupport F := packetSynthesis_compactSupport g hgc f K hK hfk
  have he (x : Space) : F x = ∫ yp, c yp * packetState g yp.1 yp.2 x ∂μ :=
    packetSynthesis_indicator_eq g A hA c x
  have hFm : MemLp (fun x => ∫ yp, c yp * packetState g yp.1 yp.2 x ∂μ) 2 volume := by
    simpa only [← he] using hFs.continuous.memLp_of_hasCompactSupport hFc (p := (2:ℝ≥0∞))
  have hK2 : MemLp (fun z : (Space × Space) × Space => packetState g z.1.1 z.1.2 z.2) 2 (μ.prod volume) :=
    (memLp_two_iff_integrable_sq_norm (packetState_joint_continuous g).aestronglyMeasurable).mpr
      (packetState_joint_square_integrable g μ)
  have hEq := l2_kernel_integral (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume)
    (packetState_toL2_memLp g μ) (fun yp x => packetState g yp.1 yp.2 x)
    (fun yp => (packetState g yp.1 yp.2).coeFn_toLp 2 volume) hK2 c hc.aestronglyMeasurable C hcb hFm
  refine ⟨F, hFs, hFc, ?_, packetSynthesis_zero_of_notMem_region g f K hfk⟩
  change (frameOperator μ (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume) u : Space → ℂ) =ᵐ[volume] F
  have hOp := (frameOperator_apply (packetState_toL2_memLp g μ) u).trans hEq
  rw [hOp]
  filter_upwards [hFm.coeFn_toLp] with x hx
  exact hx.trans (he x).symm

lemma packetFrame_eigen_smooth_supported (g : 𝓢(Space,ℂ)) (hgc : HasCompactSupport (g : Space → ℂ))
    (A : Set (Space × Space)) (hA : MeasurableSet A)
    (K : Set Space) (hK : IsCompact K) (P : ℝ)
    (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P)
    (u : Lp ℂ 2 (volume : Measure Space)) (lam : ℂ) (hlam : lam ≠ 0)
    (hu : packetFrame g (volume.restrict A) u = lam • u) :
    ∃ F : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      (u : Space → ℂ) =ᵐ[volume] F ∧
      (∀ x, x ∉ K + tsupport (g : Space → ℂ) → F x = 0) := by
  obtain ⟨F,hFs,hFc,hF,hFS⟩ := packetFrame_smooth_range_supported g hgc A hA K hK P hAK hAP u
  refine ⟨fun x => lam⁻¹*F x, contDiff_const.mul hFs, hFc.mul_left, ?_, fun x hx => by change lam⁻¹*F x = 0; rw [hFS x hx,mul_zero]⟩
  rw [hu] at hF
  filter_upwards [hF, Lp.coeFn_smul lam u] with x hx hy
  rw [hy] at hx
  change lam * u x = F x at hx
  rw [← hx, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketIndex
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

instance packetIndexCountable (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Countable (packetIndex g μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  exact orthonormal_countable (packetBasis g μ).orthonormal

lemma positivePacketIndex_ne_zero {g : 𝓢(Space,ℂ)} {μ : Measure (Space × Space)}
    (i : positivePacketIndex g μ) : i.val.1 ≠ 0 := by
  intro h
  have hi := i.property
  rw [h] at hi
  exact lt_irrefl 0 hi

lemma packetPositiveIndex_smooth (g : 𝓢(Space,ℂ)) (hgc : HasCompactSupport (g : Space → ℂ))
    (A : Set (Space × Space)) (hA : MeasurableSet A)
    (K : Set Space) (hK : IsCompact K) (P : ℝ)
    (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P) :
    letI := compactPhase_finite A K hK P hAK hAP
    ∃ F : positivePacketIndex g (volume.restrict A) → Space → ℂ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) ∧ (∀ i, HasCompactSupport (F i)) ∧
      (∀ i, (packetBasis g (volume.restrict A) i.val : Space → ℂ) =ᵐ[volume] F i) ∧
      (∀ i x, x ∉ K + tsupport (g : Space → ℂ) → F i x = 0) := by
  let := compactPhase_finite A K hK P hAK hAP
  have H (i : positivePacketIndex g (volume.restrict A)) :=
    packetFrame_eigen_smooth_supported g hgc A hA K hK P hAK hAP
      (packetBasis g (volume.restrict A) i.val) i.val.1 (positivePacketIndex_ne_zero i)
      (compactSpectralBasis_eigen _ _ _ i.val)
  choose F hs hc he hsup using H
  exact ⟨F,hs,hc,he,hsup⟩

lemma spinOrbital_contDiff {ι : Type*} (F : ι → Space → ℂ)
    (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (i : ι × Fin 2) (s : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => spinOrbital F i x s) := by
  by_cases h : s = i.2 <;> simp only [spinOrbital,h,ite_true,ite_false]
  · exact hs i.1
  · exact contDiff_const

lemma spinOrbital_compactSupport {ι : Type*} (F : ι → Space → ℂ)
    (hc : ∀ i, HasCompactSupport (F i)) (i : ι × Fin 2) (s : Fin 2) :
    HasCompactSupport (fun x => spinOrbital F i x s) := by
  by_cases h : s = i.2 <;> simp only [spinOrbital,h,ite_true,ite_false]
  · exact hc i.1
  · exact HasCompactSupport.zero

lemma spinOrbital_support {ι : Type*} (F : ι → Space → ℂ) (B : Set Space)
    (hB : ∀ i x, x ∉ B → F i x = 0) (i : ι × Fin 2) (s : Fin 2) (x : Space) (hx : x ∉ B) :
    spinOrbital F i x s = 0 := by simp only [spinOrbital,hB i.1 x hx,ite_self]

lemma spinOrbital_density {ι : Type*} (F : ι → Space → ℂ) (i : ι × Fin 2) (x : Space) :
    (∑ s : Fin 2, ‖spinOrbital F i x s‖^2) = ‖F i.1 x‖^2 := by
  simp only [spinOrbital,apply_ite,norm_zero,ite_pow,zero_pow (by decide : 2 ≠ 0)]
  simp

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WeightedExchangeAlgebra
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
namespace Coulomb

lemma selectedSlater_antisymmetric {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (w : ι → Bool) :
    Antisymmetric (selectedSlater v hv hC w) :=
  slaterState_antisymmetric _ _ _

lemma selectedSlater_normalized {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (w : ι → Bool) :
    mass (selectedSlater v hv hC w) = 1 := by
  apply slaterState_normalized
  intro a b
  simp only [ho, (occupiedIndex w).injective.eq_iff]

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_JoinSpins
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
namespace Coulomb

lemma tensorValue_square_integral {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) :
    (∫ x, ‖tensorValue u v s x‖^2) =
      (∫ x, ‖u.value (s ∘ Fin.castAdd k) x‖^2)*
        (∫ y, ‖v.value (s ∘ Fin.natAdd m) y‖^2) := by
  rw [← (joinConfiguration_measurePreserving m k).integral_comp'
    (fun x => ‖tensorValue u v s x‖^2)]
  change (∫ z : Configuration m × Configuration k,
    ‖tensorValue u v s (joinConfiguration m k z)‖^2 ∂(volume.prod volume)) = _
  simp_rw [tensorValue_join, norm_mul, mul_pow]
  exact integral_prod_mul (μ := volume) (ν := volume)
    (fun x : Configuration m => ‖u.value (s ∘ Fin.castAdd k) x‖^2)
    (fun y : Configuration k => ‖v.value (s ∘ Fin.natAdd m) y‖^2)

lemma mass_tensor {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    mass (u.tensor v) = mass u*mass v := by
  change (∑ s, ∫ x, ‖tensorValue u v s x‖^2) = _
  simp_rw [tensorValue_square_integral]
  rw [sum_joinSpins]
  simp only [joinSpins_left, joinSpins_right, mass, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end Coulomb

open scoped Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
namespace Coulomb

noncomputable section

lemma fullAntisymmetrize_value {n : ℕ} (u : H1Vector n) (s : Spins n) (x : Configuration n) :
    u.fullAntisymmetrize.value s x =
      ∑ p : Equiv.Perm (Fin n), ((p.sign : ℤ) : ℂ)*u.value (s ∘ p) (permute p x) := by
  simp [H1Vector.fullAntisymmetrize, H1Vector.finiteSum, H1Vector.scale, permutation_value]

lemma fullAntisymmetrize_antisymmetric {n : ℕ} (u : H1Vector n) :
    Antisymmetric u.fullAntisymmetrize := by
  intro p s
  filter_upwards [] with x
  rw [fullAntisymmetrize_value, fullAntisymmetrize_value, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft p⁻¹)
    (fun q => ((q.sign : ℤ) : ℂ)*u.value ((s ∘ p) ∘ q) (permute q (permute p x)))]
  apply Finset.sum_congr rfl
  intro q _
  change (((p⁻¹*q).sign : ℤ) : ℂ)*u.value ((s ∘ p) ∘ ((p⁻¹*q) : Equiv.Perm (Fin n)))
    (permute (p⁻¹*q) (permute p x)) = _
  rw [permute_mul, mul_inv_cancel_left]
  have hs : (s ∘ p) ∘ ((p⁻¹*q) : Equiv.Perm (Fin n)) = s ∘ q := by
    funext i
    simp
  rw [hs, sign_complex_mul]
  simp only [Equiv.Perm.sign_inv]
  ring
end
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NormSqSumCosets
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma permutation_value_covariance {n : ℕ} (u : H1Vector n) (h : Equiv.Perm (Fin n))
    (c : ℂ) (hc : ∀ s, (u.permutation h).value s =ᵐ[volume] fun x => c*u.value s x)
    (p : Equiv.Perm (Fin n)) (s : Spins n) :
    (u.permutation (p*h)).value s =ᵐ[volume] fun x => c*(u.permutation p).value s x := by
  have H := (permute_measurePreserving p).quasiMeasurePreserving.ae (hc (s ∘ p))
  filter_upwards [H] with x hx
  rw [permutation_mul_value, permutation_value, permutation_value]
  exact hx

lemma separated_fullAntisymmetrize_value_sq {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B) (hAB : Disjoint A B)
    (s : Spins (m+k)) :
    ∀ᵐ x ∂volume, ‖(u.tensor v).fullAntisymmetrize.value s x‖^2 =
      (Fintype.card (blockGroup m k) : ℝ)*
        ∑ p : Equiv.Perm (Fin (m+k)), ‖((u.tensor v).permutation p).value s x‖^2 := by
  have hc : ∀ᵐ x ∂volume, ∀ p : Equiv.Perm (Fin (m+k)), ∀ h : Equiv.Perm (Fin (m+k)),
      h ∈ blockGroup m k →
      ((u.tensor v).permutation (p*h)).value s x =
        complexSign (m+k) h*((u.tensor v).permutation p).value s x := by
    apply ae_all_iff.2
    intro p
    apply ae_all_iff.2
    intro h
    by_cases hh : h ∈ blockGroup m k
    · exact (permutation_value_covariance (u.tensor v) h _
        (tensor_block_covariance u v hu hv h hh) p s).mono (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun x h => (hh h).elim)
  have hz : ∀ᵐ x ∂volume, ∀ p q : Equiv.Perm (Fin (m+k)), p⁻¹*q ∉ blockGroup m k →
      conj (((u.tensor v).permutation p).value s x)*((u.tensor v).permutation q).value s x = 0 := by
    apply ae_all_iff.2
    intro p
    apply ae_all_iff.2
    intro q
    by_cases h : p⁻¹*q ∈ blockGroup m k
    · exact Filter.Eventually.of_forall (fun x hn => (hn h).elim)
    · exact (configSupported_value_orthogonal (u.tensor v) (blockRegion m k A B)
        (tensor_configSupported u v A B hsu hsv) p q
        (blockRegion_orbit_disjoint hAB p q h) s).mono (fun x hx _ => hx)
  filter_upwards [hc,hz] with x hx hy
  change ‖∑ p : Equiv.Perm (Fin (m+k)), complexSign (m+k) p*
    ((u.tensor v).permutation p).value s x‖^2 = _
  exact norm_sq_signed_sum_cosets (complexSign (m+k)) complexSign_sq complexSign_real
    (blockGroup m k) (fun p => ((u.tensor v).permutation p).value s x) hx hy

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WedgeMultiplicity
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma mass_fullAntisymmetrize_of_sq {n : ℕ} (u : H1Vector n) (c : ℝ)
    (h : ∀ s, ∀ᵐ x ∂volume, ‖u.fullAntisymmetrize.value s x‖^2 =
      c*∑ p : Equiv.Perm (Fin n), ‖(u.permutation p).value s x‖^2) :
    mass u.fullAntisymmetrize = c*(Fintype.card (Equiv.Perm (Fin n)) : ℝ)*mass u := by
  have hi (s : Spins n) : (∫ x, ‖u.fullAntisymmetrize.value s x‖^2) =
      c*∑ p : Equiv.Perm (Fin n), ∫ x, ‖(u.permutation p).value s x‖^2 := by
    rw [integral_congr_ae (h s), integral_const_mul,
      integral_finsetSum _ (fun p _ => ((u.permutation p).value_L2 s).norm.integrable_sq)]
  unfold mass
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_comm]
  change c*(∑ p : Equiv.Perm (Fin n), mass (u.permutation p)) = _
  simp_rw [mass_permutation]
  simp [mass, mul_assoc]

lemma wedge_antisymmetric {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    Antisymmetric (u.wedge v) :=
  antisymmetric_scale _ (fullAntisymmetrize_antisymmetric _) _

lemma mass_wedge {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B) (hAB : Disjoint A B) :
    mass (u.wedge v) = mass u*mass v := by
  unfold H1Vector.wedge
  rw [mass_scale, wedge_normalizer_sq,
    mass_fullAntisymmetrize_of_sq (u.tensor v) _
      (separated_fullAntisymmetrize_value_sq u v hu hv A B hsu hsv hAB)]
  change (wedgeMultiplicity m k)⁻¹*(wedgeMultiplicity m k*mass (u.tensor v)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (wedgeMultiplicity_pos m k)), one_mul, mass_tensor]

lemma potentialEnergy_wedge {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B) (hAB : Disjoint A B)
    (W : Configuration (m+k) → ℝ) (hW : ∀ p x, W (permute p x) = W x)
    (hi : ∀ s, Integrable (fun x => W x*‖(u.tensor v).value s x‖^2)) :
    potentialEnergy W (u.wedge v) = potentialEnergy W (u.tensor v) := by
  unfold H1Vector.wedge
  rw [potentialEnergy_scale, wedge_normalizer_sq,
    potentialEnergy_fullAntisymmetrize_of_sq (u.tensor v) _ W hW hi
      (separated_fullAntisymmetrize_value_sq u v hu hv A B hsu hsv hAB)]
  change (wedgeMultiplicity m k)⁻¹*(wedgeMultiplicity m k*potentialEnergy W (u.tensor v)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (wedgeMultiplicity_pos m k)), one_mul]
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_NuclearPotential
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma nuclearEnergy_wedge_tensor {M m k : ℕ} (S : Nuclei M)
    (u : H1Vector m) (v : H1Vector k) (hu : Antisymmetric u) (hv : Antisymmetric v)
    (A B : Set Space) (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hAB : Disjoint A B) : nuclearEnergy S (u.wedge v) = nuclearEnergy S (u.tensor v) :=
  potentialEnergy_wedge u v hu hv A B hsu hsv hAB (nuclearPotential S)
    (nuclearPotential_permute S) ((u.tensor v).nuclear_integrable S)

lemma pairEnergy_wedge_tensor {m k : ℕ}
    (u : H1Vector m) (v : H1Vector k) (hu : Antisymmetric u) (hv : Antisymmetric v)
    (A B : Set Space) (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hAB : Disjoint A B) : pairEnergy (u.wedge v) = pairEnergy (u.tensor v) :=
  potentialEnergy_wedge u v hu hv A B hsu hsv hAB pairPotential
    pairPotential_permute (u.tensor v).pair_integrable

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_LeftPotential
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma pairEnergy_tensor {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    pairEnergy (u.tensor v) = pairEnergy u*mass v+mass u*pairEnergy v+crossEnergy u v := by
  change potentialEnergy pairPotential (u.tensor v) = _
  rw [show (pairPotential : Configuration (m+k) → ℝ) = fun x =>
      (leftPotential pairPotential x+rightPotential pairPotential x)+
      crossPotential ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2
      from funext pairPotential_split]
  have h1 := tensor_leftPotential_integrable u v pairPotential u.pair_integrable
  have h2 := tensor_rightPotential_integrable u v pairPotential v.pair_integrable
  have h12 : ∀ s, Integrable (fun x => (leftPotential pairPotential x+rightPotential pairPotential x)*
      ‖(u.tensor v).value s x‖^2) := by
    intro s
    apply ((h1 s).add (h2 s)).congr
    filter_upwards [] with x
    exact (add_mul _ _ _).symm
  rw [potentialEnergy_add _ _ _ h12
      (tensor_crossPotential_integrable u v),
      potentialEnergy_add _ _ _ h1 h2,potentialEnergy_tensor_left,potentialEnergy_tensor_right]
  rfl

lemma form_wedge {M m k : ℕ} (S : Nuclei M) (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    form S (u.wedge v) = form S u*mass v+mass u*form S v+crossEnergy u v := by
  unfold form
  rw [kinetic_wedge u v hu hv A B hsu hsv hA hB hAB,
    nuclearEnergy_wedge_tensor S u v hu hv A B hsu hsv hAB,
    pairEnergy_wedge_tensor u v hu hv A B hsu hsv hAB,nuclearEnergy_tensor,pairEnergy_tensor]
  ring
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_UnitNucleus
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma selectedSlater_spatialSupport {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (B : Set Space)
    (hB : ∀ a s x, x ∉ B → v a x s = 0) (w : ι → Bool) :
    SpatiallySupported (selectedSlater v hv hC w) B := by
  intro s
  filter_upwards [] with x hx
  change ¬∀ i, position x i ∈ B at hx
  obtain ⟨j,hj⟩ := not_forall.mp hx
  change slaterConfiguration (fun a => v (occupiedIndex w a)) s x = 0
  rw [slaterConfiguration_expansion]
  have hp (p : Equiv.Perm (Fin (Fintype.card {i // w i = true}))) :
      tensorOrbital (fun a => v (occupiedIndex w a)) p s x = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hB _ _ _ hj
  simp only [hp,mul_zero,Finset.sum_const_zero]

theorem finite_fermi_core_trial {ι : Type*} [Fintype ι] {M m : ℕ}
    (S : Nuclei M) (u : H1Vector m) (hu : Antisymmetric u) (hm : mass u = 1)
    (A B : Set Space) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hsu : SpatiallySupported u A) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (hsv : ∀ a s x, x ∉ B → v a x s = 0)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∀ i, lam i ≤ 1) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤ form S u +
      ((1/2:ℝ)*(∑ i, lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2) -
      (∫ x, attraction S x*finiteFermiDensity v lam x) +
      (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
        (finiteFermiDensity v lam xy.1*finiteFermiDensity v lam xy.2))) +
      coreInteractionDensity u (finiteFermiDensity v lam) := by
  have he (w : ι → Bool) : form S (u.wedge (selectedSlater v hv hC w)) =
      form S u+form S (selectedSlater v hv hC w)+crossEnergy u (selectedSlater v hv hC w) := by
    rw [form_wedge S u (selectedSlater v hv hC w) hu (selectedSlater_antisymmetric v hv hC w)
      A B hsu (selectedSlater_spatialSupport v hv hC B hsv w) hA hB hAB,
      selectedSlater_normalized v hv hC ho w,hm,mul_one,one_mul]
  obtain ⟨w, hw⟩ := exists_le_weighted_average (bernoulliWeight lam)
    (fun w => form S (u.wedge (selectedSlater v hv hC w)))
    (bernoulliWeight_nonneg lam h0 h1) (bernoulliWeight_sum lam)
  refine ⟨_, u.wedge (selectedSlater v hv hC w), wedge_antisymmetric _ _, ?_, hw.trans ?_⟩
  · rw [mass_wedge u (selectedSlater v hv hC w) hu (selectedSlater_antisymmetric v hv hC w)
      A B hsu (selectedSlater_spatialSupport v hv hC B hsv w) hAB,
      selectedSlater_normalized v hv hC ho w,hm,mul_one]
  · simp only [he,mul_add,Finset.sum_add_distrib]
    rw [← Finset.sum_mul,bernoulliWeight_sum,one_mul,bernoulli_core_cross_mean u v hv hC ho lam]
    gcongr
    exact bernoulli_slater_form_upper S v hv hC ho lam
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoreCoulombPotential
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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
namespace Coulomb

theorem infinite_fermi_core_trial {ι : Type*} [Countable ι] {M m : ℕ}
    (S : Nuclei M) (u : H1Vector m) (hu : Antisymmetric u) (hm : mass u = 1)
    (A B : Set Space) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hsu : SpatiallySupported u A) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (hsv : ∀ a s x, x ∉ B → v a x s = 0)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∀ i, lam i ≤ 1)
    (d : Space → ℝ) (hd : Integrable d)
    (hseries : ∀ᵐ x ∂volume, Summable (fun i => lam i*∑ s, ‖v i x s‖^2))
    (hdensity : (fun x => ∑' i, lam i*∑ s, ‖v i x s‖^2) =ᵐ[volume] d)
    (hN : Integrable (fun x => attraction S x*d x))
    (hD : Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(d xy.1*d xy.2)))
    (hT : Summable (fun i => lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤ form S u +
      ((1/2:ℝ)*(∑' i, lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2) -
      (∫ x, attraction S x*d x) +
      (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(d xy.1*d xy.2))) +
      (∫ x, coreCoulombPotential u x*d x) + ε := by
  classical
  let f (i : ι) (x : Space) := lam i*∑ s, ‖v i x s‖^2
  have hf (i : ι) : AEStronglyMeasurable (f i) volume := by
    apply Continuous.aestronglyMeasurable
    exact continuous_const.mul (continuous_finsetSum _ (fun s _ => (hv i s).continuous.norm.pow 2))
  have hp (i : ι) (x : Space) : 0 ≤ f i x :=
    mul_nonneg (h0 i) (Finset.sum_nonneg (fun s _ => sq_nonneg _))
  have hNp : Integrable (fun x => attraction S x*∑' i, f i x) := by
    apply hN.congr
    filter_upwards [hdensity] with x hx
    rw [hx]
  have hns := (weighted_series_integrable_hasSum hf hp hseries
    (attraction_measurable S).aestronglyMeasurable (attraction_nonneg S) hNp).2
  have heN : (∫ x, attraction S x*∑' i, f i x) = ∫ x, attraction S x*d x := by
    apply integral_congr_ae
    filter_upwards [hdensity] with x hx
    rw [hx]
  rw [heN] at hns
  have hevent : ∀ᶠ F : Finset ι in atTop,
      (∫ x, attraction S x*d x)-ε < ∑ i ∈ F, ∫ x, attraction S x*f i x :=
    hns (eventually_gt_nhds (sub_lt_self _ hε))
  obtain ⟨F,hF⟩ := hevent.exists
  let vF : F → Space → Fin 2 → ℂ := fun i => v i
  let lF : F → ℝ := fun i => lam i
  let dF := finiteFermiDensity vF lF
  have hdF (x : Space) : dF x = ∑ i ∈ F, f i x := by
    exact Finset.sum_coe_sort F (fun i => f i x)
  have hpF (x : Space) : 0 ≤ dF x := by rw [hdF]; exact Finset.sum_nonneg (fun i _ => hp i x)
  have hle : ∀ᵐ x ∂volume, dF x ≤ d x := by
    filter_upwards [hseries,hdensity] with x hx hy
    rw [hdF,← hy]
    exact hx.sum_le_tsum F (fun i _ => hp i x)
  have hdi := finiteFermiDensity_integrable vF (fun a => hv a) (fun a => hC a) lF
  have hfm : AEStronglyMeasurable dF volume := hdi.1
  have hNi := finiteFermiDensity_nuclear_integrable S vF (fun a => hv a) (fun a => hC a) lF
  have hFinN : (∫ x, attraction S x*dF x) = ∑ i ∈ F, ∫ x, attraction S x*f i x := by
    simp only [hdF,Finset.mul_sum]
    exact integral_finsetSum F (fun i _ => (weighted_series_integrable_hasSum hf hp hseries
      (attraction_measurable S).aestronglyMeasurable (attraction_nonneg S) hNp).1 i)
  have hpair : ∀ᵐ xy ∂(volume : Measure Space).prod volume,
      coulombKernel (xy.1-xy.2)*(dF xy.1*dF xy.2) ≤
      coulombKernel (xy.1-xy.2)*(d xy.1*d xy.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hle, Measure.quasiMeasurePreserving_snd.ae hle] with xy hx hy
    exact mul_le_mul_of_nonneg_left (mul_le_mul hx hy (hpF _) ((hpF _).trans hx)) (coulombKernel_nonneg _)
  have hDi : Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(dF xy.1*dF xy.2)) := by
    apply hD.mono' (((coulombKernel_measurable.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul
      (hfm.comp_fst.mul hfm.comp_snd))
    filter_upwards [hpair] with xy hxy
    change ‖coulombKernel (xy.1-xy.2)*(dF xy.1*dF xy.2)‖ ≤ _
    rwa [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (mul_nonneg (hpF _) (hpF _)))]
  have hDbound := integral_mono_ae hDi hD hpair
  have hCoreBound := integral_mono_ae (coreCoulombPotential_mul_integrable u dF hdi)
    (coreCoulombPotential_mul_integrable u d hd) (hle.mono (fun x hx =>
      mul_le_mul_of_nonneg_left hx (coreCoulombPotential_nonneg u x)))
  have hTbound : (∑ i : F, lF i * ∑ s, ∑ b : Fin 3,
      ∫ x : Space, ‖fderiv ℝ (fun y => vF i y s) x (EuclideanSpace.single b 1)‖^2) ≤
      ∑' i, lam i * ∑ s, ∑ b : Fin 3,
      ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
    dsimp only [vF,lF]
    rw [Finset.sum_coe_sort F (fun i => lam i * ∑ s, ∑ b : Fin 3,
      ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2)]
    apply hT.sum_le_tsum
    intro i _
    exact mul_nonneg (h0 i) (Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun b _ =>
      integral_nonneg (fun x => sq_nonneg _))))
  obtain ⟨n,ψ,hψa,hψm,hψe⟩ := finite_fermi_core_trial S u hu hm A B hA hB hAB hsu vF
    (fun a => hv a) (fun a => hC a) (fun a => hsv a)
    (fun a b => by
      by_cases hab : a = b
      · subst b
        simpa [vF] using ho a a
      · have hval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
        simpa only [vF, ite_eq_right hab, ite_eq_right hval] using ho a b)
    lF (fun a => h0 a) (fun a => h1 a)
  refine ⟨n,ψ,hψa,hψm,?_⟩
  rw [coreInteractionDensity_eq u dF hdi] at hψe
  rw [← hFinN] at hF
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SumSpinDuplicate
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

lemma packetBasis_eigen_le_one (g : 𝓢(Space,ℂ)) (hg : (∫ x : Space, ‖g x‖^2) = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume.prod volume)
    (i : packetIndex g μ) : i.1.re ≤ 1 :=
  compactSpectralBasis_eigen_le_one _ (packetFrame_compact g μ) (packetFrame_positive g μ)
    (packetFrame_complement_positive g hg μ hμ) i

lemma packetPositive_density (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (F : positivePacketIndex g μ → Space → ℂ)
    (he : ∀ i, (packetBasis g μ i.val : Space → ℂ) =ᵐ[volume] F i) :
    ∀ᵐ x ∂volume, HasSum
      (fun i : positivePacketIndex g μ × Fin 2 => i.1.val.1.re * ∑ s, ‖spinOrbital F i x s‖^2)
      (2*frameDensity (packetState_toL2_memLp g μ) x) := by
  let b := packetBasis g μ
  have hs : Summable (fun i : packetIndex g μ => i.1.re*‖b i‖^2) := by
    let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
    have hnorm (i : packetIndex g μ) : ‖b i‖ = 1 := (packetBasis g μ).orthonormal.1 i
    simp only [hnorm,one_pow,mul_one]
    simpa only [packetIndex,packetFrame] using
      (frameOperator_spectral_hasSum (packetState_toL2_memLp g μ)).summable
  have h := l2_weighted_density_integrable b (fun i => i.1.re)
    (packetBasis_eigen_nonneg g μ) hs
  filter_upwards [h.2,ae_all_iff.mpr he] with x hx heq
  have hp := packet_positive_hasSum (g := g) (μ := μ) (fun i => ‖b i x‖^2) hx.hasSum
  have hp' : HasSum (fun i : positivePacketIndex g μ => i.val.1.re*‖F i x‖^2)
      (frameDensity (packetState_toL2_memLp g μ) x) := by
    convert hp using 1
    · ext i
      rw [heq i]
    · rfl
  simpa only [spinOrbital_density] using hasSum_spin_duplicate
    (fun i => mul_nonneg i.property.le (sq_nonneg _)) hp'

end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoreScreenedField
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb

lemma packetDensity_pair_integrable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) :
    Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*
      (packetDensity g ρ xy.1*packetDensity g ρ xy.2)) := by
  have hd := packetDensity_integrable g ρ hp hm hi
  have hdm := packetDensity_measurable g ρ hm
  have H := coulomb_pair_integrable hd hdm hd hdm (fun y => by
    rw [Real.norm_of_nonneg (packetDensity_nonneg g ρ hp y)]
    exact packetDensity_bound g ρ hp hm hi y)
  apply H.congr
  filter_upwards [] with xy
  ring

lemma packetPositive_orthonormal (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (F : positivePacketIndex g μ → Space → ℂ)
    (he : ∀ i, (packetBasis g μ i.val : Space → ℂ) =ᵐ[volume] F i) :
    ∀ i j, (∫ x : Space, star (F i x)*F j x) = @ite ℂ (i = j) (Classical.propDecidable _) 1 0 := by
  have ho : Orthonormal ℂ (fun i : positivePacketIndex g μ => packetBasis g μ i.val) :=
    (packetBasis g μ).orthonormal.comp (fun i : positivePacketIndex g μ => i.val) Subtype.val_injective
  exact orthonormal_representative_inner (fun i : positivePacketIndex g μ => packetBasis g μ i.val) ho F he

theorem bounded_packet_core_trial {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ))) (C : ℝ) (hC : ∀ y, ρ y ≤ C)
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤ form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*packetDensity g ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
          (packetDensity g ρ xy.1*packetDensity g ρ xy.2)) + ε := by
  let μ := volume.restrict (phaseRegion (fermiRadius ρ))
  let : IsFiniteMeasure (volume.restrict (phaseRegion (fermiRadius ρ))) := fermiMeasure_finite ρ hp hm hi
  let : Countable (packetIndex (complexWindow g) (volume.restrict (phaseRegion (fermiRadius ρ)))) := packetIndexCountable _ _
  let : Countable (positivePacketIndex (complexWindow g) (volume.restrict (phaseRegion (fermiRadius ρ)))) := inferInstance
  obtain ⟨F,hFs,hFc,he,hSup⟩ := packetPositiveIndex_smooth (complexWindow g)
    (complexWindow_compactSupport g hgc) (phaseRegion (fermiRadius ρ))
    (phaseRegion_measurable (fermiRadius_measurable ρ hm)) K hK
    ((3/(8*Real.pi)*C)^(1/3:ℝ)) (fermiPhase_center_mem ρ K hs)
    (fermiPhase_momentum_bound ρ hp C hC)
  have hsup : ∀ i x, x ∉ K+tsupport (g : Space → ℝ) → F i x = 0 := by
    simpa only [complexWindow_tsupport] using hSup
  have ho : ∀ i j, (∫ x : Space, star (F i x)*F j x) = @ite ℂ (i = j) (Classical.propDecidable _) 1 0 := by
    exact packetPositive_orthonormal (complexWindow g) μ F he
  have hg' : (∫ x : Space, ‖complexWindow g x‖^2) = 1 := by
    simpa only [complexWindow_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hg
  have hdens := packetPositive_density (complexWindow g) μ F he
  have hde : (fun x => ∑' i : positivePacketIndex (complexWindow g) μ × Fin 2,
      i.1.val.1.re*∑ s, ‖spinOrbital F i x s‖^2) =ᵐ[volume] packetDensity g ρ := by
    filter_upwards [hdens,fermiPacket_density g ρ hp hm hi] with x hx hy
    exact hx.tsum_eq.trans hy
  have hkin := fermiPacket_positive_kinetic g hg ρ hp hm hi ht F hFs hFc he
  have hnuc := packetDensity_nuclear_integrable S g ρ hp hm hi
  have hcor := coreCoulombPotential_mul_integrable u _ (packetDensity_integrable g ρ hp hm hi)
  have hfield : (∫ x, coreScreenedField S u x*packetDensity g ρ x) =
      (∫ x, attraction S x*packetDensity g ρ x) -
      (∫ x, coreCoulombPotential u x*packetDensity g ρ x) := by
    simp only [coreScreenedField,sub_mul]
    exact integral_sub hnuc hcor
  obtain ⟨n,ψ,hψa,hψm,hψe⟩ := infinite_fermi_core_trial S u hu hmu A
    (K+tsupport (g : Space → ℝ)) hA (hK.add hgc).isClosed hsep hsu
    (spinOrbital F) (spinOrbital_contDiff F hFs) (spinOrbital_compactSupport F hFc)
    (spinOrbital_support F _ hsup) (fun i j => by
      by_cases hij : i = j
      · simpa only [ite_eq_left hij] using spinOrbital_orthonormal F ho i j
      · simpa only [ite_eq_right hij] using spinOrbital_orthonormal F ho i j)
    (fun i => i.1.val.1.re) (fun i => i.1.property.le)
    (fun i => packetBasis_eigen_le_one (complexWindow g) hg' μ (phaseMeasure_le _) i.1.val)
    (packetDensity g ρ) (packetDensity_integrable g ρ hp hm hi)
    (hdens.mono (fun _ hx => hx.summable)) hde hnuc
    (packetDensity_pair_integrable g ρ hp hm hi) hkin.summable ε hε
  refine ⟨n,ψ,hψa,hψm,?_⟩
  dsimp only [phaseMeasure] at hkin
  change HasSum (fun i : positivePacketIndex (complexWindow g) (volume.restrict (phaseRegion (fermiRadius ρ))) × Fin 2 =>
    i.1.val.1.re*∑ s, ∑ b : Fin 3, ∫ x : Space,
      ‖fderiv ℝ (fun y => spinOrbital F i y s) x (EuclideanSpace.single b 1)‖^2) _ at hkin
  rw [hkin.tsum_eq] at hψe
  rw [hfield]
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RotatedDensityPower
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.instIsHaarMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulLeftInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulRightInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsProbabilityMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.packetIndexCountable
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

lemma fineDensityPower_bound {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    fineDensityPower b x ≤ ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n := by
  apply (fineDensityPower_le_angularAverage hb x).trans
  calc
    _ ≤ ∫ _ : Rotation, ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n ∂rotationMeasure :=
      integral_mono (rotatedFlatDensity_power_integrable_prod hb x).integral_prod_left
        (integrable_const _) (fun Q => rotatedFlatDensity_power_integral_le hb Q x)
    _ = _ := by simp

end Coulomb

open MeasureTheory Set
open scoped BigOperators Matrix ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RetainedFineDensity
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma retainedFineDensity_nonneg {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) (y : Space) : 0 ≤ retainedFineDensity b r x y :=
  Finset.sum_nonneg (fun _ _ => fineKernel_nonneg ..)

lemma retainedFineDensity_le {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) (y : Space) : retainedFineDensity b r x y ≤ fineDensity b x y := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ r)
    (fun _ _ _ => fineKernel_nonneg ..)

lemma retainedFineDensity_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) : Integrable (retainedFineDensity b r x) :=
  integrable_finsetSum _ (fun i _ => fineKernel_shift_integrable hb (x i))

lemma retainedFineDensity_measurable {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) : Measurable (retainedFineDensity b r x) :=
  Finset.measurable_sum _ (fun _ _ => (fineKernel_continuous b).measurable.comp (by fun_prop))

lemma retainedFineDensity_eq_sum_ite {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) (y : Space) :
    retainedFineDensity b r x y = ∑ i, if i ∈ r then fineKernel b (y-x i) else 0 := by
  simp [retainedFineDensity, Finset.sum_ite_mem]

lemma fineDensity_power_integrable {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    Integrable (fun y => fineDensity b x y ^ (5/3:ℝ)) := by
  apply ((fineDensity_integrable hb x).const_mul ((n*(b⁻¹)^3)^(2/3:ℝ))).mono'
  · exact ((fineDensity_measurable b x).pow_const _).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (fineDensity_nonneg ..) _)]
      exact rpow_five_thirds_le_linear (fineDensity_nonneg ..) (fineDensity_le hb ..)

lemma retainedFineDensity_power_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) :
    Integrable (fun y => retainedFineDensity b r x y ^ (5/3:ℝ)) := by
  apply (fineDensity_power_integrable hb x).mono'
  · exact ((retainedFineDensity_measurable b r x).pow_const _).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (retainedFineDensity_nonneg ..) _)]
      exact Real.rpow_le_rpow (retainedFineDensity_nonneg ..) (retainedFineDensity_le ..) (by norm_num)

lemma retainedFineDensity_power_le {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) :
    (∫ y, retainedFineDensity b r x y^(5/3:ℝ)) ≤ fineDensityPower b x :=
  integral_mono (retainedFineDensity_power_integrable hb r x) (fineDensity_power_integrable hb x)
    (fun y => Real.rpow_le_rpow (retainedFineDensity_nonneg ..) (retainedFineDensity_le ..) (by norm_num))

lemma retainedFineDensity_power_configuration_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (fun x => ∫ y, retainedFineDensity b (r x) (position x) y^(5/3:ℝ)) := by
  have hm : Measurable (fun p : Configuration n × Space => retainedFineDensity b (r p.1) (position p.1) p.2) := by
    simp_rw [retainedFineDensity_eq_sum_ite]
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite ((hr i).preimage measurable_fst)
    · exact (fineKernel_continuous b).measurable.comp
        (measurable_snd.sub ((continuous_position i).measurable.comp measurable_fst))
    · exact measurable_const
  exact (hm.pow_const (5/3:ℝ)).stronglyMeasurable.integral_prod_right'.measurable

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RetainedFineDensityConfigurationMeasurable
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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
lemma retainedFineDensity_configuration_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (fun p : Configuration n × Space => retainedFineDensity b (r p.1) (position p.1) p.2) := by
  simp_rw [retainedFineDensity_eq_sum_ite]
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite ((hr i).preimage measurable_fst)
  · exact (fineKernel_continuous b).measurable.comp
      (measurable_snd.sub ((continuous_position i).measurable.comp measurable_fst))
  · exact measurable_const

lemma retainedFineDensity_coulomb_configuration_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (fun x => coulombBilinear (retainedFineDensity b (r x) (position x))
      (retainedFineDensity b (r x) (position x))) := by
  have hm := retainedFineDensity_configuration_measurable b r hr
  have hi : Measurable (fun p : Configuration n × (Space × Space) =>
      retainedFineDensity b (r p.1) (position p.1) p.2.1 *
      retainedFineDensity b (r p.1) (position p.1) p.2.2 * coulombKernel (p.2.1-p.2.2)) :=
    ((hm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).mul
        (coulombKernel_measurable.comp (by fun_prop))
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

lemma retainedFineDensity_coulomb_nonneg {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) :
    0 ≤ coulombBilinear (retainedFineDensity b r x) (retainedFineDensity b r x) :=
  integral_nonneg fun _ => mul_nonneg
    (mul_nonneg (retainedFineDensity_nonneg ..) (retainedFineDensity_nonneg ..)) (coulombKernel_nonneg _)

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_NuclearPotentialSplitJoin
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma nuclearPotential_split_join {M m k : ℕ} (S : Nuclei M) (x : Configuration m)
    (y : Configuration k) :
    nuclearPotential S (joinConfiguration m k (x,y)) = nuclearPotential S x + nuclearPotential S y := by
  simp only [nuclearPotential, Fin.sum_univ_add, position_join_left, position_join_right]

lemma pairPotential_split_join {m k : ℕ} (x : Configuration m) (y : Configuration k) :
    pairPotential (joinConfiguration m k (x,y)) = pairPotential x + pairPotential y +
      ∑ i : Fin m, ∑ j : Fin k, coulombKernel (position x i - position y j) := by
  simp only [pairPotential, Fin.sum_univ_add, position_join_left, position_join_right]
  have hleft (i j : Fin m) : Fin.castAdd k i < Fin.castAdd k j ↔ i < j := by rfl
  have hright (i j : Fin k) : Fin.natAdd m i < Fin.natAdd m j ↔ i < j := by
    simp only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left]
  have hlr (i : Fin m) (j : Fin k) : Fin.castAdd k i < Fin.natAdd m j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega
  have hrl (i : Fin k) (j : Fin m) : ¬Fin.natAdd m i < Fin.castAdd k j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega
  simp only [hleft, hright, hlr, hrl, ite_true, ite_false, Finset.sum_const_zero, zero_add,
    Finset.sum_add_distrib]
  ring

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_CoreKinetic
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma H1Vector.outer_nuclear_integrable {M m k : ℕ} (ψ : H1Vector (m+k))
    (S : Nuclei M) (st : Spins (m+k)) :
    Integrable (fun z => nuclearPotential S ((joinConfiguration m k).symm z).1 * ‖ψ.value st z‖^2) := by
  simp only [nuclearPotential, attraction, position_split_left, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have H := (ψ.nuclear_coulomb_integrable_bound st (Fin.castAdd k i) (S.position j)
    (by norm_num : (0:ℝ)<1)).1
  simpa only [mul_assoc] using H.const_mul (S.charge j)

lemma H1Vector.outer_pair_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (st : Spins (m+k)) :
    Integrable (fun z => pairPotential ((joinConfiguration m k).symm z).1 * ‖ψ.value st z‖^2) := by
  simp only [pairPotential, position_split_left, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    exact (ψ.pair_coulomb_integrable_bound st (Fin.castAdd k i) (Fin.castAdd k j)
      (fun he => hij.ne (by apply Fin.ext; have H := congrArg Fin.val he; simpa only [Fin.val_castAdd] using H)) (by norm_num : (0:ℝ)<1)).1
  · simp only [ite_eq_right hij, zero_mul]
    exact integrable_zero _ _ _

lemma H1Vector.cross_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (st : Spins (m+k)) :
    Integrable (fun z => crossPotential ((joinConfiguration m k).symm z).1
      ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2) := by
  simp only [crossPotential, position_split_left, position_split_right, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (ψ.pair_coulomb_integrable_bound st (Fin.castAdd k i) (Fin.natAdd m j)
    (by intro h; have H := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at H; omega)
    (by norm_num : (0:ℝ)<1)).1

lemma nuclearEnergy_split {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) :
    nuclearEnergy S ψ =
      potentialForm (fun z => nuclearPotential S ((joinConfiguration m k).symm z).1) ψ +
      potentialForm (fun z => nuclearPotential S ((joinConfiguration m k).symm z).2) ψ := by
  have hp (z : Configuration (m+k)) : nuclearPotential S z =
      nuclearPotential S ((joinConfiguration m k).symm z).1 +
        nuclearPotential S ((joinConfiguration m k).symm z).2 := by
    simpa only [Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply] using
      nuclearPotential_split_join S ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2
  change potentialForm (nuclearPotential S) ψ = _
  simp only [potentialForm, hp, add_mul]
  simp_rw [integral_add (ψ.outer_nuclear_integrable S _) (ψ.core_nuclear_integrable S _)]
  exact Finset.sum_add_distrib

lemma pairEnergy_split {m k : ℕ} (ψ : H1Vector (m+k)) :
    pairEnergy ψ =
      potentialForm (fun z => pairPotential ((joinConfiguration m k).symm z).1) ψ +
      potentialForm (fun z => pairPotential ((joinConfiguration m k).symm z).2) ψ +
      potentialForm (fun z => crossPotential ((joinConfiguration m k).symm z).1
        ((joinConfiguration m k).symm z).2) ψ := by
  have hp (z : Configuration (m+k)) : pairPotential z =
      pairPotential ((joinConfiguration m k).symm z).1 +
        pairPotential ((joinConfiguration m k).symm z).2 +
        crossPotential ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2 := by
    simpa only [Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply, crossPotential] using
      pairPotential_split_join ((joinConfiguration m k).symm z).1 ((joinConfiguration m k).symm z).2
  change potentialForm pairPotential ψ = _
  simp only [potentialForm, hp, add_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro st _
  have H := integral_add ((ψ.outer_pair_integrable st).add (ψ.core_pair_integrable st))
    (ψ.cross_integrable st)
  simp only [Pi.add_apply] at H
  rw [H, integral_add (ψ.outer_pair_integrable st) (ψ.core_pair_integrable st)]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RetainedFinePower
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma retainedFinePower_nonneg {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (x : Configuration n) :
    0 ≤ retainedFinePower b r x :=
  integral_nonneg (fun _ => Real.rpow_nonneg (retainedFineDensity_nonneg ..) _)

lemma retainedFinePower_bound {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (x : Configuration n) :
    retainedFinePower b r x ≤ ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n :=
  (retainedFineDensity_power_le hb _ _).trans (fineDensityPower_bound hb _)

lemma retainedFinePower_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (retainedFinePower b r) := retainedFineDensity_power_configuration_measurable b r hr

lemma retainedFineCoulomb_nonneg {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (x : Configuration n) :
    0 ≤ retainedFineCoulomb b r x :=
  div_nonneg (retainedFineDensity_coulomb_nonneg ..) (by norm_num)

lemma retainedFineCoulomb_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (retainedFineCoulomb b r) :=
  (retainedFineDensity_coulomb_configuration_measurable b r hr).div_const 2

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_OuterJoinConfiguration
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma outer_finePower_integrable {m k : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration k → Finset (Fin k)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (ψ : H1Vector (k+m)) (st : Spins (k+m)) :
    Integrable (fun z => retainedFinePower b r ((outerJoinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2) := by
  have hw : Integrable (fun z => ‖ψ.value st z‖^2) :=
    (ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)
  apply (hw.const_mul (((k:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*k)).mono'
  · exact ((retainedFinePower_measurable b r hr).comp
      (measurable_snd.comp (outerJoinConfiguration m k).symm.continuous.measurable)).aestronglyMeasurable.mul hw.aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (mul_nonneg (retainedFinePower_nonneg ..) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (retainedFinePower_bound hb r _) (sq_nonneg _)

lemma ae_outer_block_position_injective (m k : ℕ) :
    ∀ᵐ z : Configuration (k+m), Function.Injective (position ((outerJoinConfiguration m k).symm z).2) := by
  filter_upwards [ae_position_injective (k+m)] with z hz
  intro i j hij
  have h : Fin.castAdd m i = Fin.castAdd m j := hz (by simpa only [outerJoinConfiguration_symm_snd, position_split_left] using hij)
  exact Fin.ext (congrArg (fun z : Fin (k+m) => z.val) h)

lemma ae_outer_fine_pair_bound {m k : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration k → Finset (Fin k)) :
    ∀ᵐ z : Configuration (k+m),
      retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2 ≤
        pairPotential ((outerJoinConfiguration m k).symm z).2 + ((2*Real.pi+1)/(2*b))*k := by
  filter_upwards [ae_outer_block_position_injective m k] with z hz
  have h := retained_fine_pair_lower hb (r ((outerJoinConfiguration m k).symm z).2)
    (position ((outerJoinConfiguration m k).symm z).2) hz
  have hc : ((r ((outerJoinConfiguration m k).symm z).2).card : ℝ) ≤ k := by
    exact_mod_cast (show (r ((outerJoinConfiguration m k).symm z).2).card ≤ k by simpa using Finset.card_le_univ (r ((outerJoinConfiguration m k).symm z).2))
  have hC : 0 ≤ (2*Real.pi+1)/(2*b) := by positivity
  have hh := mul_le_mul_of_nonneg_left hc hC
  change retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2 -
    ((2*Real.pi+1)/(2*b))*(r ((outerJoinConfiguration m k).symm z).2).card ≤
      pairPotential ((outerJoinConfiguration m k).symm z).2 at h
  linarith

lemma outer_fineCoulomb_integrable {m k : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration k → Finset (Fin k)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (ψ : H1Vector (k+m)) (st : Spins (k+m)) :
    Integrable (fun z => retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2) := by
  have hw : Integrable (fun z => ‖ψ.value st z‖^2) :=
    (ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)
  apply ((ψ.outer_pair_integrable st).add (hw.const_mul (((2*Real.pi+1)/(2*b))*k))).mono'
  · exact ((retainedFineCoulomb_measurable b r hr).comp
      (measurable_snd.comp (outerJoinConfiguration m k).symm.continuous.measurable)).aestronglyMeasurable.mul hw.aestronglyMeasurable
  · filter_upwards [ae_outer_fine_pair_bound (m:=m) hb r] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (retainedFineCoulomb_nonneg ..) (sq_nonneg _))]
    simpa only [add_mul, Pi.add_apply, outerJoinConfiguration_symm_snd] using mul_le_mul_of_nonneg_right hz (sq_nonneg ‖ψ.value st z‖)

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

noncomputable def conditionalEnergy {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (s : Spins m) (x : Configuration m) : ℝ :=
  form S (ψ.coreSlice s x).normalized - nuclearPotential S x + pairPotential x +
    potentialForm (crossPotential x) (ψ.coreSlice s x).normalized

lemma conditionalEnergy_weight {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (s : Spins m) (x : Configuration m) :
    mass (ψ.coreSlice s x) * conditionalEnergy S ψ s x =
      form S (ψ.coreSlice s x) -
        potentialForm (fun _ : Configuration k => nuclearPotential S x) (ψ.coreSlice s x) +
        potentialForm (fun _ : Configuration k => pairPotential x) (ψ.coreSlice s x) +
        potentialForm (crossPotential x) (ψ.coreSlice s x) := by
  simp only [conditionalEnergy, mul_add, mul_sub, form_normalized_weight,
    potentialForm_normalized_weight, potentialForm_const]
  ring

lemma conditionalEnergy_weight_integrable {M m k : ℕ} (S : Nuclei M)
    (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x) * conditionalEnergy S ψ s x) := by
  simp only [conditionalEnergy_weight]
  exact (((form_coreSlice_integrable S ψ s).sub
    (potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => nuclearPotential S x)
      (fun t => ψ.outer_nuclear_integrable S (Fin.append s t)))).add
    (potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => pairPotential x)
      (fun t => ψ.outer_pair_integrable (Fin.append s t)))).add
    (potentialForm_coreSlice_parameter_integrable ψ s crossPotential
      (fun t => ψ.cross_integrable (Fin.append s t)))

lemma conditional_energy_identity {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) :
    form S ψ = outerKinetic ψ +
      ∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) * conditionalEnergy S ψ s x := by
  have hi (s : Spins m) :
      (∫ x, mass (ψ.coreSlice s x) * conditionalEnergy S ψ s x) =
      (∫ x, form S (ψ.coreSlice s x)) -
      (∫ x, potentialForm (fun _ : Configuration k => nuclearPotential S x) (ψ.coreSlice s x)) +
      (∫ x, potentialForm (fun _ : Configuration k => pairPotential x) (ψ.coreSlice s x)) +
      (∫ x, potentialForm (crossPotential x) (ψ.coreSlice s x)) := by
    simp only [conditionalEnergy_weight]
    have hn := potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => nuclearPotential S x)
      (fun t => ψ.outer_nuclear_integrable S (Fin.append s t))
    have hp := potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => pairPotential x)
      (fun t => ψ.outer_pair_integrable (Fin.append s t))
    have hc := potentialForm_coreSlice_parameter_integrable ψ s crossPotential
      (fun t => ψ.cross_integrable (Fin.append s t))
    have hf := form_coreSlice_integrable S ψ s
    have H := integral_add ((hf.sub hn).add hp) hc
    simp only [Pi.sub_apply, Pi.add_apply] at H
    rw [H]
    have H' := integral_add (hf.sub hn) hp
    simp only [Pi.sub_apply] at H'
    rw [H', integral_sub hf hn]
  simp only [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [integral_potentialForm_coreSlice_parameter ψ (fun x _ => nuclearPotential S x)
      (ψ.outer_nuclear_integrable S),
    integral_potentialForm_coreSlice_parameter ψ (fun x _ => pairPotential x) ψ.outer_pair_integrable,
    integral_potentialForm_coreSlice_parameter ψ crossPotential ψ.cross_integrable]
  have hc := conditional_core_form_identity S ψ
  simp only [form_normalized_weight] at hc
  rw [hc]
  change kinetic ψ - nuclearEnergy S ψ + pairEnergy ψ = _
  rw [kinetic_split, nuclearEnergy_split, pairEnergy_split]
  simp only [potentialForm]
  ring

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SliceExpectation
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

lemma potentialForm_cross_eq_coreCoulomb {m k : ℕ} (x : Configuration m) (u : H1Vector k) :
    potentialForm (crossPotential x) u = ∑ i : Fin m, coreCoulombPotential u (position x i) := by
  change (∑ t : Spins k, ∫ y, crossPotential x y*‖u.value t y‖^2) = _
  rw [crossPotential_spin_integral]
  exact Finset.sum_congr rfl (fun i _ => nuclearEnergy_unit_eq_coreCoulomb u (position x i))

lemma conditionalEnergy_eq_screened {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (s : Spins m) (x : Configuration m) :
    conditionalEnergy S ψ s x = form S (ψ.coreSlice s x).normalized -
      (∑ i : Fin m, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)) + pairPotential x := by
  rw [conditionalEnergy, potentialForm_cross_eq_coreCoulomb]
  simp only [coreScreenedField, Finset.sum_sub_distrib, nuclearPotential]
  ring

lemma slice_weight_integrable_const {m k : ℕ} (ψ : H1Vector (m+k))
    (f : Configuration m → ℝ)
    (hf : ∀ st, Integrable (fun z => f ((joinConfiguration m k).symm z).1*‖ψ.value st z‖^2))
    (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*f x) := by
  have H := potentialForm_coreSlice_parameter_integrable ψ s (fun x _ => f x) (fun t => hf (Fin.append s t))
  apply H.congr
  exact Eventually.of_forall (fun x => by dsimp only; rw [potentialForm_const]; ring)

lemma retainedNuclearPotential_measurable {M m : ℕ} (S : Nuclei M)
    (r : Configuration m → Finset (Fin m)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (retainedNuclearPotential S r) :=
  measurable_retained_sum r hr _ (fun i => (attraction_measurable S).comp (positionCLM i).measurable)

lemma retainedCrossPotential_le {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (y : Configuration k) : retainedCrossPotential r x y ≤ crossPotential x y :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Finset.sum_nonneg (fun _ _ => coulombKernel_nonneg _))

lemma H1Vector.retained_outer_nuclear_integrable {M m k : ℕ} (ψ : H1Vector (m+k))
    (S : Nuclei M) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (st : Spins (m+k)) :
    Integrable (fun z => retainedNuclearPotential S r ((joinConfiguration m k).symm z).1*‖ψ.value st z‖^2) := by
  apply (ψ.outer_nuclear_integrable S st).mono'
  · exact ((retainedNuclearPotential_measurable S r hr).comp
      (measurable_fst.comp (joinConfiguration m k).symm.continuous.measurable)).aestronglyMeasurable.mul
        (((ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)).aestronglyMeasurable)
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (mul_nonneg (retainedNuclearPotential_nonneg ..) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (retainedNuclearPotential_le S r _) (sq_nonneg _)

lemma H1Vector.retained_cross_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    (r : Configuration m → Finset (Fin m)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (st : Spins (m+k)) :
    Integrable (fun z => retainedCrossPotential r ((joinConfiguration m k).symm z).1
      ((joinConfiguration m k).symm z).2*‖ψ.value st z‖^2) := by
  apply (ψ.cross_integrable st).mono'
  · exact ((retainedCrossPotential_measurable r hr).comp
      (joinConfiguration m k).symm.continuous.measurable).aestronglyMeasurable.mul
        (((ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)).aestronglyMeasurable)
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (mul_nonneg (retainedCrossPotential_nonneg ..) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (retainedCrossPotential_le r _ _) (sq_nonneg _)

lemma potentialForm_retainedCross_eq {m k : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (u : H1Vector k) :
    potentialForm (retainedCrossPotential r x) u = ∑ i ∈ r x, coreCoulombPotential u (position x i) := by
  have he (y : Configuration k) : retainedCrossPotential r x y =
      ∑ i ∈ r x, nuclearPotential (unitNucleus (position x i)) y := by
    unfold retainedCrossPotential nuclearPotential
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [attraction_unitNucleus, coulombKernel_sub_comm]
  unfold potentialForm
  simp_rw [he, Finset.sum_mul]
  have hi (s : Spins k) :
      (∫ y, ∑ i ∈ r x, nuclearPotential (unitNucleus (position x i)) y*‖u.value s y‖^2) =
      ∑ i ∈ r x, ∫ y, nuclearPotential (unitNucleus (position x i)) y*‖u.value s y‖^2 :=
    integral_finsetSum _ (fun i _ => u.nuclear_integrable (unitNucleus (position x i)) s)
  simp_rw [hi]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => nuclearEnergy_unit_eq_coreCoulomb u (position x i))

lemma retained_field_weight {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (r : Configuration m → Finset (Fin m)) (s : Spins m) (x : Configuration m) :
    mass (ψ.coreSlice s x)*(∑ i ∈ r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)) =
      mass (ψ.coreSlice s x)*retainedNuclearPotential S r x -
        potentialForm (retainedCrossPotential r x) (ψ.coreSlice s x) := by
  simp only [coreScreenedField, Finset.sum_sub_distrib, mul_sub]
  rw [←potentialForm_retainedCross_eq, potentialForm_normalized_weight]
  rfl

lemma retained_field_weight_integrable {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (r : Configuration m → Finset (Fin m)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*
      (∑ i ∈ r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i))) := by
  simp_rw [retained_field_weight]
  exact (slice_weight_integrable_const ψ _ (ψ.retained_outer_nuclear_integrable S r hr) s).sub
    (potentialForm_coreSlice_parameter_integrable ψ s (retainedCrossPotential r)
      (fun t => ψ.retained_cross_integrable r hr (Fin.append s t)))

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

lemma retainedFinePower_weight_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*retainedFinePower b r x) := by
  apply slice_weight_integrable_const ψ
  simpa only [outerJoinConfiguration_symm_snd] using outer_finePower_integrable hb r hr ψ
lemma retainedFineCoulomb_weight_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*retainedFineCoulomb b r x) := by
  apply slice_weight_integrable_const ψ
  simpa only [outerJoinConfiguration_symm_snd] using outer_fineCoulomb_integrable hb r hr ψ

lemma discreteFineTF_weight_integrable {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*discreteFineTF S ψ b r s x) := by
  simp only [discreteFineTF, mul_sub, mul_add, mul_left_comm (mass _) thomasFermiCoefficient]
  exact (((retainedFinePower_weight_integrable ψ hb r hr s).const_mul _).add
    (retainedFineCoulomb_weight_integrable ψ hb r hr s)).sub
    (retained_field_weight_integrable S ψ r hr s)

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_FineKernelShiftCoulombIntegrable
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

lemma retainedFineDensity_coulomb_eq {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) (a : Space)
    (hsep : ∀ i ∈ r, Real.sqrt 3*b ≤ ‖a-x i‖) :
    (∫ y, coulombKernel (a-y)*retainedFineDensity b r x y) = ∑ i ∈ r, coulombKernel (a-x i) := by
  simp only [retainedFineDensity, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => fineKernel_shift_coulomb_integrable hb a (x i))]
  exact Finset.sum_congr rfl (fun i hi => fineKernel_shift_coulomb_eq hb a (x i) (hsep i hi))

lemma coreCoulombPotential_fine_atom_eq {m : ℕ} (u : H1Vector m)
    {A : Set Space} (hu : SpatiallySupported u A) {b : ℝ} (hb : 0 < b) (a : Space)
    (hsep : ∀ z ∈ A, Real.sqrt 3*b ≤ ‖z-a‖) :
    (∫ y, coreCoulombPotential u y*fineKernel b (y-a)) = coreCoulombPotential u a := by
  rw [coreCoulombPotential_fubini u _ (fineKernel_shift_integrable hb a)]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x = 0
  · simp [he]
  · have ha : position x i ∈ A := (by_contra (fun hn => he (hx hn)) : x ∈ allPositions A) i
    rw [fineKernel_shift_coulomb_eq hb _ _ (hsep _ ha)]

lemma coreCoulombPotential_retainedFine_eq {m n : ℕ} (u : H1Vector m)
    {A : Set Space} (hu : SpatiallySupported u A) {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space)
    (hsep : ∀ z ∈ A, ∀ i ∈ r, Real.sqrt 3*b ≤ ‖z-x i‖) :
    (∫ y, coreCoulombPotential u y*retainedFineDensity b r x y) =
      ∑ i ∈ r, coreCoulombPotential u (x i) := by
  simp only [retainedFineDensity, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => coreCoulombPotential_mul_integrable u _ (fineKernel_shift_integrable hb (x i)))]
  exact Finset.sum_congr rfl (fun i hi => coreCoulombPotential_fine_atom_eq u hu hb (x i) (fun z hz => hsep z hz i hi))

lemma attraction_retainedFine_integrable {M n : ℕ} (S : Nuclei M) {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) :
    Integrable (fun y => attraction S y*retainedFineDensity b r x y) := by
  simp only [attraction, Finset.sum_mul]
  apply integrable_finsetSum
  intro j _
  have h := (retainedFineDensity_coulomb_integrable hb r x (S.position j)).const_mul (S.charge j)
  apply h.congr
  exact Eventually.of_forall (fun y => by dsimp only; rw [coulombKernel_sub_comm y]; ring)

lemma attraction_retainedFine_eq {M n : ℕ} (S : Nuclei M) {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space)
    (hsep : ∀ j i, i ∈ r → Real.sqrt 3*b ≤ ‖S.position j-x i‖) :
    (∫ y, attraction S y*retainedFineDensity b r x y) = ∑ i ∈ r, attraction S (x i) := by
  have hi (j : Fin M) : Integrable (fun y => S.charge j*(coulombKernel (S.position j-y)*retainedFineDensity b r x y)) :=
    (retainedFineDensity_coulomb_integrable hb r x (S.position j)).const_mul _
  simp only [attraction, Finset.sum_mul]
  simp_rw [coulombKernel_sub_comm _ (S.position _), mul_assoc]
  rw [integral_finsetSum _ (fun j _ => hi j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, retainedFineDensity_coulomb_eq hb r x _ (hsep j), Finset.mul_sum]

lemma coreScreenedField_retainedFine_eq {M m n : ℕ} (S : Nuclei M)
    (u : H1Vector m) {A : Set Space} (hu : SpatiallySupported u A) {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space)
    (hnuc : ∀ j i, i ∈ r → Real.sqrt 3*b ≤ ‖S.position j-x i‖)
    (hcore : ∀ z ∈ A, ∀ i ∈ r, Real.sqrt 3*b ≤ ‖z-x i‖) :
    (∫ y, coreScreenedField S u y*retainedFineDensity b r x y) =
      ∑ i ∈ r, coreScreenedField S u (x i) := by
  simp only [coreScreenedField,sub_mul]
  rw [integral_sub (attraction_retainedFine_integrable S hb r x)
    (coreCoulombPotential_mul_integrable u _ (retainedFineDensity_integrable hb r x)),
    attraction_retainedFine_eq S hb r x hnuc,
    coreCoulombPotential_retainedFine_eq u hu hb r x hcore, Finset.sum_sub_distrib]

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DensityCut
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma packetDensity_mono (g : 𝓢(Space,ℝ)) (ρ σ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ)
    (hsp : ∀ x, 0 ≤ σ x) (hsm : Measurable σ) (hsi : Integrable σ)
    (h : ∀ x, ρ x ≤ σ x) (x : Space) : packetDensity g ρ x ≤ packetDensity g σ x := by
  exact integral_mono (packetDensity_integrand_integrable g ρ hp hm hi x)
    (packetDensity_integrand_integrable g σ hsp hsm hsi x)
    (fun y => mul_le_mul_of_nonneg_left (h y) (sq_nonneg _))

lemma packetDensity_cut_tendsto (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ) (x : Space) :
    Tendsto (fun k => packetDensity g (densityCut ρ k) x) atTop (nhds (packetDensity g ρ x)) := by
  apply tendsto_integral_of_dominated_convergence (fun y => g (x-y)^2*ρ y)
    (fun k => (packetDensity_integrand_integrable g _ (densityCut_nonneg ρ hp k)
      (densityCut_measurable ρ hm k) (densityCut_integrable ρ hp hm hi k) x).1)
    (packetDensity_integrand_integrable g ρ hp hm hi x)
  · intro k
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (densityCut_nonneg ρ hp k y))]
    exact mul_le_mul_of_nonneg_left (densityCut_le ρ k y) (sq_nonneg _)
  · filter_upwards [] with y
    exact tendsto_const_nhds.mul (densityCut_tendsto ρ y)

lemma packetDensity_cut_weighted_tendsto (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ)
    (w : Space → ℝ) (hwp : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (hwi : Integrable (fun x => w x*packetDensity g ρ x)) :
    Tendsto (fun k => ∫ x, w x*packetDensity g (densityCut ρ k) x) atTop
      (nhds (∫ x, w x*packetDensity g ρ x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => w x*packetDensity g ρ x)
    (fun k => (hwm.mul (packetDensity_measurable g _ (densityCut_measurable ρ hm k))).aestronglyMeasurable) hwi
  · intro k
    filter_upwards [] with x
    change ‖w x*packetDensity g (densityCut ρ k) x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (hwp x) (packetDensity_nonneg g _ (densityCut_nonneg ρ hp k) x))]
    exact mul_le_mul_of_nonneg_left (packetDensity_mono g _ ρ (densityCut_nonneg ρ hp k)
      (densityCut_measurable ρ hm k) (densityCut_integrable ρ hp hm hi k) hp hm hi (densityCut_le ρ k) x) (hwp x)
  · filter_upwards [] with x
    exact tendsto_const_nhds.mul (packetDensity_cut_tendsto g ρ hp hm hi x)
end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_CoreScreenedFieldPacketIntegral
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb

theorem packet_core_trial {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤ form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*packetDensity g ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
          (packetDensity g ρ xy.1*packetDensity g ρ xy.2)) + ε := by
  have hconv := packetDensity_cut_weighted_tendsto g ρ hp hm hi (attraction S)
    (attraction_nonneg S) (attraction_measurable S) (packetDensity_nuclear_integrable S g ρ hp hm hi)
  have hevent : ∀ᶠ k : ℕ in atTop,
      (∫ x, attraction S x*packetDensity g ρ x)-ε/2 <
        ∫ x, attraction S x*packetDensity g (densityCut ρ k) x :=
    hconv (eventually_gt_nhds (sub_lt_self _ (half_pos hε)))
  obtain ⟨k,hk⟩ := hevent.exists
  let σ := densityCut ρ k
  have hsp := densityCut_nonneg ρ hp k
  have hsm := densityCut_measurable ρ hm k
  have hsi := densityCut_integrable ρ hp hm hi k
  have hst := densityCut_kinetic_integrable ρ hp hm ht k
  obtain ⟨n,ψ,ha,hmu',he⟩ := bounded_packet_core_trial S u hu hmu g hg hgc σ hsp hsm hsi hst
    (k:ℝ) (densityCut_bound ρ k) K A hK hA (densityCut_support ρ K hs k) hsu hsep (ε/2) (half_pos hε)
  have hmass : (∫ y, σ y) ≤ ∫ y, ρ y := integral_mono hsi hi (densityCut_le ρ k)
  have hkt : (∫ y, σ y^(5/3:ℝ)) ≤ ∫ y, ρ y^(5/3:ℝ) :=
    integral_mono hst ht (fun y => Real.rpow_le_rpow (hsp y) (densityCut_le ρ k y) (by norm_num))
  have hcf : 0 ≤ thomasFermiKineticConstant := by unfold thomasFermiKineticConstant; positivity
  have hkin := mul_le_mul_of_nonneg_left hkt hcf
  have hgrad : 0 ≤ ∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hmassgrad := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ) ≤ 1/2)) hgrad
  have hdle := packetDensity_mono g σ ρ hsp hsm hsi hp hm hi (densityCut_le ρ k)
  have hcore := integral_mono
    (coreCoulombPotential_mul_integrable u _ (packetDensity_integrable g σ hsp hsm hsi))
    (coreCoulombPotential_mul_integrable u _ (packetDensity_integrable g ρ hp hm hi))
    (fun x => mul_le_mul_of_nonneg_left (hdle x) (coreCoulombPotential_nonneg u x))
  have hdirect := integral_mono (packetDensity_pair_integrable g σ hsp hsm hsi)
    (packetDensity_pair_integrable g ρ hp hm hi) (fun xy =>
      mul_le_mul_of_nonneg_left (mul_le_mul (hdle xy.1) (hdle xy.2)
        (packetDensity_nonneg g σ hsp _) (packetDensity_nonneg g ρ hp _)) (coulombKernel_nonneg _))
  rw [coreScreenedField_packet_integral S u g σ hsp hsm hsi] at he
  refine ⟨n,ψ,ha,hmu',?_⟩
  rw [coreScreenedField_packet_integral S u g ρ hp hm hi]
  change (∫ x, attraction S x*packetDensity g ρ x)-ε/2 < ∫ x, attraction S x*packetDensity g σ x at hk
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketDensityReal
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb

lemma packetDensity_ofReal (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ) (x : Space) :
    ENNReal.ofReal (packetDensity g ρ x) = ∫⁻ y : Space, ENNReal.ofReal (g (x-y)^2*ρ y) :=
  ofReal_integral_eq_lintegral_ofReal (packetDensity_integrand_integrable g ρ hp hm hi x)
    (Eventually.of_forall (fun y => mul_nonneg (sq_nonneg _) (hp y)))

lemma packetDensity_product_ofReal (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ) (x y : Space) :
    ENNReal.ofReal (packetDensity g ρ x*packetDensity g ρ y) =
      ∫⁻ ac : Space × Space, ENNReal.ofReal (g (x-ac.1)^2*g (y-ac.2)^2) *
        ENNReal.ofReal (ρ ac.1*ρ ac.2) := by
  rw [ENNReal.ofReal_mul (packetDensity_nonneg g ρ hp x),packetDensity_ofReal g ρ hp hm hi x,
    packetDensity_ofReal g ρ hp hm hi y]
  have hx : Measurable (fun a : Space => ENNReal.ofReal (g (x-a)^2*ρ a)) :=
    (((g.continuous.measurable.comp (measurable_const.sub measurable_id)).pow_const 2).mul hm).ennreal_ofReal
  have hy : Measurable (fun c : Space => ENNReal.ofReal (g (y-c)^2*ρ c)) :=
    (((g.continuous.measurable.comp (measurable_const.sub measurable_id)).pow_const 2).mul hm).ennreal_ofReal
  rw [← lintegral_prod_mul hx.aemeasurable hy.aemeasurable]
  apply lintegral_congr
  intro ac
  simp only [ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_mul (hp _)]
  ring

lemma packetDensity_pair_lintegral (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ) :
    ENNReal.ofReal (∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
      (packetDensity g ρ xy.1*packetDensity g ρ xy.2)) =
    ∫⁻ ac : Space × Space, ENNReal.ofReal (ρ ac.1*ρ ac.2)*
      ENNReal.ofReal (∫ xy : Space × Space,
        g (xy.1-ac.1)^2*g (xy.2-ac.2)^2*coulombKernel (xy.1-xy.2)) := by
  let H (xy ac : Space × Space) : ℝ≥0∞ := ENNReal.ofReal (g (xy.1-ac.1)^2*g (xy.2-ac.2)^2)*
    ENNReal.ofReal (ρ ac.1*ρ ac.2)*ENNReal.ofReal (coulombKernel (xy.1-xy.2))
  have hH : Measurable (Function.uncurry H) := by
    unfold H Function.uncurry
    exact (((((g.continuous.measurable.comp (measurable_fst.fst.sub measurable_snd.fst)).pow_const 2).mul
      ((g.continuous.measurable.comp (measurable_fst.snd.sub measurable_snd.snd)).pow_const 2)).ennreal_ofReal).mul
      (((hm.comp measurable_snd.fst).mul (hm.comp measurable_snd.snd)).ennreal_ofReal)).mul
      ((coulombKernel_measurable.comp (measurable_fst.fst.sub measurable_fst.snd)).ennreal_ofReal)
  have he (ac : Space × Space) : (∫⁻ xy : Space × Space, H xy ac) =
      ENNReal.ofReal (ρ ac.1*ρ ac.2)*ENNReal.ofReal (∫ xy : Space × Space,
        g (xy.1-ac.1)^2*g (xy.2-ac.2)^2*coulombKernel (xy.1-xy.2)) := by
    have hm' (a : Space) : Measurable (fun x : Space => g (x-a)^2) :=
      (g.continuous.measurable.comp (measurable_id.sub measurable_const)).pow_const 2
    have hb (c x : Space) : ‖g (x-c)^2‖ ≤ (SchwartzMap.seminorm ℝ 0 0 g)^2 := by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact schwartz_square_le g _
    have hij := coulomb_pair_integrable (window_shift_integrable g ac.1) (hm' ac.1)
      (window_shift_integrable g ac.2) (hm' ac.2) (hb ac.2)
    rw [ofReal_integral_eq_lintegral_ofReal hij (Eventually.of_forall (fun xy =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (coulombKernel_nonneg _)))]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro xy
    dsimp only [H]
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    ac_rfl
  have hI := ofReal_integral_eq_lintegral_ofReal (packetDensity_pair_integrable g ρ hp hm hi)
    (Eventually.of_forall (fun xy => mul_nonneg (coulombKernel_nonneg _)
      (mul_nonneg (packetDensity_nonneg g ρ hp _) (packetDensity_nonneg g ρ hp _))))
  rw [hI]
  calc
    _ = ∫⁻ xy : Space × Space, ∫⁻ ac : Space × Space, H xy ac := by
      apply lintegral_congr
      intro xy
      rw [ENNReal.ofReal_mul (coulombKernel_nonneg _),packetDensity_product_ofReal g ρ hp hm hi]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro ac
      dsimp only [H]
      ac_rfl
    _ = ∫⁻ ac : Space × Space, ∫⁻ xy : Space × Space, H xy ac :=
      lintegral_lintegral_swap hH.aemeasurable
    _ = _ := lintegral_congr he

lemma radial_packetDensity_pair_le (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ)
    (hD : Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2))) :
    (∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(packetDensity g ρ xy.1*packetDensity g ρ xy.2)) ≤
      ∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2) := by
  have hpos : 0 ≤ ∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2) :=
    integral_nonneg (fun xy => mul_nonneg (coulombKernel_nonneg _) (mul_nonneg (hp _) (hp _)))
  apply (ENNReal.ofReal_le_ofReal_iff hpos).mp
  rw [packetDensity_pair_lintegral g ρ hp hm hi,
    ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall (fun xy =>
      mul_nonneg (coulombKernel_nonneg _) (mul_nonneg (hp _) (hp _))))]
  apply lintegral_mono_ae
  have hne : ∀ᵐ ac : Space × Space ∂(volume : Measure Space).prod volume, ac.1 ≠ ac.2 := by
    apply (Measure.ae_prod_iff_ae_ae (p := fun ac : Space × Space => ac.1 ≠ ac.2)
      ((measurableSet_eq_fun measurable_fst measurable_snd).compl)).mpr
    filter_upwards [] with a
    have h : ∀ᵐ c : Space, c ≠ a := by rw [ae_iff]; simp
    exact h.mono (fun c hc => Ne.symm hc)
  filter_upwards [hne] with ac hac
  rw [ENNReal.ofReal_mul (coulombKernel_nonneg _),mul_comm (ENNReal.ofReal (coulombKernel _))]
  gcongr
  exact window_shape_pair_le g hg hrad hac
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_SectorFormBottom
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

theorem radial_packet_core_trial {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤ form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*packetDensity g ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) + ε := by
  have hi := compact_density_integrable ρ hp hm ht K hK hs
  obtain ⟨n,ψ,ha,hmass,he⟩ := packet_core_trial S u hu hmu g hg hgc ρ hp hm hi ht
    K A hK hA hs hsu hsep ε hε
  have hD := radial_packetDensity_pair_le g hg hrad ρ hp hm hi
    (density_coulomb_pair_integrable ρ hp hm hi ht)
  exact ⟨n,ψ,ha,hmass,by linarith⟩

theorem trial_in_hole {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ))) :
    unrestrictedFormBottom S ≤ ((form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*packetDensity g ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) : ℝ) : EReal) := by
  let B : ℝ := form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*packetDensity g ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2))
  change unrestrictedFormBottom S ≤ (B:EReal)
  apply EReal.le_of_forall_lt_iff_le.mp
  intro z hz
  have hpz : 0 < z-B := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hz)
  obtain ⟨n,ψ,ha,hmass,he⟩ := radial_packet_core_trial S u hu hmu g hg hgc hrad ρ hp hm ht
    K A hK hA hs hsu hsep (z-B) hpz
  have hel : form S ψ ≤ z := by change form S ψ ≤ B+(z-B) at he; linarith
  exact (unrestrictedFormBottom_le_trial S ψ ha hmass).trans (EReal.coe_le_coe hel)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_WindowCoulomb
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb

theorem source_free_trial_in_hole {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (hcore : ∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖)
    (hnuc : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) : ℝ) : EReal) := by
  have H := trial_in_hole S u hu hmu g hg hgc hrad ρ hp hm ht K A hK hA hs hsu hsep
  rw [coreScreenedField_packet_eq S u hsu g hg hrad hR hgs ρ hp hm
    (compact_density_integrable ρ hp hm ht K hK hs) hcore hnuc] at H
  exact H

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawThomasFermiEnergy
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb

lemma discreteFineTF_eq_raw {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m)) (s : Spins m) (x : Configuration m)
    {A : Set Space} (hu : SpatiallySupported (ψ.coreSlice s x).normalized A)
    (hnuc : ∀ j i, i ∈ r x → Real.sqrt 3*b ≤ ‖S.position j-position x i‖)
    (hcore : ∀ z ∈ A, ∀ i ∈ r x, Real.sqrt 3*b ≤ ‖z-position x i‖) :
    discreteFineTF S ψ b r s x = rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
      (retainedFineDensity b (r x) (position x)) := by
  unfold discreteFineTF rawThomasFermiEnergy retainedFinePower retainedFineCoulomb
  rw [coreScreenedField_retainedFine_eq S (ψ.coreSlice s x).normalized hu hb (r x) (position x) hnuc hcore]
  ring

lemma source_free_trial_raw {M k : ℕ} (S : Nuclei M) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (hcore : ∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖)
    (hnuc : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u+rawThomasFermiEnergy (coreScreenedField S u) ρ+
      (1/2:ℝ)*(∫ y, ρ y)*(∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2) : ℝ) : EReal) := by
  have H := source_free_trial_in_hole S u hu hmu g hg hgc hrad hR hgs ρ hp hm ht K A hK hA hs hsu hsep hcore hnuc
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  have he : coulombBilinear ρ ρ =
      ∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2) := by
    unfold coulombBilinear
    apply integral_congr_ae; exact Eventually.of_forall (fun _ => by ring)
  unfold rawThomasFermiEnergy
  rw [he]
  unfold thomasFermiCoefficient thomasFermiKineticConstant
  ring

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfPotential
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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
include hΩ
lemma tfCoulomb_eq_field (f g : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω f g = tfFieldContinuous (tfPotentialField hΩ g) f := by
  rw [tfCoulomb_eq_potential hΩ,tfFieldContinuous_apply]
  apply integral_congr_ae
  filter_upwards [tfPotentialField_coe hΩ g] with x hx
  rw [hx,mul_comm]
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
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_TfGradientField
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
noncomputable def tfGradientField (c : ℝ) (W : TFLq (volume.restrict Ω))
    (f : TFLp (volume.restrict Ω)) : TFLq (volume.restrict Ω) :=
  (c*(5/3:ℝ)) • tfKineticField f-W+tfPotentialField hΩ f
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfExtendNonneg
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise
namespace Coulomb

lemma tfDensity_nonneg {Ω : Set Space} (f : TFLp (volume.restrict Ω)) (x : Space) :
    0 ≤ tfDensity Ω f x := le_max_right _ _

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScaledTest
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

lemma countTest_one (y : Space) {a : ℝ} (ha : 0<a) {x : Space} (hx : ‖x-y‖≤a) : countTest y a x=1 := by
  apply cutSeed_one
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),←div_eq_inv_mul]
  exact (div_le_one ha).mpr hx

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFCountTest
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

lemma rawTFBregman_nonneg {ρ σ : Space → ℝ}
    (hρ : ∀ᵐ x, 0≤ρ x) (hσ : ∀ᵐ x, 0≤σ x) : 0 ≤ rawTFBregman ρ σ := by
  apply mul_nonneg thomasFermiKineticConstant_pos.le
  apply integral_nonneg_of_ae
  filter_upwards [hρ,hσ] with x hx hy
  exact tf_power_tangent hx hy

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_FineCountTest
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

lemma fineKernel_eq_zero_of_two_mul_lt {b : ℝ} (hb : 0<b) (z : Space) (hz : 2*b<‖z‖) :
    fineKernel b z=0 := by
  apply fineKernel_eq_zero hb
  nlinarith [sq_nonneg (‖z‖-2*b)]

lemma patchRetained_mem {n : ℕ} (y : Space) (t b : ℝ) (x : Configuration n) (i : Fin n) :
    i∈patchRetained y t b x ↔ ‖position x i-y‖<t-7*b := by simp [patchRetained]

lemma patchRetained_measurable {n : ℕ} (y : Space) (t b : ℝ) (i : Fin n) :
    MeasurableSet {x : Configuration n | i∈patchRetained y t b x} := by
  simp only [patchRetained_mem]
  exact measurableSet_lt (((continuous_position i).sub continuous_const).norm.measurable) measurable_const

lemma fineKernel_countTest_one {a b : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 4*b≤a)
    (y : Space) {w : Space} (hw : ‖w-y‖≤a) :
    (∫ z, fineKernel b (z-w)*countTest y (3*a/2) z)=1 := by
  rw [←fineKernel_shift_integral hb w]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : fineKernel b (z-w)=0
  · simp only [hz,zero_mul]
  have hn : ‖z-w‖≤2*b := le_of_not_gt (fun h => hz (fineKernel_eq_zero_of_two_mul_lt hb _ h))
  rw [countTest_one y (by positivity) (le_trans (norm_sub_le_norm_sub_add_norm_sub z w y) (by linarith)),mul_one]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FieldSubmean
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

lemma coreField_aestronglyMeasurable {J k : ℕ} (S : Nuclei J) (u : H1Vector k) :
    AEStronglyMeasurable (coreScreenedField S u) volume :=
  (attraction_measurable S).aestronglyMeasurable.sub (coreCoulombPotential_aestronglyMeasurable u)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FarSubmean
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

lemma recordedFarField_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) :
    AEStronglyMeasurable (recordedFarField S u x A) volume :=
  ((attraction_measurable S).aestronglyMeasurable.sub (restrictedCorePotential_aestronglyMeasurable u hA)).sub
    (restrictedOutPotential_measurable x A).aestronglyMeasurable

theorem recordedFarField_positive_submean_square {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) {a : ℝ} (ha : 0 < a) (z w : Space)
    (hw : ‖w-z‖ ≤ a) (hcore : ∀ v ∈ A, 4*a ≤ ‖v-z‖)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-z‖) :
    (max (recordedFarField S u x A w) 0)^2 ≤
      8*(∫ v, (max (recordedFarField S u x A v) 0)^2*ballCloud z (2*a) 1 v) := by
  have hsep (v : Space) (hv : 4*a ≤ ‖v-z‖) : 2*a ≤ ‖v-w‖ := by
    have ht : ‖v-z‖ ≤ ‖v-w‖+‖w-z‖ := by simpa only [dist_eq_norm] using dist_triangle v w z
    linarith
  let f := recordedFarField S u x A
  have hci := recordedFarField_ballCloud_integrable S u x hA ha w
  have hpi := positive_ballCloud_integrable ha w f hci
  have hmeas := recordedFarField_aestronglyMeasurable S u x hA
  have hbound := recordedFarField_le_attraction S u x A
  have hsi := positive_square_ballCloud_integrable S f hmeas hbound ha w (fun j => hsep _ (hnuc j))
  have hsz := positive_square_ballCloud_integrable S f hmeas hbound (by linarith : 0 < 2*a) z
    (fun j => by linarith [hnuc j])
  have hmean : f w=∫ v, f v*ballCloud w a 1 v :=
    (recordedFarField_ballCloud S u x hA ha w
      (fun v hv => le_trans (by linarith) (hsep _ (hcore v hv)))
      (fun j => le_trans (by linarith) (hsep _ (hnuc j)))).symm
  have hpmean : max (f w) 0 ≤ ∫ v, max (f v) 0*ballCloud w a 1 v := by
    apply max_le
    · rw [hmean]
      exact integral_mono hci hpi (fun v => mul_le_mul_of_nonneg_right (le_max_left _ _)
        (uniformBall_nonneg ha zero_le_one (v-w)))
    · exact integral_nonneg (fun v => mul_nonneg (le_max_right _ _) (uniformBall_nonneg ha zero_le_one (v-w)))
  calc
    _ ≤ (∫ v, max (f v) 0*ballCloud w a 1 v)^2 := pow_le_pow_left₀ (le_max_right _ _) hpmean 2
    _ ≤ ∫ v, (max (f v) 0)^2*ballCloud w a 1 v :=
      square_weighted_mean_le volume _ _ (ballCloud_integrable a 1 w)
        (fun v => uniformBall_nonneg ha zero_le_one (v-w)) (ballCloud_mass ha 1 w) hpi hsi
    _ ≤ _ := by
      rw [← integral_const_mul]
      apply integral_mono hsi (hsz.const_mul 8)
      intro v
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (ballCloud_nested_le ha z w v hw)
        (sq_nonneg (max (f v) 0))

theorem coreField_le_local_far_cap {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {a : ℝ} (ha : 0 < a) (z w : Space)
    (hw : ‖w-z‖ ≤ a) (hnuc : ∀ j, 4*a ≤ ‖S.position j-z‖) :
    coreScreenedField S u w ≤
      Real.sqrt (8*(∫ v, (max (recordedFarField S u x {v | 4*a ≤ ‖v-z‖} v) 0)^2*ballCloud z (2*a) 1 v))+
      (m:ℝ)/(3*a) := by
  let A : Set Space := {v | 4*a ≤ ‖v-z‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const (by fun_prop)).measurableSet
  have H := recordedFarField_positive_submean_square S u x hA ha z w hw (fun _ h => h) hnuc
  have hpos : 0 ≤ 8*(∫ v, (max (recordedFarField S u x A v) 0)^2*ballCloud z (2*a) 1 v) := by
    apply mul_nonneg (by norm_num)
    exact integral_nonneg (fun v => mul_nonneg (sq_nonneg _) (uniformBall_nonneg (by linarith) zero_le_one (v-z)))
  have HB := (Real.le_sqrt (le_max_right _ _) hpos).2 H
  have HO : restrictedOutPotential x A w ≤ (m:ℝ)/(3*a) := by
    apply restrictedOutPotential_le x A (by positivity) w
    intro v hv
    have ht : ‖v-z‖ ≤ ‖v-w‖+‖w-z‖ := by simpa only [dist_eq_norm] using dist_triangle v w z
    change 4*a ≤ ‖v-z‖ at hv
    linarith
  have HC := coreField_le_far_addback S u x hA w
  have HE := le_max_left (recordedFarField S u x A w) 0
  change coreScreenedField S u w ≤ Real.sqrt (8*(∫ v, (max (recordedFarField S u x A v) 0)^2*ballCloud z (2*a) 1 v))+(m:ℝ)/(3*a)
  linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_BallTrial
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
noncomputable section
namespace Coulomb

theorem ballCloud_trial {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ z, g z = g (EuclideanSpace.single 0 ‖z‖))
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (hgs : ∀ z, a < ‖z‖ → g z = 0)
    (y : Space) (A : Set Space) (hA : IsClosed A) (hsu : SpatiallySupported u A)
    (hcore : ∀ z ∈ A, 3*a ≤ ‖z-y‖) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u-M*coreScreenedField S u y+
      ballKineticCoefficient*M^(5/3:ℝ)/a^2 + (1/2:ℝ)*M*
      (∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2)+
      (5/4:ℝ)*M^2/a : ℝ) : EReal) := by
  have hd : ∀ z x : Space, 3*a ≤ ‖z-y‖ → ballCloud y a M x ≠ 0 → a ≤ ‖z-x‖ := by
    intro z x hz hx
    have H := norm_sub_le_norm_sub_add_norm_sub z x y
    have hx' := ballCloud_ne_zero_norm y x hx
    linarith
  have H := source_free_trial_raw S u hu hmu g hg hgc hrad ha hgs (ballCloud y a M)
    (fun z => uniformBall_nonneg ha hM (z-y)) (ballCloud_measurable a M y)
    ((uniformBall_power_integrable a M).comp_sub_right y) (Metric.closedBall y a) A
    (isCompact_closedBall y a) hA (ballCloud_support y) hsu
    (ballCloud_separated_window ha y g hgs hcore)
    (fun z hz x hx => hd z x (hcore z hz) hx) (fun j x hx => hd (S.position j) x (hnuc j) hx)
  rw [ballCloud_mass ha] at H
  apply H.trans
  apply EReal.coe_le_coe_iff.mpr
  have HT := ballCloud_rawTF_bound S u hsu ha hM y
    (fun z hz => (by linarith [hcore z hz] : a ≤ ‖z-y‖))
    (fun j => (by linarith [hnuc j] : a ≤ ‖S.position j-y‖))
  linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PositiveField
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
noncomputable section
namespace Coulomb

theorem positive_field_ball_trial {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (y : Space) (A : Set Space) (hA : IsClosed A) (hsu : SpatiallySupported u A)
    (hcore : ∀ z ∈ A, 3*a ≤ ‖z-y‖) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u-M*coreScreenedField S u y+
      ballTrialCoefficient*(M^(5/3:ℝ)/a^2+M/a^2+M^2/a) : ℝ) : EReal) := by
  have H := ballCloud_trial S u hu hmu (scaledWindow unitWindow a ha.ne')
    (by rw [scaledWindow_mass unitWindow ha,unitWindow_mass])
    (scaledWindow_compactSupport unitWindow unitWindow_support ha)
    (scaledWindow_radial unitWindow unitWindow_radial ha)
    ha hM (scaledWindow_support unitWindow unitWindow_support ha)
    y A hA hsu hcore hnuc
  rw [scaledWindow_kinetic unitWindow ha] at H
  apply H.trans
  apply EReal.coe_le_coe_iff.mpr
  have hc : ballKineticCoefficient ≤ ballTrialCoefficient := by
    unfold ballTrialCoefficient
    linarith [unitWindow_kinetic_nonneg]
  have hg : (1/2:ℝ)*(∑ b : Fin 3, ∫ x : Space,
      (fderiv ℝ unitWindow x (EuclideanSpace.single b 1))^2) ≤ ballTrialCoefficient := by
    unfold ballTrialCoefficient
    linarith [ballKineticCoefficient_pos]
  have he : (5/4:ℝ) ≤ ballTrialCoefficient := by
    unfold ballTrialCoefficient
    linarith [ballKineticCoefficient_pos,unitWindow_kinetic_nonneg]
  have Hc := mul_le_mul_of_nonneg_right hc (show 0 ≤ M^(5/3:ℝ)/a^2 by positivity)
  have Hg := mul_le_mul_of_nonneg_right hg (show 0 ≤ M/a^2 by positivity)
  have He := mul_le_mul_of_nonneg_right he (show 0 ≤ M^2/a by positivity)
  linear_combination Hc+Hg+He

theorem positive_field_core_gain {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    {a m : ℝ} (ha : 0 < a) (hm : 0 ≤ m)
    (ham : 1 ≤ a*m) (ham' : 1 ≤ a*m^(1/3:ℝ))
    (y : Space) (A : Set Space) (hA : IsClosed A) (hsu : SpatiallySupported u A)
    (hcore : ∀ z ∈ A, 3*a ≤ ‖z-y‖) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u-a*(max (coreScreenedField S u y) 0)^2/
      (16*ballTrialCoefficient)+4*ballTrialCoefficient*m^2/a : ℝ) : EReal) := by
  by_cases hb : unrestrictedFormBottom S = ⊥
  · simp [hb]
  have ht : unrestrictedFormBottom S ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (unrestrictedFormBottom_le_trial S u hu hmu)
  rw [←EReal.coe_toReal ht hb]
  apply EReal.coe_le_coe_iff.mpr
  apply positive_field_trial_optimization ha ballTrialCoefficient_pos hm ham ham'
  intro M hM
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_toReal ht hb]
  exact positive_field_ball_trial S u hu hmu ha hM y A hA hsu hcore hnuc

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalPositiveField
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
noncomputable section
namespace Coulomb

theorem conditional_positive_field_gain {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k))
    (hanti : ∀ s, ∀ᵐ x, Antisymmetric (ψ.coreSlice s x))
    {a : ℝ} (ha : 0 < a) (y : Space) (A : Set Space) (hA : IsClosed A)
    (hs : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized A)
    (hcore : ∀ z ∈ A, 3*a ≤ ‖z-y‖) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖)
    {E : ℝ} (hE : (E : EReal) ≤ unrestrictedFormBottom S) :
    a/(16*ballTrialCoefficient)*sliceExpectation ψ (fun s x =>
      (max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2) ≤
      sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized)-E*mass ψ+
        (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*mass ψ := by
  have hi := normalized_coreForm_weight_integrable S ψ
  have hp := coreField_positive_square_weight_integrable S ψ
  let c : ℝ := a/(16*ballTrialCoefficient)
  let d : ℝ := 4*ballTrialCoefficient*(screenBaseMass a)^2/a
  have HD (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(form S (ψ.coreSlice s x).normalized-
      c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2+d-E)) := by
    apply (((hi s).sub (by simpa only [mul_left_comm (mass _) c] using (hp s y).const_mul c)).add
      (by simpa only [mul_comm (mass _) d] using (mass_coreSlice_integrable ψ s).const_mul d)).sub
      (by simpa only [mul_comm (mass _) E] using (mass_coreSlice_integrable ψ s).const_mul E) |>.congr
    exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply,Pi.add_apply]; ring)
  have H : 0 ≤ sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized-
      c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2+d-E) := by
    apply Finset.sum_nonneg
    intro s _
    apply integral_nonneg_of_ae
    filter_upwards [hanti s,hs s] with x hax hsx
    by_cases hz : mass (ψ.coreSlice s x)=0
    · simp [hz]
    · have hpx : 0 < mass (ψ.coreSlice s x) := lt_of_le_of_ne (mass_nonneg _) (Ne.symm hz)
      have HG := positive_field_core_gain S (ψ.coreSlice s x).normalized hax.normalized
        (mass_normalized _ hpx) ha (screenBaseMass_nonneg a) (screenBaseMass_scale ha)
        (screenBaseMass_cuberoot_scale ha) y A hA hsx hcore hnuc
      have HE := EReal.coe_le_coe_iff.mp (hE.trans HG)
      apply mul_nonneg hpx.le
      dsimp [c,d]
      convert sub_nonneg.mpr HE using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | ring
  have HH : sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized-
      c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2+d-E) =
      sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized)-
      c*sliceExpectation ψ (fun s x => (max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2)+
      d*mass ψ-E*mass ψ := by
    have hconst (v : ℝ) (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*v) :=
      (mass_coreSlice_integrable ψ s).mul_const v
    have hc (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(c*
        (max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2)) := by
      simpa only [mul_left_comm (mass _) c] using (hp s y).const_mul c
    have hd (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(form S (ψ.coreSlice s x).normalized-
        c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2)) := by
      exact ((hi s).sub (hc s)).congr (Eventually.of_forall (fun x => by dsimp; ring))
    have he (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(form S (ψ.coreSlice s x).normalized-
        c*(max (coreScreenedField S (ψ.coreSlice s x).normalized y) 0)^2+d)) := by
      exact ((hd s).add (hconst d s)).congr (Eventually.of_forall (fun x => by dsimp; ring))
    rw [sliceExpectation_sub ψ _ _ he (hconst E),sliceExpectation_add ψ _ _ hd (hconst d),
      sliceExpectation_sub ψ _ _ hi hc,sliceExpectation_const_mul,
      sliceExpectation_number,sliceExpectation_number]
  rw [HH] at H
  dsimp [c,d] at H
  linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawObservable
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

lemma restrictedOutPotential_join {m k : ℕ} (x : Configuration m) (v : Configuration k)
    (A : Set Space) (y : Space) :
    restrictedOutPotential (joinConfiguration m k (x,v)) A y =
      restrictedOutPotential x A y+restrictedOutPotential v A y := by
  simp only [restrictedOutPotential,Fin.sum_univ_add,position_join_left,position_join_right]

lemma coreConditionalObservable_rawSignedField {m k : ℕ} (u : H1Vector (m+k))
    (V : ℝ) {A : Set Space} (hA : MeasurableSet A) (y : Space) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) (s : Spins m) (x : Configuration m)
    (hm : 0 < mass (u.coreSlice s x)) :
    coreConditionalObservable u (rawSignedField V A y) s x =
      V-restrictedCorePotential (u.coreSlice s x).normalized A y-restrictedOutPotential x A y := by
  unfold coreConditionalObservable
  have he : (fun v => rawSignedField V A y (joinConfiguration m k (x,v))) =
      rawSignedField (V-restrictedOutPotential x A y) A y := by
    funext v
    simp only [rawSignedField,restrictedOutPotential_join]
    ring
  rw [he,potentialForm_rawSignedField _ _ hA y hr hsep,mass_normalized _ hm,mul_one]
  ring

lemma coreConditionalObservable_raw_positive_weight {m k : ℕ} (u : H1Vector (m+k))
    (V : ℝ) {A : Set Space} (hA : MeasurableSet A) (y : Space) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) (s : Spins m) (x : Configuration m) :
    mass (u.coreSlice s x)*(max (coreConditionalObservable u (rawSignedField V A y) s x) 0)^2 =
      mass (u.coreSlice s x)*(max (V-restrictedCorePotential (u.coreSlice s x).normalized A y-
        restrictedOutPotential x A y) 0)^2 := by
  by_cases h : mass (u.coreSlice s x)=0
  · simp only [h,zero_mul]
  · rw [coreConditionalObservable_rawSignedField u V hA y hr hsep s x
      (lt_of_le_of_ne (mass_nonneg _) (Ne.symm h))]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_JointSlice
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

lemma recordedFarField_normalized_slice_joint {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) {A : Set Space} (hA : MeasurableSet A) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      recordedFarField S (u.coreSlice s z.1).normalized z.1 A z.2) (volume.prod volume) := by
  exact ((attraction_measurable S).comp measurable_snd).aestronglyMeasurable.sub
    (restrictedCorePotential_normalized_slice_joint u s hA) |>.sub
    (restrictedOutPotential_joint_measurable hA).aestronglyMeasurable

lemma farSquare_mass_ballCloud_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) {A : Set Space} (hA : MeasurableSet A)
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    Integrable (fun z : Configuration m × Space => mass (u.coreSlice s z.1)*
      (max (recordedFarField S (u.coreSlice s z.1).normalized z.1 A z.2) 0)^2*
      ballCloud y a 1 z.2) (volume.prod volume) := by
  let K := (totalCharge S/a)^2
  have hm := (mass_coreSlice_integrable u s).aestronglyMeasurable.comp_fst (ν := (volume : Measure Space))
  have hf := ((recordedFarField_normalized_slice_joint S u s hA).sup
    (aestronglyMeasurable_const (b:=(0:ℝ)))).pow 2
  have hb : Measurable (fun z : Configuration m × Space => ballCloud y a 1 z.2) :=
    (ballCloud_measurable a 1 y).comp measurable_snd
  apply (((mass_coreSlice_integrable u s).mul_prod (ballCloud_integrable a 1 y)).const_mul K).mono'
    ((hm.mul hf).mul hb.aestronglyMeasurable)
  filter_upwards [] with z
  change ‖mass (u.coreSlice s z.1)*
    (max (recordedFarField S (u.coreSlice s z.1).normalized z.1 A z.2) 0)^2*ballCloud y a 1 z.2‖ ≤ _
  have hball : 0 ≤ ballCloud y a 1 z.2 := uniformBall_nonneg ha zero_le_one (z.2-y)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mass_nonneg _) (sq_nonneg _)) hball)]
  by_cases hz : z.2-y ∈ Metric.ball (0:Space) a
  · have hdist : ‖z.2-y‖ < a := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have hsep (j : Fin J) : a ≤ ‖z.2-S.position j‖ := by
      have ht : ‖S.position j-y‖ ≤ ‖S.position j-z.2‖+‖z.2-y‖ := by
        simpa only [dist_eq_norm] using dist_triangle (S.position j) z.2 y
      rw [norm_sub_rev (S.position j) z.2] at ht
      linarith [hnuc j]
    have hP : max (recordedFarField S (u.coreSlice s z.1).normalized z.1 A z.2) 0 ≤ totalCharge S/a :=
      (max_le (recordedFarField_le_attraction S _ _ A z.2) (attraction_nonneg S z.2)).trans
        (attraction_le_totalCharge_div S ha z.2 hsep)
    have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_max_right _ _) hP 2) (mass_nonneg (u.coreSlice s z.1))) hball
    dsimp [K]
    nlinarith
  · simp only [ballCloud,uniformBall,indicator_of_notMem hz,mul_zero,le_refl]

theorem sliceExpectation_farSquare_ballCloud {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {A : Set Space} (hA : MeasurableSet A)
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    sliceExpectation u (fun s x => ∫ v,
      (max (recordedFarField S (u.coreSlice s x).normalized x A v) 0)^2*ballCloud y a 1 v) =
    ∫ v, (sliceExpectation u (fun s x =>
      (max (recordedFarField S (u.coreSlice s x).normalized x A v) 0)^2))*ballCloud y a 1 v := by
  unfold sliceExpectation
  simp only [←integral_const_mul,Finset.sum_mul,←integral_mul_const]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s hs
    have H := integral_integral_swap (f := fun x v => mass (u.coreSlice s x)*
      (max (recordedFarField S (u.coreSlice s x).normalized x A v) 0)^2*ballCloud y a 1 v)
      (farSquare_mass_ballCloud_integrable S u s hA ha y hnuc)
    simpa only [mul_assoc] using H
  · intro s hs
    exact (farSquare_mass_ballCloud_integrable S u s hA ha y hnuc).integral_prod_right

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_LpParameter
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

lemma coreScreenedField_memLp {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖) :
    MemLp (coreScreenedField S u) TFFieldExponent (volume.restrict Ω) := by
  let C := ∑ s : Spins k, ∑ i : Fin k,
      (4*(∑ b : Fin 3, ∫ x, ‖u.gradient s (i,b) x‖^2)+(1/4:ℝ)*(∫ x, ‖u.value s x‖^2))
  apply MemLp.of_bound ((coreField_aestronglyMeasurable S u).mono_measure Measure.restrict_le_self)
    (totalCharge S/d+C)
  filter_upwards [ae_restrict_mem hΩ] with x hx
  have ha := attraction_le_totalCharge_div S hd x (fun j => hn j x hx)
  have hc : coreCoulombPotential u x≤C := coreCoulombPotential_bound u x
  have hp := coreCoulombPotential_nonneg u x
  have hA := attraction_nonneg S x
  have hC : 0≤C := hp.trans hc
  have hT : 0≤totalCharge S/d := hA.trans ha
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  dsimp [coreScreenedField]
  constructor <;> linarith

def coreTFField {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖) : TFLq (volume.restrict Ω) :=
  (coreScreenedField_memLp S u hΩ hd hn).toLp _

lemma coreTFField_coe {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖) :
    coreTFField S u hΩ hd hn =ᵐ[volume.restrict Ω] coreScreenedField S u := MemLp.coeFn_toLp _

lemma coreScreenedField_normalized_slice_joint {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      coreScreenedField S (u.coreSlice s z.1).normalized z.2) (volume.prod volume) := by
  have H := restrictedCorePotential_normalized_slice_joint u s MeasurableSet.univ
  have he (v : H1Vector k) : restrictedCorePotential v univ=coreCoulombPotential v := by
    funext x
    simp only [restrictedCorePotential,mem_univ,ite_true,coreCoulombPotential]
  simp_rw [he] at H
  exact ((attraction_measurable S).comp measurable_snd).aestronglyMeasurable.sub H

lemma coreTFField_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m)
    {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖) :
    AEStronglyMeasurable (fun x => coreTFField S (u.coreSlice s x).normalized hΩ hd hn) volume := by
  apply tfField_parameter_aestronglyMeasurable _
    (fun z => coreScreenedField S (u.coreSlice s z.1).normalized z.2)
  · exact (coreScreenedField_normalized_slice_joint S u s).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  · exact Eventually.of_forall (fun x => coreTFField_coe S _ hΩ hd hn)

end Coulomb

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

lemma coreTF_conditional_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    (s : Spins m) {d : ℝ} (hd : 0<d) (hn : ∀ j x, x∈Ω → d≤‖x-S.position j‖)
    {D : ℝ} (hD : 0<D) (hdiam : ∀ x∈Ω, ∀ y∈Ω, ‖x-y‖≤D)
    (F : Configuration m → ℝ) (hF : ∀ᵐ x, 0≤F x)
    (hFi : Integrable (fun x => mass (u.coreSlice s x)*(F x)^2))
    (hcap : ∀ᵐ x, ∀ y∈Ω, coreScreenedField S (u.coreSlice s x).normalized y≤F x) :
    Integrable (fun x => mass (u.coreSlice s x)*(∫ y,
      localTFDensity hΩ (coreTFField S (u.coreSlice s x).normalized hΩ hd hn) y)) ∧
    Integrable (fun x => mass (u.coreSlice s x)*rawThomasFermiEnergy
      (coreScreenedField S (u.coreSlice s x).normalized)
      (localTFDensity hΩ (coreTFField S (u.coreSlice s x).normalized hΩ hd hn))) := by
  have H := conditional_localTF_integrable hΩ _ (coreTFField_slice_aestronglyMeasurable S u s hΩ hd hn)
    (fun x => mass (u.coreSlice s x)) F (mass_coreSlice_integrable u s)
    (Eventually.of_forall (fun x => mass_nonneg _)) hF hFi hD hdiam (show ∀ᵐ x,
      ∀ᵐ y ∂volume.restrict Ω, coreTFField S (u.coreSlice s x).normalized hΩ hd hn y≤F x from ?_)
  · refine ⟨H.1,H.2.congr (Eventually.of_forall (fun x => ?_))⟩
    apply congrArg (fun E => mass (u.coreSlice s x)*E)
    exact (rawThomasFermiEnergy_tfDensity hΩ _ _ (coreTFField_coe S _ hΩ hd hn)
      (localTFMinimizer_nonneg hΩ _)).symm
  · filter_upwards [hcap] with x hx
    filter_upwards [ae_restrict_mem hΩ,coreTFField_coe S (u.coreSlice s x).normalized hΩ hd hn] with y hy he
    rw [he]
    exact hx y hy

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFInterior
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ
omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_nonneg_of_nonneg {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (x : Space) :
    0 ≤ tfPotential f x := by
  apply integral_nonneg_of_ae
  filter_upwards [tfExtend_nonneg hΩ hf] with y hy
  exact mul_nonneg (coulombKernel_nonneg _) hy

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

lemma patch_retained_separated {n : ℕ} {a b t : ℝ} (_ : 0<a) (hb : 0<b)
    (y : Space) (x : Configuration n) :
    ∀ z∈{z | t≤‖z-y‖}, ∀ i∈patchRetained y t b x, Real.sqrt 3*b≤‖z-position x i‖ := by
  intro z hz i hi
  have hsmall : Real.sqrt 3≤2 := by exact (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have hret := (patchRetained_mem ..).mp hi
  have H := norm_sub_le_norm_sub_add_norm_sub z (position x i) y
  change t≤‖z-y‖ at hz
  nlinarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_Partial
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

lemma PartlySupported.recorded_positions {m k : ℕ} {u : H1Vector (m+k)} {A : Set Space}
    (hu : PartlySupported u (outIndexSet m k) A) (s : Spins m) :
    ∀ᵐ x, mass (u.coreSlice s x)≠0 → ∀ i : Fin m, position x i∈A := by
  have hall : ∀ᵐ x : Configuration m, ∀ t : Spins k, ∀ᵐ z : Configuration k,
      ∀ i∈outIndexSet m k, position (joinConfiguration m k (x,z)) i∉A →
        u.value (Fin.append s t) (joinConfiguration m k (x,z))=0 :=
    ae_all_iff.mpr (fun t => Measure.ae_ae_of_ae_prod
      ((joinConfiguration_measurePreserving m k).quasiMeasurePreserving.ae (hu (Fin.append s t))))
  filter_upwards [u.coreSliceRegular_ae s,hall] with x hx ha
  intro hm i
  by_contra hi
  apply hm
  unfold mass
  apply Finset.sum_eq_zero
  intro t ht
  apply integral_eq_zero_of_ae
  filter_upwards [ha t] with z hz
  rw [u.coreSlice_value s hx,hz (Fin.castAdd k i) ⟨i,rfl⟩ (by rwa [position_join_left])]
  norm_num

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_LocalizedEnsemble
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

lemma conditionalOutCost_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*(pairPotential x-
      ∑ i : Fin m, coreScreenedField S (ψ.coreSlice s x).normalized (position x i))) := by
  apply ((conditionalEnergy_weight_integrable S ψ s).sub
    (normalized_coreForm_weight_integrable S ψ s)).congr
  exact Eventually.of_forall (fun x => by
    simp only [Pi.sub_apply,conditionalEnergy_eq_screened]
    ring)

lemma form_eq_conditionalOutCost {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k)) :
    form S ψ = sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized)+conditionalOutCost S ψ := by
  rw [conditional_energy_identity]
  change outerKinetic ψ+sliceExpectation ψ (conditionalEnergy S ψ)=_
  have H : sliceExpectation ψ (conditionalEnergy S ψ) =
      sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized)+
      sliceExpectation ψ (fun s x => pairPotential x-
        ∑ i : Fin m, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)) := by
    rw [← sliceExpectation_add ψ _ _ (normalized_coreForm_weight_integrable S ψ)
      (conditionalOutCost_weight_integrable S ψ)]
    congr 1
    funext s x
    rw [conditionalEnergy_eq_screened]
    ring
  rw [H]
  unfold conditionalOutCost
  ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_OutCap
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

lemma localFarCap_le {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) {a : ℝ} (ha : 0 < a)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) :
    localFarCap S u x y a ≤ Real.sqrt (8*(totalCharge S/(2*a))^2) := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply positive_square_ballCloud_integral_le S _
    (recordedFarField_aestronglyMeasurable S u x (isClosed_le continuous_const (by fun_prop)).measurableSet)
    (recordedFarField_le_attraction S u x _) (by positivity) y
  intro j
  nlinarith [hnuc j]

lemma localFarCap_normalized_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) (y : Space) (a : ℝ) :
    AEStronglyMeasurable (fun x => localFarCap S (u.coreSlice s x).normalized x y a) volume := by
  have hf := recordedFarField_normalized_slice_joint S u s
    (isClosed_le continuous_const (by fun_prop) : IsClosed {z : Space | 4*a ≤ ‖z-y‖}).measurableSet
  have H : AEStronglyMeasurable (fun z : Configuration m × Space =>
      (max (recordedFarField S (u.coreSlice s z.1).normalized z.1 {z | 4*a ≤ ‖z-y‖} z.2) 0)^2*
        ballCloud y (2*a) 1 z.2) (volume.prod volume) :=
    ((hf.sup aestronglyMeasurable_const).pow 2).mul
      ((ballCloud_measurable (2*a) 1 y).comp measurable_snd).aestronglyMeasurable
  exact Real.continuous_sqrt.comp_aestronglyMeasurable (H.integral_prod_right'.const_mul 8)

lemma localFarCap_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) {a : ℝ} (ha : 0 < a) (y : Space)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) (q : ℕ) :
    Integrable (fun x => mass (u.coreSlice s x)*(localFarCap S (u.coreSlice s x).normalized x y a)^q) := by
  apply (mass_coreSlice_integrable u s).mul_bdd ((localFarCap_normalized_slice_aestronglyMeasurable S u s y a).pow q)
  filter_upwards [] with x
  change ‖(localFarCap S (u.coreSlice s x).normalized x y a)^q‖ ≤ (Real.sqrt (8*(totalCharge S/(2*a))^2))^q
  rw [Real.norm_of_nonneg (pow_nonneg (localFarCap_nonneg _ _ _ _ _) q)]
  exact pow_le_pow_left₀ (localFarCap_nonneg _ _ _ _ _) (localFarCap_le S _ x y ha hnuc) q

theorem sliceExpectation_localFarCap_sq {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {a : ℝ} (ha : 0 < a) (y : Space)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) :
    sliceExpectation u (fun s x => (localFarCap S (u.coreSlice s x).normalized x y a)^2) =
      8*(∫ v, (sliceExpectation u (fun s x =>
        (max (recordedFarField S (u.coreSlice s x).normalized x {z | 4*a ≤ ‖z-y‖} v) 0)^2))*
          ballCloud y (2*a) 1 v) := by
  simp only [localFarCap_sq S _ _ y ha]
  rw [sliceExpectation_const_mul,sliceExpectation_farSquare_ballCloud S u
    (isClosed_le continuous_const (by fun_prop)).measurableSet (by positivity) y (fun j => by nlinarith [hnuc j])]

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

lemma sliceCount_cap_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {A : Set Space} (hA : MeasurableSet A)
    (s : Spins m) {a : ℝ} (ha : 0<a) (y : Space) (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) :
    Integrable (fun x => mass (u.coreSlice s x)*localCount A x*localFarCap S (u.coreSlice s x).normalized x y a) := by
  have hc : Integrable (fun x => mass (u.coreSlice s x)*localFarCap S (u.coreSlice s x).normalized x y a) := by
    simpa only [pow_one] using localFarCap_weight_integrable S u s ha y hnuc 1
  apply (hc.mul_const (m:ℝ)).mono'
    (((mass_coreSlice_integrable u s).aestronglyMeasurable.mul (localCount_measurable hA).aestronglyMeasurable).mul
      (localFarCap_normalized_slice_aestronglyMeasurable S u s y a))
  filter_upwards [] with x
  dsimp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mass_nonneg _) (localCount_nonneg _ _)) (localFarCap_nonneg _ _ _ _ _))]
  calc
    _ = mass (u.coreSlice s x)*localFarCap S (u.coreSlice s x).normalized x y a*localCount A x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (localCount_le _ _) (mul_nonneg (mass_nonneg _) (localFarCap_nonneg _ _ _ _ _))

lemma coreScreenedField_sum_le_cover {C : Type*} [Fintype C] {J m k : ℕ}
    (S : Nuclei J) (u : H1Vector k) (x : Configuration m)
    (y : C → Space) (a : C → ℝ) (ha : ∀ c, 0<a c)
    (hnuc : ∀ c j, 4*a c ≤ ‖S.position j-y c‖)
    (hcover : ∀ i, ∃ c, ‖position x i-y c‖ ≤ a c) :
    (∑ i : Fin m, coreScreenedField S u (position x i)) ≤
      ∑ c, localCount (Metric.closedBall (y c) (a c)) x*
        (localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c)) := by
  have H (i : Fin m) : coreScreenedField S u (position x i) ≤
      ∑ c, if position x i ∈ Metric.closedBall (y c) (a c) then
        localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c) else 0 := by
    obtain ⟨c,hc⟩ := hcover i
    have hm : position x i ∈ Metric.closedBall (y c) (a c) := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hc
    calc
      _ ≤ localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c) :=
        coreField_le_local_far_cap S u x (ha c) (y c) (position x i) hc (hnuc c)
      _ = (if position x i ∈ Metric.closedBall (y c) (a c) then
          localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c) else 0) := (ite_eq_left hm).symm
      _ ≤ _ := Finset.single_le_sum (f := fun d : C => if position x i ∈ Metric.closedBall (y d) (a d) then
          localFarCap S u x (y d) (a d)+(m:ℝ)/(3*a d) else 0) (fun d _ => by
        split_ifs
        · exact add_nonneg (localFarCap_nonneg _ _ _ _ _) (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (ha d).le))
        · exact le_refl _) (Finset.mem_univ c)
  calc
    _ ≤ ∑ i : Fin m, ∑ c, if position x i ∈ Metric.closedBall (y c) (a c) then
        localFarCap S u x (y c) (a c)+(m:ℝ)/(3*a c) else 0 := Finset.sum_le_sum (fun i _ => H i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      simp only [localCount,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : position x i ∈ Metric.closedBall (y c) (a c) <;> simp only [Set.indicator,h,ite_true,ite_false,one_mul,zero_mul]

theorem conditionalOutCost_lower_cover {C : Type*} [Fintype C] {J m k : ℕ}
    (S : Nuclei J) (u : H1Vector (m+k))
    (y : C → Space) (a : C → ℝ) (ha : ∀ c, 0<a c)
    (hnuc : ∀ c j, 4*a c ≤ ‖S.position j-y c‖)
    (hsupp : ∀ s, ∀ᵐ x, mass (u.coreSlice s x) ≠0 → ∀ i, ∃ c, ‖position x i-y c‖ ≤ a c) :
    -(∑ c, sliceExpectation u (fun s x => localCount (Metric.closedBall (y c) (a c)) x*
      (localFarCap S (u.coreSlice s x).normalized x (y c) (a c)+(m:ℝ)/(3*a c)))) ≤ conditionalOutCost S u := by
  let F := fun c (s : Spins m) (x : Configuration m) => localCount (Metric.closedBall (y c) (a c)) x*
      (localFarCap S (u.coreSlice s x).normalized x (y c) (a c)+(m:ℝ)/(3*a c))
  have hi (c : C) (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*F c s x) := by
    have hc := sliceCount_cap_weight_integrable S u (show MeasurableSet (Metric.closedBall (y c) (a c)) from measurableSet_closedBall) s (ha c) (y c) (hnuc c)
    have hn : Integrable (fun x => mass (u.coreSlice s x)*localCount (Metric.closedBall (y c) (a c)) x) := by
      simpa only [pow_one] using sliceCount_weight_integrable u (show MeasurableSet (Metric.closedBall (y c) (a c)) from measurableSet_closedBall) s 1
    exact (hc.add (hn.mul_const ((m:ℝ)/(3*a c)))).congr (Eventually.of_forall (fun x => by dsimp [F]; ring))
  have H (s : Spins m) :
      -(∑ c, ∫ x, mass (u.coreSlice s x)*F c s x) ≤
      ∫ x, mass (u.coreSlice s x)*(pairPotential x-∑ i : Fin m, coreScreenedField S (u.coreSlice s x).normalized (position x i)) := by
    rw [←integral_finsetSum _ (fun c _ => hi c s),←integral_neg]
    apply integral_mono_ae ((integrable_finsetSum _ (fun c _ => hi c s)).neg)
      (conditionalOutCost_weight_integrable S u s)
    filter_upwards [hsupp s] with x hx
    by_cases hm : mass (u.coreSlice s x)=0
    · simp [hm]
    · have h := coreScreenedField_sum_le_cover S (u.coreSlice s x).normalized x y a ha hnuc (hx hm)
      have hp := pairPotential_nonneg_pointwise x
      have h' := mul_le_mul_of_nonneg_left (show -(∑ c, F c s x) ≤ pairPotential x-∑ i : Fin m, coreScreenedField S (u.coreSlice s x).normalized (position x i) by dsimp [F]; linarith) (mass_nonneg (u.coreSlice s x))
      simpa only [Finset.mul_sum,mul_neg,Pi.neg_apply] using h'
  have H' := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => H s)
  rw [Finset.sum_neg_distrib,Finset.sum_comm] at H'
  change -(∑ c, sliceExpectation u (F c)) ≤ sliceExpectation u _ at H'
  exact H'.trans (le_add_of_nonneg_left (outerKinetic_nonneg u))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RecordedCount
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

lemma localCount_join {m k : ℕ} (A : Set Space) (x : Configuration m) (v : Configuration k) :
    localCount A (joinConfiguration m k (x,v))=localCount A x+localCount A v := by
  simp only [localCount,Fin.sum_univ_add,position_join_left,position_join_right]

lemma sliceExpectation_localCount_sq_le {m k : ℕ} (u : H1Vector (m+k))
    {A : Set Space} (hA : MeasurableSet A) :
    sliceExpectation u (fun _ x => (localCount A x)^2) ≤ localCountSecondMoment u A := by
  let W : Configuration (m+k) → ℝ := fun v => (localCount A v)^2
  have hW : Measurable W := (localCount_measurable hA).pow_const 2
  have hB : ∀ v, |W v| ≤ ((m+k:ℕ):ℝ)^2 := by
    intro v
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (localCount_nonneg _ _) (localCount_le _ _) 2
  have hp : sliceExpectation u (fun _ x => (localCount A x)^2) ≤ sliceExpectation u (coreConditionalObservable u W) := by
    apply Finset.sum_le_sum
    intro s hs
    apply integral_mono (sliceCount_weight_integrable u hA s 2)
      (coreConditionalObservable_weight_integrable u W hW (sq_nonneg _) hB s)
    intro x
    by_cases hm : mass (u.coreSlice s x)=0
    · simp only [hm,zero_mul,le_refl]
    · apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
      have hm' := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hm)
      let w := (u.coreSlice s x).normalized
      calc
        (localCount A x)^2 = potentialForm (fun _ : Configuration k => (localCount A x)^2) w := by
          rw [potentialForm_const,mass_normalized _ hm',mul_one]
        _ ≤ potentialForm (fun v => W (joinConfiguration m k (x,v))) w := by
          apply potentialForm_mono_bounded w _ _ measurable_const
            (hW.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
            (fun _ => le_rfl) (fun v => hB _)
          intro v
          dsimp [W]
          rw [localCount_join]
          exact pow_le_pow_left₀ (localCount_nonneg _ _) (le_add_of_nonneg_right (localCount_nonneg _ _)) 2
        _ = _ := rfl
  rw [sliceExpectation_coreConditionalObservable u W hW hB] at hp
  exact hp

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma raw_posterior_positive_le_core {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {a : ℝ} (ha : 0<a) (y : Space)
    (s : Spins m) (x : Configuration m)
    (hs : SpatiallySupported (u.coreSlice s x).normalized {z | 40*a ≤ ‖z-y‖}) :
    mass (u.coreSlice s x)*(max (coreConditionalObservable u
      (rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y) s x) 0)^2 ≤
    mass (u.coreSlice s x)*(max (coreScreenedField S (u.coreSlice s x).normalized y) 0)^2 := by
  rw [coreConditionalObservable_raw_positive_weight u _
    (isClosed_le continuous_const (by fun_prop) : IsClosed {z : Space | 40*a ≤ ‖z-y‖}).measurableSet y (by positivity : 0<40*a) (fun _ h => h),
    restrictedCorePotential_eq _ hs]
  apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
  apply pow_le_pow_left₀ (le_max_right _ _) _ 2
  apply max_le_max _ le_rfl
  unfold coreScreenedField
  linarith [restrictedOutPotential_nonneg x {z | 40*a ≤ ‖z-y‖} y]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_RadialAppend
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

theorem radial_append_raw_gain {J m n : ℕ} (S : Nuclei J)
    (u : H1Vector (m+n)) (hu : PartlyAntisymmetric u (coreIndexSet m n))
    (A : Set Space) (hA : PartlySupported u (outIndexSet m n) A)
    {a E : ℝ} (ha : 0<a) (y : Space) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖)
    (hE : (E:EReal) ≤ unrestrictedFormBottom S) :
    ∃ (q k : (Fin (m+n) → Fin 2) → ℕ)
      (e : (p : Fin (m+n) → Fin 2) → Fin (q p+k p) ≃ Fin n),
      let χ := radialCut y (40*a)
      let D := radialCutCoefficient/(40*a)
      let v := fun p => u.appendCut χ (radialCut_smooth y (40*a))
        (radialCut_partition y (40*a)) D
        (div_nonneg radialCutCoefficient_pos.le (by positivity))
        (radialCut_derivative_bound y (by positivity)) p (e p)
      (∑ p, mass (v p))=mass u ∧
      (∀ p, PartlyAntisymmetric (v p) (coreIndexSet (m+q p) (k p))) ∧
      (∀ p, PartlySupported (v p) (coreIndexSet (m+q p) (k p)) {z | 40*a ≤ ‖z-y‖}) ∧
      (∀ p, PartlySupported (v p) (outIndexSet (m+q p) (k p)) (A∪Metric.closedBall y (80*a))) ∧
      (∀ W : Configuration (m+n) → ℝ, Measurable W → (∃ B : ℝ, ∀ x, |W x| ≤ B) →
        (∑ p, potentialForm (W ∘ reindexConfiguration (coreReindex m (e p)) ∘
          reindexConfiguration (recordAssoc m (q p) (k p))) (v p))=potentialForm W u) ∧
      a/(16*ballTrialCoefficient)*sliceExpectation u (fun s x =>
        (max (coreConditionalObservable u
          (rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y) s x) 0)^2) ≤
        form S u+3*D^2*expectedPopulation u (Metric.closedBall y (80*a))-
          (∑ p, conditionalOutCost S (v p))-E*mass u+
          (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*mass u := by
  have hr : 0<40*a := by positivity
  let χ := radialCut y (40*a)
  let D := radialCutCoefficient/(40*a)
  have hD : 0≤D := div_nonneg radialCutCoefficient_pos.le hr.le
  have hc : ∀ z∉{z : Space | 40*a ≤ ‖z-y‖}, χ 1 z=0 := by
    intro z hz
    exact radialCut_core_zero y hr z (le_of_lt (by simpa only [Set.mem_ofPred_eq,not_le] using hz))
  have ho : ∀ z∉Metric.closedBall y (80*a), χ 0 z=0 := by
    intro z hz
    apply radialCut_out_zero y hr
    have h : 80*a < ‖z-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hz
    linarith
  have H (p : Fin (m+n) → Fin 2) := binary_append_cut_outcome u hu hA χ
    (radialCut_smooth y (40*a)) (radialCut_partition y (40*a)) D hD
    (radialCut_derivative_bound y hr) p _ _ ho hc
  choose q k e hanti hcore hout using H
  let v := fun p : Fin (m+n) → Fin 2 => u.appendCut χ (radialCut_smooth y (40*a))
    (radialCut_partition y (40*a)) D hD (radialCut_derivative_bound y hr) p (e p)
  have hm : (∑ p, mass (v p))=mass u := by
    simp only [v,mass_appendCut]
    exact mass_labelCut u χ _ _ _ _ _
  have hs (p) (s : Spins (m+q p)) : ∀ᵐ x,
      SpatiallySupported ((v p).coreSlice s x).normalized {z | 40*a ≤ ‖z-y‖} := by
    filter_upwards [(hcore p).coreSlice s] with x hx
    exact hx.normalized
  have hconserve (W : Configuration (m+n) → ℝ) (hW : Measurable W)
      (hB : ∃ B : ℝ, ∀ x, |W x| ≤ B) :
      (∑ p, potentialForm (W ∘ reindexConfiguration (coreReindex m (e p)) ∘
        reindexConfiguration (recordAssoc m (q p) (k p))) (v p))=potentialForm W u := by
    simp only [v,potentialForm_appendCut]
    obtain ⟨B,hB⟩ := hB
    exact potentialForm_labelCut u χ _ _ _ _ _ W hW hB
  have hclosed : IsClosed {z : Space | 40*a ≤ ‖z-y‖} := isClosed_le continuous_const (by fun_prop)
  have hg (p : Fin (m+n) → Fin 2) :
      a/(16*ballTrialCoefficient)*sliceExpectation (v p) (fun s x =>
        (max (coreScreenedField S ((v p).coreSlice s x).normalized y) 0)^2) ≤
      form S (v p)-conditionalOutCost S (v p)-E*mass (v p)+
        (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*mass (v p) := by
    have HG := conditional_positive_field_gain S (v p) ((hanti p).coreSlice) ha y _ hclosed
      (hs p) (fun z hz => by change 40*a ≤ ‖z-y‖ at hz; linarith) hnuc hE
    rw [form_eq_conditionalOutCost S (v p)]
    linarith
  have HI : (∑ p, form S (v p)) ≤ form S u+3*D^2*expectedPopulation u (Metric.closedBall y (80*a)) := by
    simp only [v,form_appendCut]
    have HI := form_radial_labelCut S u y hr
    have heq : 2*(40*a)=80*a := by ring
    rw [heq] at HI
    exact HI
  have HG := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hg p)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,hm] at HG
  have hraw (p) : sliceExpectation (v p) (fun s x =>
      (max (coreConditionalObservable (v p) (rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y) s x) 0)^2) ≤
      sliceExpectation (v p) (fun s x => (max (coreScreenedField S ((v p).coreSlice s x).normalized y) 0)^2) := by
    apply Finset.sum_le_sum
    intro s hs0
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))
    · exact coreField_positive_square_weight_integrable S (v p) s y
    · filter_upwards [hs p s] with x hx
      exact raw_posterior_positive_le_core S (v p) ha y s x hx
  let W : Configuration (m+n) → ℝ := rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y
  have hW : Measurable W := rawSignedField_measurable _ hclosed.measurableSet y
  let B := |attraction S y|+((m+n:ℕ):ℝ)/(40*a)
  have hB0 : 0≤B := by dsimp [B]; positivity
  have hB : ∀ x, |W x| ≤ B := rawSignedField_abs_le _ _ y hr (fun _ h => h)
  have HJ := appendCut_positive_jensen u χ (radialCut_smooth y (40*a)) (radialCut_partition y (40*a)) D hD (radialCut_derivative_bound y hr) q k e W hW hB0 hB
  have heq (p) : W ∘ reindexConfiguration (coreReindex m (e p)) ∘ reindexConfiguration (recordAssoc m (q p) (k p))=
      rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y := by
    funext x
    simp only [W,Function.comp_apply,rawSignedField_reindex]
  simp only [heq] at HJ
  have HJL := HJ.trans (Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hraw p))
  have hcoef : 0≤a/(16*ballTrialCoefficient) := div_nonneg ha.le (mul_nonneg (by norm_num) ballTrialCoefficient_pos.le)
  have HK := mul_le_mul_of_nonneg_left HJL hcoef
  refine ⟨q,k,e,hm,hanti,hcore,hout,hconserve,?_⟩
  change a/(16*ballTrialCoefficient)*sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) ≤ _
  linarith

end Coulomb
end

end
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

lemma Conserves.recorded_secondMoment {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) :
    (∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount A x)^2))≤
      localCountSecondMoment ψ A := by
  rw [←hT.secondMoment hA]
  exact Finset.sum_le_sum (fun p _ => sliceExpectation_localCount_sq_le (T.vector p) hA)

theorem append_radial (S : Nuclei J) (ψ : H1Vector n) (T : RecordedEnsemble n)
    (hT : T.Conserves ψ) (hanti : T.CoreFermionic) (A : Set Space) (hsupp : T.OutSupported A)
    {a E : ℝ} (ha : 0<a) (y : Space) (hnuc : ∀ j, 3*a≤‖S.position j-y‖)
    (hE : (E:EReal)≤unrestrictedFormBottom S) :
    ∃ U : RecordedEnsemble n,
      U.Conserves ψ ∧ U.CoreFermionic ∧ U.OutSupported (A∪Metric.closedBall y (80*a)) ∧
      U.totalMass=T.totalMass ∧
      U.totalForm S≤T.totalForm S+3*(radialCutCoefficient/(40*a))^2*expectedPopulation ψ (Metric.closedBall y (80*a)) ∧
      a/(16*ballTrialCoefficient)*T.rawSquare S y a ≤
        T.totalForm S+3*(radialCutCoefficient/(40*a))^2*expectedPopulation ψ (Metric.closedBall y (80*a))-
          (∑ p, conditionalOutCost S (U.vector p))-E*T.totalMass+
            (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*T.totalMass := by
  have H (p : T.index) := radial_append_raw_gain S (T.vector p) (hanti p) A (hsupp p) ha y hnuc hE
  choose q k e hm hanti' hcore hout hcons hgain using H
  let χ := radialCut y (40*a)
  let D := radialCutCoefficient/(40*a)
  have hr : 0<40*a := by positivity
  have hD : 0≤D := div_nonneg radialCutCoefficient_pos.le hr.le
  let v (p : T.index) (l : Fin (T.out p+T.core p) → Fin 2) :=
    (T.vector p).appendCut χ (radialCut_smooth y (40*a)) (radialCut_partition y (40*a))
      D hD (radialCut_derivative_bound y hr) l (e p l)
  let U : RecordedEnsemble n := {
    index := (p : T.index) × (Fin (T.out p+T.core p) → Fin 2)
    finite := inferInstance
    out := fun pl => T.out pl.1+q pl.1 pl.2
    core := fun pl => k pl.1 pl.2
    vector := fun pl => v pl.1 pl.2
    labels := fun pl => (recordAssoc _ _ _).trans ((coreReindex _ (e pl.1 pl.2)).trans (T.labels pl.1)) }
  have hmass : U.totalMass=T.totalMass := by
    dsimp [totalMass,U]
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun p _ => hm p)
  have HC : U.Conserves ψ := by
    intro W hW hB
    change (∑ pl : (p : T.index) × (Fin (T.out p+T.core p) → Fin 2),
      potentialForm (W ∘ reindexConfiguration ((recordAssoc _ _ _).trans
        ((coreReindex _ (e pl.1 pl.2)).trans (T.labels pl.1)))) (v pl.1 pl.2))=_
    rw [Fintype.sum_sigma]
    simp only [reindexConfiguration_trans,←Function.comp_assoc]
    rw [show (∑ p, ∑ l, potentialForm (((W ∘ reindexConfiguration (T.labels p)) ∘
      reindexConfiguration (coreReindex _ (e p l))) ∘ reindexConfiguration (recordAssoc _ _ _)) (v p l))=
        ∑ p, potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p) from ?_]
    · exact hT W hW hB
    · apply Finset.sum_congr rfl
      intro p hp
      exact hcons p _ (hW.comp (reindexConfiguration_continuous _).measurable)
        (hB.imp (fun B hb x => hb _))
  have HI : U.totalForm S≤T.totalForm S+3*D^2*expectedPopulation ψ (Metric.closedBall y (80*a)) := by
    dsimp [totalForm,U]
    rw [Fintype.sum_sigma]
    have HH := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) =>
      form_radial_labelCut S (T.vector p) y hr)
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,show 2*(40*a)=80*a by ring] at HH
    rw [hT.population measurableSet_closedBall] at HH
    simpa only [v,form_appendCut] using HH
  have HG := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hgain p)
  change (∑ p, a/(16*ballTrialCoefficient)*_)≤_ at HG
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at HG
  rw [hT.population measurableSet_closedBall] at HG
  refine ⟨U,HC,(fun pl => hanti' pl.1 pl.2),(fun pl => hout pl.1 pl.2),hmass,HI,?_⟩
  change _≤T.totalForm S+3*D^2*expectedPopulation ψ (Metric.closedBall y (80*a))-
    (∑ pl : (p : T.index) × (Fin (T.out p+T.core p) → Fin 2), conditionalOutCost S (v pl.1 pl.2))-
      E*T.totalMass+_
  rw [Fintype.sum_sigma]
  exact HG

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

lemma out_square_le {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) (hsupp : T.OutSupported A) :
    (∑ p, (T.out p:ℝ)^2*mass (T.vector p))≤localCountSecondMoment ψ A := by
  calc
    _ = ∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount A x)^2) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [←sliceExpectation_number]
      apply Finset.sum_congr rfl
      intro s hs
      apply integral_congr_ae
      filter_upwards [(hsupp p).recorded_positions s] with x hx
      by_cases hm : mass ((T.vector p).coreSlice s x)=0
      · simp only [hm,zero_mul]
      · have he : localCount A x=(T.out p:ℝ) := by simp only [localCount,indicator_of_mem (hx hm _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
        rw [he]
    _ ≤ _ := hT.recorded_secondMoment hA

lemma out_square_cover {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {C : Type*} [Fintype C] (A : C → Set Space)
    (hA : ∀ c, MeasurableSet (A c))
    (hcover : ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 → ∀ i, ∃ c, position x i∈A c) :
    (∑ p, (T.out p:ℝ)^2*mass (T.vector p))≤
      (Fintype.card C:ℝ)*(∑ c, localCountSecondMoment ψ (A c)) := by
  have H (p : T.index) : (T.out p:ℝ)^2*mass (T.vector p)≤
      (Fintype.card C:ℝ)*∑ c, sliceExpectation (T.vector p) (fun _ x => (localCount (A c) x)^2) := by
    rw [←sliceExpectation_number]
    change (∑ s, ∫ x, mass ((T.vector p).coreSlice s x)*(T.out p:ℝ)^2)≤_
    simp only [sliceExpectation]
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    rw [←integral_finsetSum _ (fun c _ => sliceCount_weight_integrable (T.vector p) (hA c) s 2),←integral_const_mul]
    apply integral_mono_ae
    · exact (mass_coreSlice_integrable (T.vector p) s).mul_const _
    · exact (integrable_finsetSum _ (fun c _ => sliceCount_weight_integrable (T.vector p) (hA c) s 2)).const_mul _
    · filter_upwards [hcover p s] with x hx
      by_cases hm : mass ((T.vector p).coreSlice s x)=0
      · simp only [hm,zero_mul,Finset.sum_const_zero,mul_zero,le_refl]
      · have H := count_cover_le A x (hx hm)
        have HS := sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun c => localCount (A c) x)
        simp only [Finset.card_univ] at HS
        have HG := (pow_le_pow_left₀ (Nat.cast_nonneg _) H 2).trans HS
        have HM := mul_le_mul_of_nonneg_left HG (mass_nonneg ((T.vector p).coreSlice s x))
        simpa only [Finset.mul_sum,mul_left_comm] using HM
  have HH := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => H p)
  rw [←Finset.mul_sum,Finset.sum_comm] at HH
  refine HH.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => ?_)) (Nat.cast_nonneg _))
  exact hT.recorded_secondMoment (hA c)

end RecordedEnsemble
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_AtomicCapRaw
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

lemma farSquare_to_atomic_raw {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {z v : Space} (hz : z≠0) (hv : ‖v-z‖ ≤ 2*atomicCellScale z) :
    sliceExpectation u (fun s x =>
      (max (recordedFarField S (u.coreSlice s x).normalized x {w | 4*atomicCellScale z ≤ ‖w-z‖} v) 0)^2) ≤
    sliceExpectation u (fun s x =>
      (max (coreConditionalObservable u
        (rawSignedField (attraction S v) {w | 40*atomicCellScale v ≤ ‖w-v‖} v) s x) 0)^2) := by
  have hv0 : v≠0 := atomicCellScale_near_nonzero hz (by nlinarith [atomicCellScale_nonneg z])
  have hvpos := atomicCellScale_pos hv0
  have hp : 0<40*atomicCellScale v := by positivity
  have hA : MeasurableSet {w : Space | 40*atomicCellScale v ≤ ‖w-v‖} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hB : MeasurableSet {w : Space | 4*atomicCellScale z ≤ ‖w-z‖} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hb := rawSignedField_abs_le (n:=m+k) (attraction S v) _ v hp (fun _ h => h)
  have hB0 : 0 ≤ |attraction S v|+((m+k:ℕ):ℝ)/(40*atomicCellScale v) := by positivity
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))
  · exact coreConditionalObservable_positive_weight_integrable u _
      (rawSignedField_measurable _ hA v) hB0 hb s 2
  · filter_upwards [] with x
    by_cases hm : mass (u.coreSlice s x)=0
    · simp only [hm,zero_mul,le_refl]
    · have hm' := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hm)
      rw [coreConditionalObservable_rawSignedField u _ hA v hp (fun _ h => h) s x hm']
      apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
      apply pow_le_pow_left₀ (le_max_right _ _) _ 2
      apply max_le_max _ le_rfl
      exact recordedFarField_anti S (u.coreSlice s x).normalized x hA hB (atomic_raw_exclusion_subset hv) v

lemma sliceFarSquare_ballCloud_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {A : Set Space} (hA : MeasurableSet A)
    {a : ℝ} (ha : 0<a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    Integrable (fun v => (sliceExpectation u (fun s x =>
      (max (recordedFarField S (u.coreSlice s x).normalized x A v) 0)^2))*ballCloud y a 1 v) := by
  unfold sliceExpectation
  simp only [Finset.sum_mul,←integral_mul_const]
  exact integrable_finsetSum _ (fun s _ =>
    (farSquare_mass_ballCloud_integrable S u s hA ha y hnuc).integral_prod_right)

theorem atomic_cap_sq_le_of_raw_bound {P : Type*} [Fintype P] {J : ℕ}
    (S : Nuclei J) (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    {z : Space} (hz : z≠0) (hnuc : ∀ j, 4*atomicCellScale z ≤ ‖S.position j-z‖)
    {H : ℝ} (hraw : ∀ v : Space, ‖v-z‖ ≤ 2*atomicCellScale z →
      (∑ p, sliceExpectation (u p) (fun s x =>
        (max (coreConditionalObservable (u p)
          (rawSignedField (attraction S v) {w | 40*atomicCellScale v ≤ ‖w-v‖} v) s x) 0)^2)) ≤ H) :
    (∑ p, sliceExpectation (u p) (fun s x =>
      (localFarCap S ((u p).coreSlice s x).normalized x z (atomicCellScale z))^2)) ≤ 8*H := by
  have ha := atomicCellScale_pos hz
  let A := {w : Space | 4*atomicCellScale z ≤ ‖w-z‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const (by fun_prop)).measurableSet
  let F := fun p v => sliceExpectation (u p) (fun s x =>
    (max (recordedFarField S ((u p).coreSlice s x).normalized x A v) 0)^2)
  have hi (p) : Integrable (fun v => F p v*ballCloud z (2*atomicCellScale z) 1 v) :=
    sliceFarSquare_ballCloud_integrable S (u p) hA (by positivity) z (fun j => by nlinarith [hnuc j])
  have hb : Integrable (fun v => H*ballCloud z (2*atomicCellScale z) 1 v) := (ballCloud_integrable _ _ _).const_mul H
  have hsum : (∫ v, ∑ p, F p v*ballCloud z (2*atomicCellScale z) 1 v) ≤ H := by
    calc
      _ ≤ ∫ v, H*ballCloud z (2*atomicCellScale z) 1 v := by
        apply integral_mono (integrable_finsetSum _ (fun p _ => hi p)) hb
        intro v
        change (∑ p, F p v*ballCloud z (2*atomicCellScale z) 1 v) ≤ H*ballCloud z (2*atomicCellScale z) 1 v
        rw [←Finset.sum_mul]
        by_cases hv : v-z ∈ Metric.ball (0:Space) (2*atomicCellScale z)
        · have hdist : ‖v-z‖ ≤ 2*atomicCellScale z := by
            exact (by simpa only [Metric.mem_ball,dist_zero_right] using hv : ‖v-z‖ < 2*atomicCellScale z).le
          apply mul_le_mul_of_nonneg_right _ (uniformBall_nonneg (by positivity) zero_le_one (v-z))
          exact (Finset.sum_le_sum (fun p _ => farSquare_to_atomic_raw S (u p) hz hdist)).trans (hraw v hdist)
        · simp only [ballCloud,uniformBall,indicator_of_notMem hv,mul_zero,le_refl]
      _ = H := by rw [integral_const_mul,ballCloud_mass (by positivity) 1 z,mul_one]
  calc
    _ = ∑ p, 8*(∫ v, F p v*ballCloud z (2*atomicCellScale z) 1 v) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sliceExpectation_localFarCap_sq S (u p) ha z hnuc
    _ = 8*(∫ v, ∑ p, F p v*ballCloud z (2*atomicCellScale z) 1 v) := by
      rw [←Finset.mul_sum,integral_finsetSum _ (fun p _ => hi p)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

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

lemma sliceExpectation_count_cap_addback {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {a : ℝ} (ha : 0<a) (y : Space)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) :
    sliceExpectation u (fun s x => localCount (Metric.closedBall y a) x*
      (localFarCap S (u.coreSlice s x).normalized x y a+(m:ℝ)/(3*a))) ≤
    sliceExpectation u (fun s x => localCount (Metric.closedBall y a) x*
      localFarCap S (u.coreSlice s x).normalized x y a)+(m:ℝ)^2/(3*a)*mass u := by
  have hc (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*
      (localCount (Metric.closedBall y a) x*localFarCap S (u.coreSlice s x).normalized x y a)) := by
    simpa only [mul_assoc] using sliceCount_cap_weight_integrable S u measurableSet_closedBall s ha y hnuc
  have hn (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*
      ((m:ℝ)/(3*a)*localCount (Metric.closedBall y a) x)) := by
    have h : Integrable (fun x => mass (u.coreSlice s x)*localCount (Metric.closedBall y a) x) := by
      simpa only [pow_one] using sliceCount_weight_integrable u measurableSet_closedBall s 1
    simpa only [mul_left_comm (mass _) ((m:ℝ)/(3*a))] using h.const_mul ((m:ℝ)/(3*a))
  have he : sliceExpectation u (fun s x => localCount (Metric.closedBall y a) x*
      (localFarCap S (u.coreSlice s x).normalized x y a+(m:ℝ)/(3*a))) =
      sliceExpectation u (fun s x => localCount (Metric.closedBall y a) x*
        localFarCap S (u.coreSlice s x).normalized x y a)+
      (m:ℝ)/(3*a)*sliceExpectation u (fun _ x => localCount (Metric.closedBall y a) x) := by
    rw [←sliceExpectation_const_mul,←sliceExpectation_add u _ _ hc hn]
    congr 1
    funext s x
    ring
  rw [he]
  have H := mul_le_mul_of_nonneg_left (sliceExpectation_localCount_le u (A:=Metric.closedBall y a) measurableSet_closedBall)
    (show 0 ≤ (m:ℝ)/(3*a) by positivity)
  have heq : (m:ℝ)/(3*a)*((m:ℝ)*mass u)=(m:ℝ)^2/(3*a)*mass u := by ring
  rw [heq] at H
  exact add_le_add le_rfl H

theorem conditionalOutCost_ensemble_cover_lower {P C : Type*} [Fintype P] [Fintype C] {J : ℕ}
    (S : Nuclei J) (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (y : C → Space) (a : C → ℝ) (ha : ∀ c, 0<a c)
    (hnuc : ∀ c j, 4*a c ≤ ‖S.position j-y c‖)
    (hsupp : ∀ p s, ∀ᵐ x, mass ((u p).coreSlice s x) ≠0 → ∀ i, ∃ c, ‖position x i-y c‖ ≤ a c) :
    -(∑ c, (Real.sqrt ((∑ p, sliceExpectation (u p) (fun _ x => (localCount (Metric.closedBall (y c) (a c)) x)^2))*
      (∑ p, sliceExpectation (u p) (fun s x => (localFarCap S ((u p).coreSlice s x).normalized x (y c) (a c))^2)))+
      (∑ p, (m p:ℝ)^2*mass (u p))/(3*a c))) ≤ ∑ p, conditionalOutCost S (u p) := by
  let F := fun c p (s : Spins (m p)) (x : Configuration (m p)) =>
    localCount (Metric.closedBall (y c) (a c)) x*(localFarCap S ((u p).coreSlice s x).normalized x (y c) (a c)+(m p:ℝ)/(3*a c))
  have hlow := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => conditionalOutCost_lower_cover S (u p) y a ha hnuc (hsupp p))
  change (∑ p, -(∑ c, sliceExpectation (u p) (F c p))) ≤ _ at hlow
  rw [Finset.sum_neg_distrib,Finset.sum_comm] at hlow
  refine (neg_le_neg (Finset.sum_le_sum (fun c (_ : c∈Finset.univ) => ?_))).trans hlow
  have hcs := slice_ensemble_mul_le_sqrt m k u
    (fun _ _ x => localCount (Metric.closedBall (y c) (a c)) x)
    (fun p s x => localFarCap S ((u p).coreSlice s x).normalized x (y c) (a c))
    (fun p s => sliceCount_weight_integrable (u p) measurableSet_closedBall s 2)
    (fun p s => localFarCap_weight_integrable S (u p) s (ha c) (y c) (hnuc c) 2)
    (fun p s => by simpa only [mul_assoc] using sliceCount_cap_weight_integrable S (u p) measurableSet_closedBall s (ha c) (y c) (hnuc c))
  have hsum := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => sliceExpectation_count_cap_addback S (u p) (ha c) (y c) (hnuc c))
  rw [Finset.sum_add_distrib] at hsum
  have he : (∑ p, (m p:ℝ)^2/(3*a c)*mass (u p))=(∑ p, (m p:ℝ)^2*mass (u p))/(3*a c) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he] at hsum
  exact hsum.trans (add_le_add hcs le_rfl)

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb
namespace RecordedEnsemble

theorem atomic_cost_lower {n J : ℕ} {C : Type*} [Fintype C]
    (S : Nuclei J) (hatom : ∀ j, S.position j=0) (ψ : H1Vector n)
    (T : RecordedEnsemble n) (hT : T.Conserves ψ) (z : C → Space) (hz : ∀ c, z c≠0)
    (hcover : ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      ∀ i, ∃ c, ‖position x i-z c‖≤atomicCellScale (z c))
    {H : ℝ}
    (hraw : ∀ c v, ‖v-z c‖≤2*atomicCellScale (z c) → T.rawSquare S v (atomicCellScale v)≤H) :
    -(∑ c, (Real.sqrt (localCountSecondMoment ψ (Metric.closedBall (z c) (atomicCellScale (z c)))*(8*H))+
      ((Fintype.card C:ℝ)*(∑ d, localCountSecondMoment ψ (Metric.closedBall (z d) (atomicCellScale (z d)))))/
        (3*atomicCellScale (z c)))) ≤ ∑ p, conditionalOutCost S (T.vector p) := by
  let a := fun c => atomicCellScale (z c)
  have ha (c) : 0<a c := atomicCellScale_pos (hz c)
  have hnuc (c) (j) : 4*a c≤‖S.position j-z c‖ := by
    rw [hatom j]
    exact atomicCellScale_nucleus_far _
  have HC := conditionalOutCost_ensemble_cover_lower S T.out T.core T.vector z a ha hnuc hcover
  have hcap (c) : (∑ p, sliceExpectation (T.vector p) (fun s x =>
      (localFarCap S ((T.vector p).coreSlice s x).normalized x (z c) (a c))^2))≤8*H :=
    atomic_cap_sq_le_of_raw_bound S T.out T.core T.vector (hz c) (hnuc c) (hraw c)
  have hcount := out_square_cover hT (fun c => Metric.closedBall (z c) (a c))
    (fun _ => measurableSet_closedBall)
    (fun p s => by
      filter_upwards [hcover p s] with x hx
      intro hm i
      obtain ⟨c,hc⟩ := hx hm i
      exact ⟨c,by simpa only [Metric.mem_closedBall,dist_eq_norm] using hc⟩)
  refine (neg_le_neg (Finset.sum_le_sum (fun c _ => ?_))).trans HC
  apply add_le_add
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul (hT.recorded_secondMoment measurableSet_closedBall) (hcap c)
    · exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun s _ => integral_nonneg
        (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
    · exact localCountSecondMoment_nonneg ψ _
  · exact div_le_div_of_nonneg_right hcount (mul_nonneg (by norm_num) (ha c).le)

lemma patches_cover {n : ℕ} {I : Type*} [Fintype I]
    (T : RecordedEnsemble n) (target : I → Space) (htarget : ∀ i, target i≠0)
    (hsupp : T.OutSupported (⋃ i, Metric.closedBall (target i) (80*atomicCellScale (target i)))) :
    ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      ∀ j, ∃ c : I × {v : Space // v∈atomicPatchMesh},
        ‖position x j-atomicMeshCenter (target c.1) c.2.val‖≤
          atomicCellScale (atomicMeshCenter (target c.1) c.2.val) := by
  intro p s
  filter_upwards [(hsupp p).recorded_positions s] with x hx
  intro hm j
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hx hm j)
  obtain ⟨v,hv,hclose⟩ := atomicMesh_cover (htarget i) (position x j)
    (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hi)
  exact ⟨(i,⟨v,hv⟩),hclose⟩

end RecordedEnsemble
end Coulomb

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

lemma RecordedEnsemble.rawSquare_le {n J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J)
    (y : Space) {a : ℝ} (ha : 0<a) :
    T.rawSquare S y a ≤ (attraction S y)^2*T.totalMass := by
  rw [RecordedEnsemble.totalMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [←sliceExpectation_number]
  unfold sliceExpectation
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))
  · exact (mass_coreSlice_integrable (T.vector p) s).mul_const _
  · filter_upwards [] with x
    rw [coreConditionalObservable_raw_positive_weight (T.vector p) (attraction S y)
      (A := {z | 40*a ≤ ‖z-y‖})
      (isClosed_le continuous_const (by fun_prop)).measurableSet y
      (show 0<40*a by positivity) (fun _ h => h)]
    apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
    apply pow_le_pow_left₀ (le_max_right _ _) _ 2
    apply max_le _ (attraction_nonneg S y)
    linarith [restrictedCorePotential_nonneg (T.vector p |>.coreSlice s x |>.normalized) {z | 40*a ≤ ‖z-y‖} y,
      restrictedOutPotential_nonneg x {z | 40*a ≤ ‖z-y‖} y]

lemma RecordedEnsemble.rawSquare_atomic_cap {n J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (hm : T.totalMass=1) {y : Space} (hy : y≠0) :
    T.rawSquare S y (atomicCellScale y) ≤ (totalCharge S/(100000*atomicCellScale y))^2 := by
  simpa only [attraction_atomic S hatom,atomicCellScale_norm,hm,mul_one] using
    T.rawSquare_le S y (atomicCellScale_pos hy)

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

lemma patch_packet_bound {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t F : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (hF : 0≤F)
    (hcap : ∀ w∈Metric.ball y (t-4*b), coreScreenedField S u w≤F) :
    packetKineticError (scaledWindow unitWindow b hb.ne')
      (localTFDensity measurableSet_ball (coreTFField S u measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht y hn))) ≤ 12*a*unitWindowKinetic/b^2*F := by
  have hW : ∀ᵐ x ∂volume.restrict (Metric.ball y (t-4*b)),
      coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn) x≤F := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn),ae_restrict_mem measurableSet_ball] with x hx hy
    exact hx ▸ hcap x hy
  have HM := (localTFMass_bound measurableSet_ball (show 0<12*a by positivity) hF (patch_diameter ha hb ht y)
    (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn)) hW).2
  unfold packetKineticError
  rw [scaledWindow_kinetic unitWindow hb]
  have H := mul_le_mul_of_nonneg_right HM (show 0≤(1/2:ℝ)*(unitWindowKinetic/b^2) by positivity [unitWindowKinetic_nonneg])
  change (1/2:ℝ)*_*(unitWindowKinetic/b^2) ≤ _
  calc
    _ = _*(1/2*(unitWindowKinetic/b^2)) := by ring
    _ ≤ _ := H
    _ = _ := by ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_AtomicBudgetHistory
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

namespace AtomicBudgetHistory
variable {J n j : ℕ} {S : Nuclei J} {ψ : H1Vector n} {B : ℝ}

theorem append (hatom : ∀ i, S.position i=0) (T : AtomicBudgetHistory S ψ B j)
    (hmass : mass ψ=1) {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (hstate : form S ψ≤E+δ) {y : Space} (hy : y≠0) :
    ∃ U : AtomicBudgetHistory S ψ B (j+1),
      U.target=Fin.snoc T.target y ∧
      (∀ H : ℝ,
        (∀ c v, ‖v-U.center c‖≤2*atomicCellScale (U.center c) →
          U.ensemble.rawSquare S v (atomicCellScale v)≤H) →
        atomicCellScale y/(16*ballTrialCoefficient)*T.ensemble.rawSquare S y (atomicCellScale y)≤
          δ+B+(∑ i, atomicIMS ψ (U.target i))+4*ballTrialCoefficient*(screenBaseMass (atomicCellScale y))^2/atomicCellScale y+
          ∑ c, (Real.sqrt (localCountSecondMoment ψ (Metric.closedBall (U.center c) (atomicCellScale (U.center c)))*(8*H))+
            (((Fintype.card (Fin (j+1) × {z : Space // z∈atomicPatchMesh})):ℝ)*
              (∑ d, localCountSecondMoment ψ (Metric.closedBall (U.center d) (atomicCellScale (U.center d)))))/
              (3*atomicCellScale (U.center c)))) := by
  have ha := atomicCellScale_pos hy
  have hnuc (i) : 3*atomicCellScale y≤‖S.position i-y‖ := by
    rw [hatom i]
    have H := atomicCellScale_nucleus_far y
    linarith [atomicCellScale_nonneg y]
  obtain ⟨V,hV,hanti,hsupp,hm,hform,hgain⟩ := T.ensemble.append_radial S ψ T.law T.fermionic
    (atomicPatchRegion T.target) T.support ha y hnuc hE
  have hag : ∑ i : Fin (j+1), atomicIMS ψ (Fin.snoc (α := fun _ => Space) T.target y i)=(∑ i, atomicIMS ψ (T.target i))+atomicIMS ψ y := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
  let U : AtomicBudgetHistory S ψ B (j+1) := {
    ensemble := V
    target := Fin.snoc T.target y
    nonzero := by
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using hy
      · simpa only [Fin.snoc_castSucc] using T.nonzero i
    law := hV
    fermionic := hanti
    support := by rwa [atomicPatchRegion_snoc]
    mass_eq := hm.trans T.mass_eq
    energy := by
      rw [hag]
      have HG := T.energy
      change V.totalForm S≤_
      change V.totalForm S≤T.ensemble.totalForm S+atomicIMS ψ y at hform
      linarith }
  refine ⟨U,rfl,?_⟩
  intro H hraw
  have hcost := RecordedEnsemble.atomic_cost_lower S hatom ψ U.ensemble U.law U.center U.center_nonzero
    (RecordedEnsemble.patches_cover U.ensemble U.target U.nonzero U.support) hraw
  have hm1 : T.ensemble.totalMass=1 := T.mass_eq.trans hmass
  rw [hm1,mul_one,mul_one] at hgain
  have HG := T.energy
  have hs : ∑ i, atomicIMS ψ (U.target i)=(∑ i, atomicIMS ψ (T.target i))+atomicIMS ψ y := hag
  rw [hs]
  change _≤_+atomicIMS ψ y-_ -E+_ at hgain
  linarith

end AtomicBudgetHistory
end Coulomb
end

end
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

lemma atomicBudgetRawValues_cap {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n) (hm : mass ψ=1) {B a w : ℝ} (ha : 0<a) (hw : 0<w) (j : ℕ) :
    ∀ r ∈ atomicBudgetRawValues S ψ B a w j, r ≤ (totalCharge S/(100000*a*w))*4^j := by
  intro r hr
  rcases hr with (rfl|⟨k,hk,T,hT,y,hy,rfl⟩)
  · exact mul_nonneg (div_nonneg (totalCharge_nonneg S) (by positivity)) (by positivity)
  · have hy0 := hy.nonzero ha
    have hay := atomicCellScale_pos hy0
    have hcap := T.ensemble.rawSquare_atomic_cap S hatom (T.mass_eq.trans hm) hy0
    have hb : Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y)) ≤
        totalCharge S/(100000*atomicCellScale y) := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨div_nonneg (totalCharge_nonneg S) (by positivity),hcap⟩
    apply (div_le_iff₀ hw).mpr
    calc
      _ ≤ totalCharge S/(100000*atomicCellScale y) := hb
      _ ≤ totalCharge S/(100000*(a/4^j)) := div_le_div_of_nonneg_left (totalCharge_nonneg S)
        (by positivity) (mul_le_mul_of_nonneg_left (hy.div_lower (by positivity)) (by norm_num))
      _ = _ := by field_simp

lemma atomicBudgetRawValues_bdd {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n) (hm : mass ψ=1) {B a w : ℝ} (ha : 0<a) (hw : 0<w) (j : ℕ) :
    BddAbove (atomicBudgetRawValues S ψ B a w j) := ⟨_,atomicBudgetRawValues_cap S hatom ψ hm ha hw j⟩

lemma atomicBudgetRawSup_nonneg {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n) (hm : mass ψ=1) {B a w : ℝ} (ha : 0<a) (hw : 0<w) (j : ℕ) :
    0 ≤ atomicBudgetRawSup S ψ B a w j :=
  le_csSup (atomicBudgetRawValues_bdd S hatom ψ hm ha hw j) (Set.mem_insert 0 _)

lemma atomicBudgetRawSup_cap {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n) (hm : mass ψ=1) {B a w : ℝ} (ha : 0<a) (hw : 0<w) (j : ℕ) :
    atomicBudgetRawSup S ψ B a w j ≤ (totalCharge S/(100000*a*w))*4^j :=
  csSup_le (atomicBudgetRawValues_nonempty S ψ B a w j) (atomicBudgetRawValues_cap S hatom ψ hm ha hw j)

theorem AtomicBudgetHistory.append_normalized {J n k : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a q B : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hB : B ≤ P*screenEnergy δ a) (hδ : 0 ≤ δ) (hP : 1 ≤ P) (ha : 0<a) (hq : 1 ≤ q)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2)
    (T : AtomicBudgetHistory S ψ B k) (hT : ∀ i, AtomicScaleWindow a q (T.target i))
    (y : Space) (hy : AtomicScaleWindow a q y) :
    ∃ U : AtomicBudgetHistory S ψ B (k+1), U.target=Fin.snoc T.target y ∧
      (∀ i, AtomicScaleWindow a q (U.target i)) ∧
      (∀ G : ℝ, 0 ≤ G →
        (∀ c v, ‖v-U.center c‖ ≤ 2*atomicCellScale (U.center c) →
          U.ensemble.rawSquare S v (atomicCellScale v) ≤ (screenFieldUnit δ P a*G)^2) →
        (Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y))/screenFieldUnit δ P a)^2 ≤
          16*ballTrialCoefficient*(4*q)^8*
            (2+(k+1:ℕ)*atomicIMSConstant+4*ballTrialCoefficient+
              3*(Fintype.card (Fin (k+1) × {z : Space // z∈atomicPatchMesh}):ℝ)*G+
              (Fintype.card (Fin (k+1) × {z : Space // z∈atomicPatchMesh}):ℝ)^3)) := by
  have hy0 := hy.nonzero ha
  have hq0 : 0<q := by linarith
  obtain ⟨U,ht,hgain⟩ := T.append hatom hm hE hstate hy0
  have hU (i) : AtomicScaleWindow a q (U.target i) := by
    rw [ht]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [Fin.snoc_last] using hy
    · simpa only [Fin.snoc_castSucc] using hT i
  refine ⟨U,ht,hU,?_⟩
  intro G hG hraw
  let Q := 4*q
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith
  have hQ0 : 0<Q := by linarith
  have hyQ : AtomicScaleWindow a Q y := hy.enlarge ha.le (by dsimp [Q]; linarith)
  have hUQ (i) : AtomicScaleWindow a Q (U.target i) := (hU i).enlarge ha.le (by dsimp [Q]; linarith)
  have hcQ (c) : AtomicScaleWindow a Q (U.center c) := by
    exact ((hU c.1).mesh hq0.le c.2.property).enlarge ha.le (by dsimp [Q]; linarith)
  have hp0 : 0 ≤ P := by linarith
  have he : 0 < screenEnergy δ a := screenEnergy_pos δ ha
  have hPQ : 1 ≤ P*Q^7 := one_le_mul_of_one_le_of_one_le hP (one_le_pow₀ hQ)
  have hδe : δ ≤ P*Q^7*screenEnergy δ a :=
    (screenEnergy_ge_offset hδ ha).trans (le_mul_of_one_le_left he.le hPQ)
  have hBe : B ≤ P*Q^7*screenEnergy δ a := by
    apply hB.trans
    have H := mul_le_mul_of_nonneg_left (one_le_pow₀ hQ : 1≤Q^7) (mul_nonneg hp0 he.le)
    nlinarith
  have HI (i) : atomicIMS ψ (U.target i) ≤ atomicIMSConstant*P*Q^7*screenEnergy δ a := by
    apply (atomicIMS_le_units ψ hm hδ hP hc (U.nonzero i)).trans
    convert mul_le_mul_of_nonneg_left ((hUQ i).energy ha hQ hδ)
      (mul_nonneg atomicIMSConstant_nonneg hp0) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hisum : (∑ i, atomicIMS ψ (U.target i)) ≤ (k+1:ℕ)*atomicIMSConstant*P*Q^7*screenEnergy δ a := by
    have H := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => HI i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using H
  have hbase : (screenBaseMass (atomicCellScale y))^2/atomicCellScale y ≤ screenEnergy δ (atomicCellScale y) := by
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (screenBaseMass_nonneg _) (screenMass_ge_base _ _) 2)
      (atomicCellScale_nonneg _)
  have henergy : screenEnergy δ (atomicCellScale y) ≤ P*Q^7*screenEnergy δ a :=
    calc
      _ ≤ Q^7*screenEnergy δ a := hyQ.energy ha hQ hδ
      _ ≤ P*(Q^7*screenEnergy δ a) := le_mul_of_one_le_left (mul_nonneg (pow_nonneg hQ0.le _) he.le) hP
      _ = _ := by ring
  have hbase' : 4*ballTrialCoefficient*(screenBaseMass (atomicCellScale y))^2/atomicCellScale y ≤
      4*ballTrialCoefficient*P*Q^7*screenEnergy δ a := by
    have H := mul_le_mul_of_nonneg_left (hbase.trans henergy) (show 0 ≤ 4*ballTrialCoefficient by positivity [ballTrialCoefficient_pos])
    simpa only [mul_div_assoc,mul_assoc] using H
  have hcost := atomic_cell_cost_units ψ hδ hP ha hQ hG U.center hcQ hc
  have HG := hgain ((screenFieldUnit δ P a*G)^2) hraw
  let L : ℝ := Fintype.card (Fin (k+1) × {z : Space // z∈atomicPatchMesh})
  have HG' : atomicCellScale y/(16*ballTrialCoefficient)*T.ensemble.rawSquare S y (atomicCellScale y) ≤
      P*Q^7*screenEnergy δ a*(2+(k+1:ℕ)*atomicIMSConstant+4*ballTrialCoefficient+3*L*G+L^3) := by
    dsimp [L]
    nlinarith [hδe,hBe,hisum,hbase',hcost]
  exact screening_gain_normalized ha (atomicCellScale_pos hy0) hQ0 ballTrialCoefficient_pos
    (screenFieldUnit_pos hP ha) (T.ensemble.rawSquare_nonneg S y _) hyQ.1
    (screenFieldUnit_square hp0 ha) HG'

lemma AtomicBudgetHistory.rawSquare_le_next_sup {J n k j : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {B a w : ℝ} (ha : 0<a) (hw : 0<w) (hk : k≤j)
    (U : AtomicBudgetHistory S ψ B (k+1))
    (hU : ∀ i, AtomicScaleWindow a (4^j) (U.target i))
    (c) (v : Space) (hv : ‖v-U.center c‖ ≤ 2*atomicCellScale (U.center c)) :
    U.ensemble.rawSquare S v (atomicCellScale v) ≤
      (w*atomicBudgetRawSup S ψ B a w (j+1))^2 := by
  have hq : (4:ℝ)^j ≤ 4^(j+1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (show (0:ℝ)≤4 by norm_num) j]
  have htargets (i) : AtomicScaleWindow a (4^(j+1)) (U.target i) :=
    (hU i).enlarge ha.le hq
  have hvw : AtomicScaleWindow a (4^(j+1)) v := by
    have H := (hU c.1).mesh_near (by positivity) c.2.property hv
    simpa only [pow_succ,mul_comm (4:ℝ)] using H
  have H : Real.sqrt (U.ensemble.rawSquare S v (atomicCellScale v))/w ≤
      atomicBudgetRawSup S ψ B a w (j+1) :=
    le_csSup (atomicBudgetRawValues_bdd S hatom ψ hm ha hw (j+1))
      (Set.mem_insert_of_mem _ ⟨k+1,Nat.add_le_add_right hk 1,U,htargets,v,hvw,rfl⟩)
  have HH := (div_le_iff₀ hw).mp H
  rw [mul_comm] at HH
  exact ((Real.sqrt_le_iff).mp HH).2

lemma atomicBudgetRawValues_recursion {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a B : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hB : B≤P*screenEnergy δ a) (hδ : 0≤δ) (hP : 1≤P) (ha : 0<a)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) (j : ℕ) :
    ∀ r∈atomicBudgetRawValues S ψ B a (screenFieldUnit δ P a) j,
      r^2 ≤ atomicBudgetRecursionC^(j+1)*(1+atomicBudgetRawSup S ψ B a (screenFieldUnit δ P a) (j+1)) := by
  let w := screenFieldUnit δ P a
  have hw : 0<w := screenFieldUnit_pos hP ha
  let G := atomicBudgetRawSup S ψ B a w (j+1)
  have hG : 0≤G := atomicBudgetRawSup_nonneg (B:=B) S hatom ψ hm ha hw (j+1)
  have hC : 0≤atomicBudgetRecursionC := le_trans (by norm_num) atomicBudgetRecursionC_ge_four
  intro r hr
  rcases hr with (rfl|⟨k,hk,T,hT,y,hy,rfl⟩)
  · simpa only [zero_pow (by omega : 2≠0)] using mul_nonneg (pow_nonneg hC (j+1)) (by linarith : 0≤1+G)
  obtain ⟨U,ht,hU,hgain⟩ := T.append_normalized S hatom ψ hm hE hstate hB hδ hP ha
    (one_le_pow₀ (by norm_num : (1:ℝ)≤4)) hc hT y hy
  have HG := hgain G hG (U.rawSquare_le_next_sup S hatom ψ hm ha hw hk hU)
  let M : ℝ := Fintype.card {z : Space // z∈atomicPatchMesh}
  let L : ℝ := Fintype.card (Fin (k+1) × {z : Space // z∈atomicPatchMesh})
  have hLM : L ≤ (j+1:ℕ)*M := by
    dsimp [L,M]
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hk 1) (Nat.cast_nonneg _)
  have Hpoly0 := screening_polynomial_bound atomicIMSConstant_nonneg
    (show 0≤ballTrialCoefficient+(1/4:ℝ) by linarith [ballTrialCoefficient_pos])
    (show 0≤M by positivity) hG (Nat.cast_nonneg (k+1))
    (show 0≤L by positivity) (show (1:ℝ)≤(j+1:ℕ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
    (show ((k+1:ℕ):ℝ)≤(j+1:ℕ) by exact_mod_cast Nat.add_le_add_right hk 1) hLM
  have Hpoly : 2+(k+1:ℕ)*atomicIMSConstant+4*ballTrialCoefficient+3*L*G+L^3 ≤
      (2+atomicIMSConstant+4*ballTrialCoefficient+3*M+M^3)*(j+1:ℕ)^3*(1+G) := by
    convert Hpoly0 using 1 <;> ring
  have hA : 16*ballTrialCoefficient*(2+atomicIMSConstant+4*ballTrialCoefficient+3*M+M^3) ≤
      atomicBudgetRecursionA := le_max_right _ _
  calc
    _ ≤ 16*ballTrialCoefficient*(4*4^j)^8*
        (2+(k+1:ℕ)*atomicIMSConstant+4*ballTrialCoefficient+3*L*G+L^3) := HG
    _ ≤ 16*ballTrialCoefficient*(4*4^j)^8*
        ((2+atomicIMSConstant+4*ballTrialCoefficient+3*M+M^3)*(j+1:ℕ)^3*(1+G)) :=
      mul_le_mul_of_nonneg_left Hpoly (by positivity [ballTrialCoefficient_pos])
    _ = (16*ballTrialCoefficient*(2+atomicIMSConstant+4*ballTrialCoefficient+3*M+M^3))*
        ((4:ℝ)^(j+1))^8*(j+1:ℕ)^3*(1+G) := by rw [pow_succ]; ring
    _ ≤ atomicBudgetRecursionA*((4:ℝ)^(j+1))^8*(j+1:ℕ)^3*(1+G) := by
      gcongr
    _ ≤ atomicBudgetRecursionC^(j+1)*(1+G) :=
      mul_le_mul_of_nonneg_right (screening_exponential_majorant (le_max_left _ _) j) (by linarith)

theorem atomicBudgetRawSup_recursion {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a B : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hB : B≤P*screenEnergy δ a) (hδ : 0≤δ) (hP : 1≤P) (ha : 0<a)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) (j : ℕ) :
    (atomicBudgetRawSup S ψ B a (screenFieldUnit δ P a) j)^2 ≤
      atomicBudgetRecursionC^(j+1)*(1+atomicBudgetRawSup S ψ B a (screenFieldUnit δ P a) (j+1)) := by
  let R := atomicBudgetRecursionC^(j+1)*(1+atomicBudgetRawSup S ψ B a (screenFieldUnit δ P a) (j+1))
  have hw := screenFieldUnit_pos (δ:=δ) hP ha
  have hnonneg := atomicBudgetRawSup_nonneg (B:=B) S hatom ψ hm ha hw j
  have hbound : atomicBudgetRawSup S ψ B a (screenFieldUnit δ P a) j ≤ Real.sqrt R := by
    apply csSup_le (atomicBudgetRawValues_nonempty _ _ _ _ _ _)
    intro r hr
    exact Real.le_sqrt_of_sq_le (atomicBudgetRawValues_recursion S hatom ψ hm hE hstate hB hδ hP ha hc j r hr)
  have hR : 0≤R := by
    apply mul_nonneg (pow_nonneg (le_trans (by norm_num) atomicBudgetRecursionC_ge_four) _)
    linarith [atomicBudgetRawSup_nonneg (B:=B) S hatom ψ hm ha hw (j+1)]
  exact (pow_le_pow_left₀ hnonneg hbound 2).trans_eq (Real.sq_sqrt hR)

theorem atomicBudgetRawSup_uniform {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a B : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hB : B≤P*screenEnergy δ a) (hδ : 0≤δ) (hP : 1≤P) (ha : 0<a)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) (j : ℕ) :
    atomicBudgetRawSup S ψ B a (screenFieldUnit δ P a) j ≤ 2*atomicBudgetRecursionC^(j+2) := by
  have hw := screenFieldUnit_pos (δ:=δ) hP ha
  have hC : 1≤atomicBudgetRecursionC := le_trans (by norm_num) atomicBudgetRecursionC_ge_four
  apply geometric_screening_recursion_all hC
    (div_nonneg (totalCharge_nonneg S) (show 0≤100000*a*screenFieldUnit δ P a by positivity))
    _ (atomicBudgetRawSup_recursion S hatom ψ hm hE hstate hB hδ hP ha hc) j
  intro l
  apply (atomicBudgetRawSup_cap S hatom ψ hm ha hw l).trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (totalCharge_nonneg S) (by positivity))
  exact (pow_le_pow_left₀ (by norm_num) atomicBudgetRecursionC_ge_four l).trans
    (pow_le_pow_right₀ hC (by omega))

theorem AtomicBudgetHistory.positive_field {J n j : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a B : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hB : B≤P*screenEnergy δ a) (hδ : 0≤δ) (hP : 1≤P) (ha : 0<a)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2)
    (T : AtomicBudgetHistory S ψ B j) (hT : ∀ i, AtomicScaleWindow a (4^j) (T.target i))
    (y : Space) (hy : AtomicScaleWindow a (4^j) y) :
    Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y)) ≤
      2*atomicBudgetRecursionC^(j+2)*screenFieldUnit δ P a := by
  have hw := screenFieldUnit_pos (δ:=δ) hP ha
  have H : Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y))/screenFieldUnit δ P a ≤
      atomicBudgetRawSup S ψ B a (screenFieldUnit δ P a) j :=
    le_csSup (atomicBudgetRawValues_bdd S hatom ψ hm ha hw j)
      (Set.mem_insert_of_mem _ ⟨j,le_rfl,T,hT,y,hy,rfl⟩)
  exact (div_le_iff₀ hw).mp (H.trans (atomicBudgetRawSup_uniform S hatom ψ hm hE hstate hB hδ hP ha hc j))

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

lemma RecordedEnsemble.deletedSquare_le {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hC : T.Conserves ψ) {y : Space} {t b : ℝ}
    (hs : T.OutSupported (Metric.closedBall y (t+b))) :
    T.deletedSquare y t b≤localCountSecondMoment ψ (deletedShell y t b) := by
  have HE : T.deletedSquare y t b=
      ∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount (deletedShell y t b) x)^2) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro s hs'
    apply integral_congr_ae
    filter_upwards [(hs p).recorded_positions s] with x hx
    by_cases hm : mass ((T.vector p).coreSlice s x)=0
    · simp only [hm,zero_mul]
    · congr 2
      apply Finset.sum_congr rfl
      intro i hi
      have hi : ‖position x i-y‖≤t+b := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx hm i
      have he : (position x i∈{z | t-7*b≤‖z-y‖}) ↔ position x i∈deletedShell y t b := by
        change (t-7*b≤‖position x i-y‖) ↔ (t-7*b≤‖position x i-y‖ ∧ ‖position x i-y‖≤t+b)
        exact ⟨fun h => ⟨h,hi⟩,And.left⟩
      simp only [Set.indicator_apply,he]
  rw [HE]
  exact hC.recorded_secondMoment (deletedShell_measurable y t b)

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

lemma potentialForm_count_join_of_support {m k : ℕ} {u : H1Vector k}
    {A B : Set Space} (hAB : Disjoint A B) (hu : SpatiallySupported u A) (x : Configuration m) :
    potentialForm (fun z => (localCount B (joinConfiguration m k (x,z)))^2) u=
      (localCount B x)^2*mass u := by
  rw [←potentialForm_const ((localCount B x)^2) u]
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [hu s] with z hz
  by_cases h : z∈allPositions A
  · rw [localCount_join,localCount_eq_zero_of_allPositions hAB h,add_zero]
  · rw [hz h,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,mul_zero]

lemma sliceExpectation_localCount_sq_eq {m k : ℕ} (u : H1Vector (m+k))
    {A B : Set Space} (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hu : PartlySupported u (coreIndexSet m k) A) :
    sliceExpectation u (fun _ x => (localCount B x)^2)=localCountSecondMoment u B := by
  let W := fun x : Configuration (m+k) => (localCount B x)^2
  have hWB : ∀ x, |W x|≤((m+k:ℕ):ℝ)^2 := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (localCount_nonneg _ _) (localCount_le _ _) 2
  change sliceExpectation u (fun _ x => (localCount B x)^2)=potentialForm W u
  rw [←sliceExpectation_coreConditionalObservable u W ((localCount_measurable hB).pow_const 2) hWB]
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [hu.coreSlice s] with x hx
  by_cases hm : mass (u.coreSlice s x)=0
  · simp only [hm,zero_mul]
  · have hm' := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hm)
    unfold coreConditionalObservable
    rw [potentialForm_count_join_of_support hAB hx.normalized x,mass_normalized _ hm',mul_one]

lemma RecordedEnsemble.Conserves.recorded_secondMoment_eq {n : ℕ} {T : RecordedEnsemble n}
    {ψ : H1Vector n} (hT : T.Conserves ψ) {A B : Set Space} (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hcs : T.CoreSupported A) :
    (∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount B x)^2))=localCountSecondMoment ψ B := by
  rw [←hT.secondMoment hB]
  exact Finset.sum_congr rfl (fun p _ => sliceExpectation_localCount_sq_eq (T.vector p) hB hAB (hcs p))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PhysicalCount
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

lemma patch_retained_nucleus_separated {J n : ℕ} (S : Nuclei J) {a b t : ℝ}
    (_ : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (x : Configuration n) :
    ∀ j i, i∈patchRetained y t b x → Real.sqrt 3*b≤‖S.position j-position x i‖ := by
  intro j i hi
  have hret := (patchRetained_mem ..).mp hi
  have H := norm_sub_le_norm_sub_add_norm_sub (S.position j) (position x i) y
  have hs : Real.sqrt 3≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  nlinarith [hn j]

lemma patchFineTF_weight_integrable {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t≤6*a)
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    Integrable (fun x => mass (ψ.coreSlice s x)*rawThomasFermiEnergy
      (coreScreenedField S (ψ.coreSlice s x).normalized)
      (retainedFineDensity b (patchRetained y t b x) (position x))) := by
  apply (discreteFineTF_weight_integrable S ψ hb (patchRetained y t b) (patchRetained_measurable y t b) s).congr
  filter_upwards [hcs] with x hx
  congr 1
  exact discreteFineTF_eq_raw S ψ hb (patchRetained y t b) s x hx
    (patch_retained_nucleus_separated S ha hb hsmall ht y hn x)
    (patch_retained_separated ha hb y x)

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

lemma patch_packet_expected_bound {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (F : Spins m → Configuration m → ℝ)
    (hFm : ∀ s, AEStronglyMeasurable (F s) volume)
    (hF0 : ∀ s, ∀ᵐ x, 0≤F s x)
    (hFi : ∀ s, Integrable (fun x => mass (u.coreSlice s x)*(F s x)^2))
    (hcap : ∀ s, ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S (u.coreSlice s x).normalized w≤F s x) :
    sliceExpectation u (fun s x => packetKineticError (scaledWindow unitWindow b hb.ne')
      (localTFDensity measurableSet_ball (coreTFField S (u.coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht y hn))))≤
      (12*a*unitWindowKinetic/b^2)*sliceExpectation u F := by
  unfold sliceExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hTF := coreTF_conditional_integrable measurableSet_ball S u s ha
    (patch_nucleus_separation S ha hb ht y hn) (show 0<12*a by positivity)
    (patch_diameter ha hb ht y) (F s) (hF0 s) (hFi s) (hcap s)
  have hi : Integrable (fun x => mass (u.coreSlice s x)*packetKineticError (scaledWindow unitWindow b hb.ne')
      (localTFDensity measurableSet_ball (coreTFField S (u.coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht y hn)))) := by
    unfold packetKineticError
    convert hTF.1.mul_const ((1/2:ℝ)*(∑ j : Fin 3, ∫ z : Space,
      (fderiv ℝ (scaledWindow unitWindow b hb.ne') z (EuclideanSpace.single j 1))^2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    ring
  rw [←integral_const_mul]
  apply integral_mono_ae hi ((weighted_cap_integrable (mass_coreSlice_integrable u s)
    (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm s) (hF0 s) (hFi s)).const_mul _)
  filter_upwards [hF0 s,hcap s] with x hf hc
  simpa only [mul_left_comm (mass _) (12*a*unitWindowKinetic/b^2)] using
    mul_le_mul_of_nonneg_left (patch_packet_bound S _ ha hb ht y hn hf hc) (mass_nonneg _)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicWeighted
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

def atomicWeight (e:ℝ) (x:Space):ℝ:=(coulombKernel x+e)⁻¹
end Coulomb
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

lemma coreField_le_atomicPatchCap {J m k : ℕ} (S : Nuclei J) (hatom : ∀ j, S.position j=0)
    (u : H1Vector k) (x : Configuration m) {y : Space} (hy : y≠0) {w : Space}
    (hw : ‖w-y‖≤80*atomicCellScale y) : coreScreenedField S u w≤atomicPatchCap S u x y := by
  obtain ⟨z,hz,hwz⟩ := atomicMesh_cover hy w hw
  have hz0 : atomicMeshCenter y z≠0 := atomicCellScale_near_nonzero hy
    (by nlinarith [atomicMeshCenter_distance y z hz,atomicCellScale_nonneg y])
  have hza := atomicCellScale_pos hz0
  have H := coreField_le_local_far_cap S u x hza (atomicMeshCenter y z) w hwz
    (fun j => by rw [hatom j]; exact atomicCellScale_nucleus_far _)
  have hcap := le_sqrt_sum_squares
    (fun v : {z : Space // z∈atomicPatchMesh} =>
      localFarCap S u x (atomicMeshCenter y v.val) (atomicCellScale (atomicMeshCenter y v.val)))
    (⟨z,hz⟩ : {z : Space // z∈atomicPatchMesh})
  have hcount : (m:ℝ)/(3*atomicCellScale (atomicMeshCenter y z))≤2*(m:ℝ)/(3*atomicCellScale y) := by
    calc
      _≤(m:ℝ)/(3*(atomicCellScale y/2)) := div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (by positivity [atomicCellScale_pos hy]) (by linarith [(atomicMeshCenter_comparable y z hz).1])
      _=_ := by ring
  exact H.trans (add_le_add hcap hcount)

lemma atomicPatchCap_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) (y : Space) :
    AEStronglyMeasurable (fun x => atomicPatchCap S (u.coreSlice s x).normalized x y) volume := by
  apply AEStronglyMeasurable.add_const
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  exact Finset.aestronglyMeasurable_fun_sum _ (fun z _ =>
    (localFarCap_normalized_slice_aestronglyMeasurable S u s _ _).pow 2)

lemma atomicPatchCap_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) (u : H1Vector (m+k)) (s : Spins m) {y : Space} (hy : y≠0) :
    Integrable (fun x => mass (u.coreSlice s x)*(atomicPatchCap S (u.coreSlice s x).normalized x y)^2) := by
  let C := {z : Space // z∈atomicPatchMesh}
  have hi (z : C) : Integrable (fun x => mass (u.coreSlice s x)*
      (localFarCap S (u.coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2) := by
    apply localFarCap_weight_integrable S u s
    · exact atomicCellScale_pos (atomicCellScale_near_nonzero hy (by
        nlinarith [atomicMeshCenter_distance y z.val z.property,atomicCellScale_nonneg y]))
    · intro j
      rw [hatom j]
      exact atomicCellScale_nucleus_far _
  have HR : Integrable (fun x => 2*(∑ z : C, mass (u.coreSlice s x)*
      (localFarCap S (u.coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2)+
      mass (u.coreSlice s x)*(8*(m:ℝ)^2/(9*(atomicCellScale y)^2))) :=
    ((integrable_finsetSum _ (fun z _ => hi z)).const_mul 2).add ((mass_coreSlice_integrable u s).mul_const _)
  apply HR.mono'
    ((mass_coreSlice_integrable u s).aestronglyMeasurable.mul ((atomicPatchCap_slice_aestronglyMeasurable S u s y).pow 2))
  filter_upwards [] with x
  simp only [Pi.mul_apply,Pi.pow_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (mass_nonneg _) (sq_nonneg _))]
  have H := mul_le_mul_of_nonneg_left (atomicPatchCap_square_le S (u.coreSlice s x).normalized x y) (mass_nonneg (u.coreSlice s x))
  simpa only [Pi.add_apply,mul_add,Finset.mul_sum,mul_left_comm (mass _) 2] using H

theorem atomicPatchCap_ensemble_square {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) (T : RecordedEnsemble n) {y : Space} (hy : y≠0) {H : ℝ}
    (hraw : ∀ v, AtomicScaleWindow (atomicCellScale y) 4 v → T.rawSquare S v (atomicCellScale v)≤H) :
    (∑ p, sliceExpectation (T.vector p) (fun s x => (atomicPatchCap S ((T.vector p).coreSlice s x).normalized x y)^2))≤
      16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*H+
        8*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))/(9*(atomicCellScale y)^2) := by
  let C := {z : Space // z∈atomicPatchMesh}
  have hz (z : C) : atomicMeshCenter y z.val≠0 := atomicCellScale_near_nonzero hy (by
    nlinarith [atomicMeshCenter_distance y z.val z.property,atomicCellScale_nonneg y])
  have hnuc (z : C) (j) : 4*atomicCellScale (atomicMeshCenter y z.val)≤‖S.position j-atomicMeshCenter y z.val‖ := by
    rw [hatom j]
    exact atomicCellScale_nucleus_far _
  have Hcap (z : C) : (∑ p, sliceExpectation (T.vector p) (fun s x =>
      (localFarCap S ((T.vector p).coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2))≤8*H := by
    apply atomic_cap_sq_le_of_raw_bound S T.out T.core T.vector (hz z) (hnuc z)
    intro v hv
    apply hraw v
    have hw : AtomicScaleWindow (atomicCellScale y) 1 y := by constructor <;> simp
    simpa only [mul_one] using hw.mesh_near zero_le_one z.property hv
  have Hp (p : T.index) : sliceExpectation (T.vector p) (fun s x => (atomicPatchCap S ((T.vector p).coreSlice s x).normalized x y)^2)≤
      2*(∑ z : C, sliceExpectation (T.vector p) (fun s x =>
        (localFarCap S ((T.vector p).coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2))+
      (8*(T.out p:ℝ)^2/(9*(atomicCellScale y)^2))*mass (T.vector p) := by
    rw [←sliceExpectation_number (T.vector p) (8*(T.out p:ℝ)^2/(9*(atomicCellScale y)^2))]
    unfold sliceExpectation
    rw [Finset.sum_comm,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s hs
    rw [←integral_finsetSum _ (fun z _ => localFarCap_weight_integrable S (T.vector p) s (atomicCellScale_pos (hz z)) _ (hnuc z) 2),←integral_const_mul,
      ←integral_add ((integrable_finsetSum _ (fun z _ => localFarCap_weight_integrable S (T.vector p) s (atomicCellScale_pos (hz z)) _ (hnuc z) 2)).const_mul 2)
        ((mass_coreSlice_integrable (T.vector p) s).mul_const _)]
    apply integral_mono_ae (atomicPatchCap_weight_integrable S hatom (T.vector p) s hy)
      (((integrable_finsetSum _ (fun z _ => localFarCap_weight_integrable S (T.vector p) s (atomicCellScale_pos (hz z)) _ (hnuc z) 2)).const_mul 2).add
        ((mass_coreSlice_integrable (T.vector p) s).mul_const _))
    filter_upwards [] with x
    have HH := mul_le_mul_of_nonneg_left (atomicPatchCap_square_le S ((T.vector p).coreSlice s x).normalized x y)
      (mass_nonneg ((T.vector p).coreSlice s x))
    simpa only [Pi.add_apply,mul_add,Finset.mul_sum,mul_left_comm (mass _) 2] using HH
  calc
    _≤∑ p, (2*(∑ z : C, sliceExpectation (T.vector p) (fun s x =>
        (localFarCap S ((T.vector p).coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2))+
      (8*(T.out p:ℝ)^2/(9*(atomicCellScale y)^2))*mass (T.vector p)) := Finset.sum_le_sum (fun p _ => Hp p)
    _=2*(∑ z : C, ∑ p, sliceExpectation (T.vector p) (fun s x =>
        (localFarCap S ((T.vector p).coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2))+
      8*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))/(9*(atomicCellScale y)^2) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_comm]
      congr 1
      simp only [Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _≤2*(∑ _z : C, 8*H)+8*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))/(9*(atomicCellScale y)^2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => Hcap z)) (show (0:ℝ)≤2 by norm_num)) le_rfl
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe, C]; ring

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

theorem exists_atomic_thin_screened_sharp {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)) :
    ∃ t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t b ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      T.ensemble.deletedSquare y t b≤
        18*atomicPatchCountFactor*(b/atomicCellScale y)*screenCountParameter ψ δ*(screenMass δ (atomicCellScale y))^2 ∧
      (∑ p, (T.ensemble.out p:ℝ)^2*mass (T.ensemble.vector p))≤
        atomicPatchCountFactor*screenCountParameter ψ δ*(screenMass δ (atomicCellScale y))^2 ∧
      (∀ v, AtomicScaleWindow (atomicCellScale y) 4 v →
        Real.sqrt (T.ensemble.rawSquare S v (atomicCellScale v))≤
          2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*
            screenFieldUnit δ (screenCountParameter ψ δ) (atomicCellScale y)) := by
  let P := screenCountParameter ψ δ
  have hP : 1≤P := screenCountParameter_ge_one ψ δ
  have hP0 : 0≤P := le_trans zero_le_one hP
  have hc := fun z hz => screenCountParameter_controls ψ hm δ (y:=z) hz
  obtain ⟨t,ht,hdel⟩ := exists_atomic_deletedShell ψ hm hδ hy hb hsmall
  have ht0 : 0≤t := by nlinarith [ht.1,atomicCellScale_nonneg y]
  have hwidth : t+b≤80*atomicCellScale y := by linarith [ht.2,atomicCellScale_nonneg y]
  obtain ⟨T,hTr,ho,hcs,hos,hEt⟩ := thin_localization_history_sharp S ψ hψ hy ht0 hb hwidth
  have hbudget := thinIMS_budget ψ hm hδ hP hc hy hb hwidth hcond
  have hP' : 1≤thinReserveFactor*P := by nlinarith [thinReserveFactor_ge_one]
  have hc' (z : Space) (hz : z≠0) : localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z))≤
      (thinReserveFactor*P)*(screenMass δ (atomicCellScale z))^2 :=
    (hc z hz).trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left hP0 thinReserveFactor_ge_one) (sq_nonneg _))
  refine ⟨t,ht,T,hEt,ho,hcs,hos,(RecordedEnsemble.deletedSquare_le T.law hos).trans hdel,?_,?_⟩
  · exact (RecordedEnsemble.out_square_le T.law measurableSet_closedBall hos).trans
      ((localCountSecondMoment_mono ψ measurableSet_closedBall (Metric.closedBall_subset_closedBall hwidth)).trans
        (atomicPatch_secondMoment ψ hδ hP0 hc hy))
  · intro v hv
    have H := T.positive_field S hatom ψ hm hE hstate hbudget hδ hP' (atomicCellScale_pos hy) hc'
      (fun i => by rw [hTr i]; constructor <;> norm_num <;> linarith [atomicCellScale_nonneg y])
      v (by simpa only [pow_one] using hv)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    simp only [screenFieldUnit,Real.sqrt_mul thinReserveFactor_nonneg]
    ring

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical

end

end OAI
end


