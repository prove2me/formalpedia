-- Prove2me | Definitions.Def_OAIQ059C008
-- name    : OAIQ059C008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:52:44.723481+00:00
-- url     : https://prove2.me/theorems/ff4f4fda-9d6f-4706-9347-b474e954d932
-- title:
--   Definitions bundle OAIQ059C008 of the split of OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 15 definitions, 1 instance and 36 theorems. The definitions and types are `OAI.ScalarConductivity.compactVoltageJetModule`, `OAI.ScalarConductivity.criticalWallRegion`, `OAI.ScalarConductivity.cylinderEndJet`, `OAI.ScalarConductivity.physicalBlockTensor`, `OAI.ScalarConductivity.physicalBlockTensorList`, `OAI.ScalarConductivity.physicalEndTensor`, `OAI.ScalarConductivity.sourceAveragePull`, `OAI.ScalarConductivity.sourceAveragePullIter`, `OAI.ScalarConductivity.sourceDifferencePull`, `OAI.ScalarConductivity.sourceWordPull`, `OAI.ScalarConductivity.sourceWordTraceCLM`, `OAI.ScalarConductivity.splicedAttachedGradient`, `OAI.ScalarConductivity.torusInitialPair`, `OAI.ScalarConductivity.zeroVoltageGradientMap`, `OAI.ScalarConductivity.zeroVoltageJets`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Conductivity_Branching_ParametricCorrectionTransport`, `Conductivity_Branching_TorusEndingCorrection`, `Conductivity_Flux_AttachedSplicedGreen`, `Conductivity_Flux_CylinderSlopeGreen`, `Conductivity_Flux_PhysicalBlockTensor`, `Conductivity_Geometry_CoordinateCorrectionC0`, `Conductivity_Geometry_CoordinateWeakCorrection`, `Conductivity_Geometry_UniformPhysicalBoxCorrection`, `Conductivity_Sobolev_LocalPhysicalCorrectionBound`, `Conductivity_Sobolev_UniformLocalPhysicalCorrection`, `Conductivity_Sobolev_VoltageJetCompletion`, `Conductivity_Sources_BranchCombine`, `Conductivity_Sources_CopiedEnergyAlgebra`, `Conductivity_Sources_CriticalWallGap`, `Conductivity_Sources_WordTrace`, `Conductivity_Variational_ParametricGlobalCorrection`, `Conductivity_Variational_ParametricLocalRegularCorrection`, `Conductivity_Variational_ParametricMomentSmall`, `Conductivity_Variational_RegularVanishingFamily`, `Conductivity_Walls_CriticalWall`, `Conductivity_Walls_CriticalWallFamilyCorrection`, `Conductivity_Walls_CriticalWallHomogeneous`, `Conductivity_Walls_CriticalWallRegion`, `Conductivity_Walls_CriticalWallResidual`, `Conductivity_Walls_CriticalWallTensor`, `Conductivity_Walls_ParametricWallTensors`, `Conductivity_Walls_WallSideMoments`, `Conductivity_Walls_WallTransferParametric`, `Conductivity_Walls_WallVanishingMomentCoefficients`.
--
--   **Imports.** It imports the published bundle `Def_Conductivity`; the bundles `OAIQ059C006` and `OAIQ059C007` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists`, `OAI.ScalarConductivity.finite_field_scalarization` and `OAI.ScalarConductivity.splicedAttached_energy_ae`; the proofs of `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative_regular`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists`, `OAI.ScalarConductivity.boundedRootSources_nonempty`, `OAI.ScalarConductivity.elliptic_fourier_matching_regular`, `OAI.ScalarConductivity.finite_field_scalarization`, `OAI.ScalarConductivity.fourierMatchingFamily_correction`, `OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg`, `OAI.ScalarConductivity.fullAttachedEnd_smooth_green_pos`, `OAI.ScalarConductivity.main_nonuniqueness`, `OAI.ScalarConductivity.matchedEnding_regularRegion_ae` and `OAI.ScalarConductivity.splicedAttached_energy_ae`.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C006
import Definitions.Def_OAIQ059C007

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CoordinateWeakCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

lemma cube_weak_divergence_to_coordinates {F₁ F₂ F₃ r : Box3 → ℝ}
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂)
    (h₃ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₃)
    (hs₁ : HasCompactSupport F₁) (hs₂ : HasCompactSupport F₂) (hs₃ : HasCompactSupport F₃)
    (hd : ∀ p,cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
      cubePartial F₃ ((0,0),1) p=r p)
    (φ : Coord3 → ℝ) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) :
    (∫ x,fderiv ℝ φ x ![F₁ (boxCoordinates x),F₂ (boxCoordinates x),F₃ (boxCoordinates x)])=
      -(∫ x,φ x*r (boxCoordinates x)) := by
  have he (p w : Box3) : fderiv ℝ (φ∘boxCoordinates.symm) p w=
      fderiv ℝ φ (boxCoordinates.symm p) (boxCoordinates.symm w) := by
    rw [fderiv_comp p (hφ.differentiable (by simp) _) boxCoordinates.symm.differentiableAt,
      boxCoordinates.symm.fderiv]
    rfl
  have h := cube_weak_divergence h₁ h₂ h₃ hs₁ hs₂ hs₃ hd (φ∘boxCoordinates.symm)
    (hφ.comp boxCoordinates.symm.contDiff)
  simp_rw [he,Function.comp_apply] at h
  rw [←boxCoordinates_integral (fun p => fderiv ℝ φ (boxCoordinates.symm p)
    (boxCoordinates.symm ((F₁ p,F₂ p),F₃ p))),
    ←boxCoordinates_integral (fun p => φ (boxCoordinates.symm p)*r p)] at h
  simpa only [boxCoordinates.symm_apply_apply,boxCoordinates_symm_apply] using h

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CoordinateCorrectionC0
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

theorem compact_coordinate_box_correction_C0 {a b c d : Fin 3 → ℝ}
    (hab : ∀ i,a i<b i) (hca : ∀ i,c i<a i) (hbd : ∀ i,b i<d i) :
    ∃ L : ℝ,0<L ∧ ∀ (r₁ r₂ : Box3 → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ → ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ →
      HasCompactSupport r₁ → HasCompactSupport r₂ →
      tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      (∫ p,r₁ p)=0 → (∫ p,r₂ p)=0 →
      (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0 → ∀ M : ℝ,0≤M →
      UniformC1Bound r₁ M → UniformC1Bound r₂ M →
    ∃ B : Coord3 → Mat3,
      ContDiff ℝ (↑(⊤ : ℕ∞)) B ∧ HasCompactSupport B ∧
      tsupport B⊆boxCoordinates ⁻¹' ((Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2)) ∧
      (∀ x,(B x).IsSymm) ∧
      (∀ φ : Coord3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        (∫ x,fderiv ℝ φ x ((B x).col 0))=-(∫ x,φ x*r₁ (boxCoordinates x))) ∧
      (∀ φ : Coord3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        (∫ x,fderiv ℝ φ x ((B x).col 1))=-(∫ x,φ x*r₂ (boxCoordinates x))) ∧
      (∀ x,‖B x‖≤L*M) := by
  obtain ⟨L,hL,solve⟩ := compact_regular_box_correction_C0 hab hca hbd
  refine ⟨L,hL,?_⟩
  intro r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  obtain ⟨H,hH,hcH,hsH,hsy,hd₁,hd₂,hbH⟩ :=
    solve r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  let B : Coord3 → Mat3 := fun x i j => H i j (boxCoordinates x)
  have hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => (hH i j).comp boxCoordinates.contDiff))
  have hbc : HasCompactSupport B := matrix_hasCompactSupport B (fun i j =>
    (hcH i j).comp_homeomorph boxCoordinates.toHomeomorph)
  have hbs : tsupport B⊆boxCoordinates ⁻¹' ((Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2)) := by
    apply matrix_tsupport_subset B
    intro i j
    exact (tsupport_comp_subset_preimage (H i j) boxCoordinates.continuous).trans (preimage_mono (hsH i j))
  have hcol (x : Coord3) (j : Fin 3) : (B x).col j=
      ![H 0 j (boxCoordinates x),H 1 j (boxCoordinates x),H 2 j (boxCoordinates x)] := by
    ext i; fin_cases i <;> rfl
  refine ⟨B,hB,hbc,hbs,?_,?_,?_,?_⟩
  · intro x
    ext i j
    exact hsy j i (boxCoordinates x)
  · intro φ hφ
    simp_rw [hcol]
    exact cube_weak_divergence_to_coordinates (hH 0 0) (hH 1 0) (hH 2 0)
      (hcH 0 0) (hcH 1 0) (hcH 2 0) hd₁ φ hφ
  · intro φ hφ
    simp_rw [hcol]
    exact cube_weak_divergence_to_coordinates (hH 0 1) (hH 1 1) (hH 2 1)
      (hcH 0 1) (hcH 1 1) (hcH 2 1) hd₂ φ hφ

  · intro x
    apply Matrix.norm_le_iff (mul_nonneg hL.le hM) |>.mpr
    intro i j
    exact hbH i j (boxCoordinates x)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPhysicalCorrectionBound
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma correctionBox_subset_closed {a b c d : Coord3}
    (hca : ∀ i,c i≤a i) (hbd : ∀ i,b i≤d i) :
    correctionBox a b⊆closedCorrectionBox c d := by
  intro x hx
  have h := mem_correctionBox.mp hx
  exact ⟨⟨⟨(hca 0).trans (h 0).1.le,(h 0).2.le.trans (hbd 0)⟩,
    ⟨(hca 1).trans (h 1).1.le,(h 1).2.le.trans (hbd 1)⟩⟩,
    ⟨(hca 2).trans (h 2).1.le,(h 2).2.le.trans (hbd 2)⟩⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_UniformPhysicalBoxCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

theorem uniform_physical_box_symmetric_correction_C0
    {I : Type*} (Xs : I → OpenPartialHomeomorph Coord3 Coord3)
    (hXs : ∀ i,ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs i) (Xs i).source)
    (hXis : ∀ i,ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs i).symm (Xs i).target)
    {a b c d : Coord3} (hab : ∀ i,a i<b i)
    (hca : ∀ i,c i<a i) (hbd : ∀ i,b i<d i)
    (hboxes : ∀ i,closedCorrectionBox c d⊆(Xs i).source)
    {P : ℝ} (hP : 0<P)
    (hmetric : ∀ i x,x∈closedCorrectionBox c d →
      9*|(fderiv ℝ (Xs i) x).det|⁻¹*‖operatorMatrix (fderiv ℝ (Xs i) x)‖*
        ‖operatorMatrix (fderiv ℝ (Xs i) x)‖≤P) :
    ∃ L : ℝ,0<L ∧ ∀ i (r₁ r₂ : Box3 → ℝ),
      ContDiff ℝ (↑(⊤:ℕ∞)) r₁ → ContDiff ℝ (↑(⊤:ℕ∞)) r₂ →
      HasCompactSupport r₁ → HasCompactSupport r₂ →
      tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      (∫ p,r₁ p)=0 → (∫ p,r₂ p)=0 →
      (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0 → ∀ M : ℝ,0≤M →
      UniformC1Bound r₁ M → UniformC1Bound r₂ M →
    ∃ H : Coord3 → Mat3,
      ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ HasCompactSupport H ∧ tsupport H⊆(Xs i).target ∧
      (∀ y,(H y).IsSymm) ∧
      (∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤:ℕ∞)) ψ →
        (∫ y,fderiv ℝ ψ y ((H y*gradientColumns (fderiv ℝ (coordinatePair∘(Xs i).symm) y)).col j))=
          -(∫ y,ψ y*localPiolaSource (Xs i) (fun x => ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j) y)) ∧
      (∀ y,‖H y‖≤L*M) := by
  obtain ⟨L,hL,solve⟩ := compact_coordinate_box_correction_C0 hab hca hbd
  refine ⟨P*L,mul_pos hP hL,?_⟩
  intro i r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  let X := Xs i
  have hX := hXs i
  have hXi := hXis i
  have hbox := hboxes i
  have hPi := fun (B : Coord3 → Mat3) (hB : Function.support B⊆closedCorrectionBox c d) (y : Coord3) =>
    localPiolaTensor_bound_of_coefficient X hP.le (hmetric i) B hB y

  obtain ⟨B,hB,hcB,htB,hsy,hw₁,hw₂,hbB⟩ :=
    solve r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  have hBs : tsupport B⊆X.source := htB.trans hbox
  have hinner : (Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2)⊆
      (Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2) := by
    intro p hp
    exact ⟨⟨⟨((hca 0).trans hp.1.1.1).le,(hp.1.1.2.trans (hbd 0)).le⟩,
      ⟨((hca 1).trans hp.1.2.1).le,(hp.1.2.2.trans (hbd 1)).le⟩⟩,
      ⟨((hca 2).trans hp.2.1).le,(hp.2.2.trans (hbd 2)).le⟩⟩
  let r : Fin 2 → Coord3 → ℝ := fun j x => ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j
  have hcr : ∀ j,HasCompactSupport (r j) := by
    intro j
    fin_cases j
    · exact hs₁.comp_homeomorph boxCoordinates.toHomeomorph
    · exact hs₂.comp_homeomorph boxCoordinates.toHomeomorph
  have hsr : ∀ j,tsupport (r j)⊆X.source := by
    intro j
    fin_cases j
    · exact ((tsupport_comp_subset_preimage r₁ boxCoordinates.continuous).trans
        (preimage_mono (hv₁.trans hinner))).trans hbox
    · exact ((tsupport_comp_subset_preimage r₂ boxCoordinates.continuous).trans
        (preimage_mono (hv₂.trans hinner))).trans hbox
  have hweak : ∀ j (φ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      (∫ x,fderiv ℝ φ x ((B x*gradientColumns (fderiv ℝ coordinatePair x)).col j))=
        -(∫ x,φ x*r j x) := by
    intro j φ hφ
    simp_rw [coordinatePair_columns]
    fin_cases j
    · exact hw₁ φ hφ
    · exact hw₂ φ hφ
  refine ⟨localPiolaTensor X B,localPiolaTensor_smooth X hX hXi B hB hcB hBs,
    (localPiolaTensor_compact X B hcB hBs).1,(localPiolaTensor_compact X B hcB hBs).2,
    localPiolaTensor_isSymm X B hsy,?_,?_⟩
  · intro j ψ hψ
    change (∫ y,fderiv ℝ ψ y ((localPiolaTensor X B y*gradientColumns (fderiv ℝ (coordinatePair∘X.symm) y)).col j))=_
    simp_rw [localPiolaTensor_columns X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) B coordinatePair
      (coordinatePair_smooth.differentiable (by simp)).differentiableOn]
    have htj := tensorColumn_tsupport B (fun x => gradientColumns (fderiv ℝ coordinatePair x)) j
    exact localPiolaFlux_weak_source volume X hX hXi _ _
      (hcB.of_isClosed_subset isClosed_closure htj) (hcr j) (htj.trans hBs) (hsr j) (hweak j) ψ hψ
  · intro y
    exact (hPi B ((subset_tsupport B).trans htB) y).trans
      ((mul_le_mul_of_nonneg_left (hbB _) hP.le).trans_eq (by ring))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_UniformLocalPhysicalCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem uniform_local_physical_symmetric_correction_C0
    {I : Type*} (Xs : I → OpenPartialHomeomorph Coord3 Coord3)
    (hXs : ∀ i,ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs i) (Xs i).source)
    (hXis : ∀ i,ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs i).symm (Xs i).target)
    {a b c d : Coord3} (hab : ∀ i,a i<b i)
    (hca : ∀ i,c i<a i) (hbd : ∀ i,b i<d i)
    (hboxes : ∀ i,closedCorrectionBox c d⊆(Xs i).source)
    {B : ℝ} (hB : 0<B)
    (hmetric : ∀ i x,x∈closedCorrectionBox c d →
      |inverseSourceWeight (Xs i) x|≤B ∧
      ‖fderiv ℝ (inverseSourceWeight (Xs i)) x‖≤B ∧ ‖fderiv ℝ (Xs i) x‖≤B ∧
      9*|(fderiv ℝ (Xs i) x).det|⁻¹*‖operatorMatrix (fderiv ℝ (Xs i) x)‖*
        ‖operatorMatrix (fderiv ℝ (Xs i) x)‖≤B)
    (us : I → Coord3 → Fin 2 → ℝ) (hus : ∀ i,ContDiff ℝ (↑(⊤:ℕ∞)) (us i))
    (hpot : ∀ i,EqOn (us i) (coordinatePair∘(Xs i).symm) (Xs i).target) :
    ∃ L : ℝ,0<L ∧ ∀ i (r : PhysicalSourcePair),
      CompactSmoothPair r → PairSupported r ((Xs i) '' correctionBox a b) →
      physicalSourceMoment (us i) r=0 → ∀ M : ℝ,0≤M →
      (∀ j,UniformC1Bound (r j) M) →
      BoundedPhysicallyCorrectable (us i) (Xs i).target r (L*M) := by
  have hiK := correctionBox_subset_closed (fun i => (hca i).le) (fun i => (hbd i).le)
  let P := B*(B+1)
  have hP : 0<P := by dsimp [P]; positivity
  obtain ⟨L,hL,solve⟩ := uniform_physical_box_symmetric_correction_C0 Xs hXs hXis hab hca hbd hboxes hB
    (fun i x hx => (hmetric i x hx).2.2.2)
  refine ⟨L*P,mul_pos hL hP,?_⟩
  intro i r hrc hs hm M hM hb
  have hr := fun j => (hrc j).1
  have hc := fun j => (hrc j).2
  have hz (j : Fin 2) : (∫ x,r j x)=0 := by
    fin_cases j
    · exact congrFun hm 0
    · exact congrFun hm 1
  have ht : (∫ x,us i x 1*r 0 x-us i x 0*r 1 x)=0 := congrFun hm 2
  let X := Xs i
  let u := us i
  have hX := hXs i
  have hXi := hXis i
  have huu := hus i
  have hu := hpot i
  have houter := hboxes i
  have hbox := hiK.trans houter
  have hPsolve := localPiolaSource_inverse_C1_of_bounds X hX hXi houter hB
    (fun x hx => ⟨(hmetric i x hx).1,(hmetric i x hx).2.1⟩)
    (fun x hx => (hmetric i x hx).2.2.1)

  let p : Fin 2 → Coord3 → ℝ := fun j => localPiolaSource X.symm (r j)
  have hst (j) : tsupport (r j)⊆X.target :=
    (hs j).trans (by rintro y ⟨x,hx,rfl⟩; exact X.map_source (hbox hx))
  have hp (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (p j) :=
    localPiolaSource_smooth X.symm hXi hX (r j) (hr j) (hc j) (hst j)
  have hpc (j) : HasCompactSupport (p j) :=
    (localPiolaSource_compact X.symm (r j) (hc j) (hst j)).1
  have hps (j) : tsupport (p j)⊆correctionBox a b :=
    localPiolaSource_inverse_support X (r j) (hc j) hbox (hs j)
  let q : Fin 2 → Box3 → ℝ := fun j => p j∘boxCoordinates.symm
  have hq (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (q j) := (hp j).comp boxCoordinates.symm.contDiff
  have hqc (j) : HasCompactSupport (q j) := (hpc j).comp_homeomorph boxCoordinates.symm.toHomeomorph
  have hqs (j) : tsupport (q j)⊆
      (Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) := by
    intro z hz
    have h := hps j ((tsupport_comp_subset_preimage (p j) boxCoordinates.symm.continuous) hz)
    simpa only [correctionBox,mem_preimage,boxCoordinates.apply_symm_apply] using h
  have hd := hX.differentiableOn (by simp)
  have hdi := hXi.differentiableOn (by simp)
  have hback (j) : localPiolaSource X (p j)=r j :=
    localPiolaSource_inverse X hd hdi (r j) ((subset_tsupport _).trans (hst j))
  have hqz (j) : (∫ z,q j z)=0 := by
    rw [←boxCoordinates_integral (q j)]
    simp only [q,Function.comp_apply,boxCoordinates.symm_apply_apply]
    have he := localPiolaSource_pairing volume X.symm hdi
      (fun _ hy => local_fderiv_det_ne_zero X.symm hdi hd hy) (r j)
      ((subset_tsupport _).trans (hst j)) (fun _ => 1)
    simpa only [one_mul] using he.trans (by simpa only [one_mul] using hz j)
  have hqt : (∫ z : Box3,z.1.2*q 0 z-z.1.1*q 1 z)=0 := by
    rw [←boxCoordinates_integral (fun z : Box3 => z.1.2*q 0 z-z.1.1*q 1 z)]
    have he := localPiolaSource_torque X hd hdi (p 0) (p 1)
      ((subset_tsupport _).trans ((hps 0).trans hbox))
      ((subset_tsupport _).trans ((hps 1).trans hbox))
    rw [hback 0,hback 1] at he
    simp only [q,Function.comp_apply,boxCoordinates.symm_apply_apply]
    change (∫ x,x 1*p 0 x-x 0*p 1 x)=0
    rw [←he]
    refine (integral_congr_ae ?_).trans ht
    filter_upwards [] with y
    by_cases hy : y∈X.target
    · rw [hu hy]; rfl
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hst 0 h)),
        image_eq_zero_of_notMem_tsupport (fun h => hy (hst 1 h)),mul_zero,mul_zero,mul_zero,mul_zero]
  have hpb (j) : UniformC1Bound (p j) (P*M) :=
    hPsolve (r j) (hr j) (hc j) ((hs j).trans (image_mono hiK)) M hM (hb j)
  have hqb (j) : UniformC1Bound (q j) (P*M) :=
    (hpb j).comp_linear ((hp j).differentiable (by simp)) (mul_nonneg hP.le hM)
      boxCoordinates.symm.toContinuousLinearMap boxCoordinates_symm_norm_le
  obtain ⟨H,hH,hHc,hHs,hsy,hweak,hHb⟩ := solve i (q 0) (q 1)
    (hq 0) (hq 1) (hqc 0) (hqc 1) (hqs 0) (hqs 1) (hqz 0) (hqz 1) hqt
    (P*M) (mul_nonneg hP.le hM) (hqb 0) (hqb 1)
  refine ⟨H,hH,hHc,hHs,hsy,?_,fun y => (hHb y).trans_eq (by ring)⟩
  apply symmetricSource_eq_of_weak huu hH hHc (fun j => ⟨hr j,hc j⟩)
  intro j ψ hψ
  have he := hweak j ψ hψ
  have hpsource : (fun x => ![q 0 (boxCoordinates x),q 1 (boxCoordinates x)] j)=p j := by
    funext x
    fin_cases j <;> simp [q]
  rw [hpsource,hback j] at he
  refine (integral_congr_ae ?_).trans he
  filter_upwards [] with y
  by_cases hy : y∈X.target
  · have hf : u =ᶠ[𝓝 y] coordinatePair∘X.symm :=
      Filter.eventuallyEq_of_mem (X.open_target.mem_nhds hy) (fun z hz => hu hz)
    rw [hf.fderiv_eq]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hHs h)),Matrix.zero_mul,Matrix.zero_mul]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricLocalRegularCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_uniform_local_regular_correction
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (p : P) {x : Coord3} (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    ∃ V : Set P,∃ W : Set Coord3,∃ L : ℝ,
      IsOpen V ∧ p∈V ∧ IsOpen W ∧ x∈W ∧ W⊆U ∧ Bornology.IsBounded W ∧ 0<L ∧
      ∀ q∈V,∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r W →
        physicalSourceMoment (fun y => u (q,y)) r=0 → ∀ M : ℝ,0≤M →
        (∀ j,UniformC1Bound (r j) M) →
        BoundedPhysicallyCorrectable (fun y => u (q,y)) U r (L*M) := by
  obtain ⟨Y,hpY,hYU,hY,hpot,hsm,hinv⟩ := exists_parametric_potential_coordinates hu p x hD
    (isOpen_univ.prod hU) ⟨mem_univ p,hx⟩
  let z := (Y (p,x)).2
  have hpz : (p,z)∈Y.target := by
    have he : (p,z)=Y (p,x) := Prod.ext (hY p x).symm rfl
    rw [he]
    exact Y.map_source hpY
  obtain ⟨V₀,W₀,hV₀,hW₀,hp₀,hz₀,hprod₀⟩ := exists_open_product_inside Y.open_target hpz
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hW₀ z hz₀
  let a : Coord3 := fun i => z i-ε/3
  let b : Coord3 := fun i => z i+ε/3
  let c : Coord3 := fun i => z i-2*ε/3
  let d : Coord3 := fun i => z i+2*ε/3
  have hc : closedCorrectionBox c d⊆W₀ := by
    intro y hy
    apply hball
    rw [Metric.mem_ball,dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq,abs_lt]
    have hi : c i≤y i ∧ y i≤d i := by
      fin_cases i
      · exact hy.1.1
      · exact hy.1.2
      · exact hy.2
    dsimp [c,d] at hi
    constructor <;> linarith
  have hab : ∀ i,a i<b i := fun i => by dsimp [a,b]; linarith
  have hca : ∀ i,c i<a i := fun i => by dsimp [c,a]; linarith
  have hbd : ∀ i,b i<d i := fun i => by dsimp [b,d]; linarith
  obtain ⟨δ,hδ,hδball⟩ := Metric.isOpen_iff.mp hV₀ p hp₀
  let Kp := Metric.closedBall p (δ/2)
  have hKp : IsCompact Kp := isCompact_closedBall _ _
  have hpK : Kp⊆V₀ := fun q hq => hδball
    (lt_of_le_of_lt hq (by linarith : δ/2<δ))
  have hjoint : Kp×ˢclosedCorrectionBox c d⊆Y.target :=
    fun q hq => hprod₀ ⟨hpK hq.1,hc hq.2⟩
  obtain ⟨B,hB,hbound⟩ := parametric_chart_compact_bounds Y hY hsm hinv
    (hKp.prod (closedCorrectionBox_compact c d)) hjoint
  let O : Set (P×Coord3) := Y.source∩{q | (Y q).2∈correctionBox a b}
  have hO : IsOpen O := Y.open_source.inter
    ((correctionBox_isOpen a b).preimage (continuous_snd.comp hsm.continuous))
  have hpxO : (p,x)∈O := ⟨hpY,mem_correctionBox.mpr (fun i => by dsimp [a,b,z]; constructor <;> linarith)⟩
  obtain ⟨V₁,W₁,hV₁,hW₁,hp₁,hx₁,hprod₁⟩ := exists_open_product_inside hO hpxO
  let V := Metric.ball p (δ/2)∩V₁
  let W := W₁∩Metric.ball x 1
  have hVp : p∈V := ⟨Metric.mem_ball_self (by positivity),hp₁⟩
  have hWx : x∈W := ⟨hx₁,Metric.mem_ball_self zero_lt_one⟩
  have hWU : W⊆U := fun y hy => (hYU (hprod₁ (show (p,y)∈V₁×ˢW₁ from ⟨hp₁,hy.1⟩)).1).2
  let Xs : V → OpenPartialHomeomorph Coord3 Coord3 := fun q => (fiberSlice Y hY q.1).symm
  have hXs (q : V) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs q) (Xs q).source :=
    (fiberSlice_smooth Y hY hsm hinv q.1).2
  have hXis (q : V) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (Xs q).symm (Xs q).target :=
    (fiberSlice_smooth Y hY hsm hinv q.1).1.contDiffOn
  have hboxes (q : V) : closedCorrectionBox c d⊆(Xs q).source :=
    fun y hy => hjoint ⟨Metric.ball_subset_closedBall q.2.1,hy⟩
  let us : V → Coord3 → Fin 2 → ℝ := fun q y => u (q.1,y)
  have hus (q : V) : ContDiff ℝ (↑(⊤:ℕ∞)) (us q) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hpot' (q : V) : EqOn (us q) (coordinatePair∘(Xs q).symm) (Xs q).target :=
    fun y _ => (hpot q.1 y).symm
  obtain ⟨L,hL,solve⟩ := uniform_local_physical_symmetric_correction_C0 Xs hXs hXis hab hca hbd hboxes hB
    (fun q y hy => hbound (q.1,y) ⟨Metric.ball_subset_closedBall q.2.1,hy⟩) us hus hpot'
  refine ⟨V,W,L,Metric.isOpen_ball.inter hV₁,hVp,hW₁.inter Metric.isOpen_ball,hWx,hWU,
    Metric.isBounded_ball.subset inter_subset_right,hL,?_⟩
  intro q hq r hr hs hm M hM hb
  let i : V := ⟨q,hq⟩
  have hWbox : W⊆(Xs i) '' correctionBox a b := by
    intro y hy
    have hh := hprod₁ (show (q,y)∈V₁×ˢW₁ from ⟨hq.2,hy.1⟩)
    refine ⟨(Y (q,y)).2,hh.2,?_⟩
    exact (fiberSlice Y hY q).left_inv hh.1
  have hXt : (Xs i).target⊆U := fun y hy => (hYU hy).2
  exact (solve i r hr (fun j => (hs j).trans hWbox) hm M hM hb).region_mono hXt

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ParametricCorrectionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma exists_parametric_correction_box
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {U : Set Coord3} (hU : IsOpen U) {x : Coord3} (hx : x∈U)
    (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) :
    ∃ B : ParametricCorrectionBox u p U,x∈B.region := by
  obtain ⟨V,W,L,hV,hp,hW,hxW,hWU,hWb,hL,solve⟩ :=
    exists_uniform_local_regular_correction hu p hD hU hx
  refine ⟨⟨W,hW,⟨x,hxW⟩,hWU,hWb,L,hL,?_⟩,hxW⟩
  exact Filter.eventually_of_mem (hV.mem_nhds hp) solve

lemma parametric_correction_boxes_cover
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) :
    (⋃ B : ParametricCorrectionBox u p U,B.region)=U := by
  apply Subset.antisymm
  · exact iUnion_subset fun B => B.region_subset
  · intro x hx
    obtain ⟨B,hB⟩ := exists_parametric_correction_box hu p hU hx (hD x hx)
    exact mem_iUnion.mpr ⟨B,hB⟩

lemma parametric_correction_boxes_chain
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    (B C : ParametricCorrectionBox u p U) :
    Relation.TransGen (fun B C : ParametricCorrectionBox u p U => (B.region∩C.region).Nonempty) B C := by
  have hc : IsPreconnected (⋃ B : ParametricCorrectionBox u p U,B.region) := by
    rwa [parametric_correction_boxes_cover hu p hU hD]
  exact hc.transGen_of_iUnion (fun B => B.region_open) B C B.region_nonempty C.region_nonempty

theorem parametric_controlled_source_transport
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    (B C : ParametricCorrectionBox u p U) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ t in 𝓝 p,∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r B.region →
      ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      ∃ q : PhysicalSourcePair,CompactSmoothPair q ∧ PairSupported q C.region ∧
        physicalSourceMoment (fun x => u (t,x)) q=physicalSourceMoment (fun x => u (t,x)) r ∧
        (∀ j,UniformC1Bound (q j) (L*M)) ∧
        BoundedPhysicallyCorrectable (fun x => u (t,x)) U (r-q) (L*M) := by
  have hp := parametric_correction_boxes_chain hu p hU hUc hD B C
  induction hp with
  | single h => exact B.bounded_transfer hu p hD _ h
  | @tail C D hpath hCD ih =>
    obtain ⟨L,hL,hsolve⟩ := ih
    obtain ⟨R,hR,hstep⟩ := C.bounded_transfer hu p hD D hCD
    refine ⟨L+R*L,by positivity,?_⟩
    filter_upwards [hsolve,hstep] with t solve step
    intro r hr hs M hM hb
    obtain ⟨q,hq,hqs,hqm,hqb,hqc⟩ := solve r hr hs M hM hb
    obtain ⟨s,hss,hssup,hsm,hsb,hsc⟩ := step q hq hqs (L*M) (mul_nonneg hL.le hM) hqb
    refine ⟨s,hss,hssup,hsm.trans hqm,fun j => (hsb j).mono ?_,?_⟩
    · nlinarith [mul_nonneg hL.le hM]
    · have hut : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (t,x)) :=
        hu.comp (contDiff_const.prodMk contDiff_id)
      have he := hqc.add hut hsc
      rw [sub_add_sub_cancel] at he
      exact he.mono (by ring_nf; rfl)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderSlopeGreen
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def cylinderEndJet (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (r R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) : FiniteCylinderJets R :=
  endPoissonJet s hs R hR f+cylinderSlopeJet r R

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallTensor
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wallCoordinatePair_derivative {v : Box3 → ℝ}
    (hv : Differentiable ℝ v) (x w : Coord3) :
    fderiv ℝ (wallCoordinatePair v) x w=![w 0,fderiv ℝ v (boxCoordinates x) (boxCoordinates w)] := by
  have hd : DifferentiableAt ℝ (wallCoordinatePair v) x := by
    apply differentiableAt_pi.mpr
    intro j
    fin_cases j
    · exact differentiableAt_apply (0 : Fin 3) x
    · exact (hv _).comp x boxCoordinates.differentiableAt
  ext j
  fin_cases j
  · have hh := congrArg (fun D : Coord3 →L[ℝ] ℝ => D w) (fderiv_apply hd (0 : Fin 2))
    change fderiv ℝ (fun x : Coord3 => x 0) x w=fderiv ℝ (wallCoordinatePair v) x w 0 at hh
    have hp : fderiv ℝ (fun x : Coord3 => x 0) x=ContinuousLinearMap.proj (0 : Fin 3) :=
      (ContinuousLinearMap.proj (0 : Fin 3) : Coord3 →L[ℝ] ℝ).hasFDerivAt.fderiv
    rw [hp] at hh
    exact hh.symm
  · have hh := congrArg (fun D : Coord3 →L[ℝ] ℝ => D w) (fderiv_apply hd (1 : Fin 2))
    change fderiv ℝ (v∘boxCoordinates) x w=fderiv ℝ (wallCoordinatePair v) x w 1 at hh
    exact hh.symm.trans (boxCoordinates_fderiv v hv x w)

lemma wallMatrix_columns {v : Box3 → ℝ} (hv : Differentiable ℝ v)
    (A B : Box3 → ℝ) (x : Coord3) :
    (wallMatrix A B x*gradientColumns (fderiv ℝ (wallCoordinatePair v) x)).col 0=
      ![0,0,A (boxCoordinates x)] ∧
    (wallMatrix A B x*gradientColumns (fderiv ℝ (wallCoordinatePair v) x)).col 1=
      ![A (boxCoordinates x)*wallDerivative v (boxCoordinates x),0,
        A (boxCoordinates x)*wallAlong (1,0) v (boxCoordinates x)+
        B (boxCoordinates x)*wallDerivative v (boxCoordinates x)] := by
  have he (i : Fin 3) : gradientColumns (fderiv ℝ (wallCoordinatePair v) x) i 0=
      (Pi.single i (1:ℝ) : Coord3) 0 := by
    change fderiv ℝ (wallCoordinatePair v) x (Pi.single i 1) 0=_
    rw [wallCoordinatePair_derivative hv]
    rfl
  have he' (i : Fin 3) : gradientColumns (fderiv ℝ (wallCoordinatePair v) x) i 1=
      fderiv ℝ v (boxCoordinates x) (boxCoordinates (Pi.single i 1)) := by
    change fderiv ℝ (wallCoordinatePair v) x (Pi.single i 1) 1=_
    rw [wallCoordinatePair_derivative hv]
    rfl
  constructor
  · ext i
    change (∑ k,wallMatrix A B x i k*gradientColumns (fderiv ℝ (wallCoordinatePair v) x) k 0)=_
    fin_cases i <;> simp [he,wallMatrix,Pi.single_apply]
  · ext i
    change (∑ k,wallMatrix A B x i k*gradientColumns (fderiv ℝ (wallCoordinatePair v) x) k 1)=_
    fin_cases i <;> simp [Fin.sum_univ_three,he',wallMatrix,
      boxCoordinates_apply,Pi.single_apply,wallDerivative,wallAlong]
    all_goals exact Or.inl rfl

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma coordinateDivergence_wallFlux {f g : Box3 → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Coord3) :
    coordinateDivergence (fun y => ![f (boxCoordinates y),0,g (boxCoordinates y)]) x=
      wallAlong (1,0) f (boxCoordinates x)+wallDerivative g (boxCoordinates x) := by
  have he : coordinateDivergence (fun y => ![f (boxCoordinates y),0,g (boxCoordinates y)]) x=
      fderiv ℝ (f∘boxCoordinates) x (Pi.single 0 1)+
      fderiv ℝ (g∘boxCoordinates) x (Pi.single 2 1) := by
    simp [coordinateDivergence,Fin.sum_univ_three,Function.comp_def]
  rw [he,boxCoordinates_fderiv f hf,boxCoordinates_fderiv g hg]
  rfl

lemma wallMatrix_sources {A B v : Box3 → ℝ}
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (x : Coord3) :
    symmetricSource (wallMatrix A B) (wallCoordinatePair v) 0 x=wallDerivative A (boxCoordinates x) ∧
    symmetricSource (wallMatrix A B) (wallCoordinatePair v) 1 x=
      wallAlong (1,0) (fun p => A p*wallDerivative v p) (boxCoordinates x)+
        wallDerivative (fun p => A p*wallAlong (1,0) v p+B p*wallDerivative v p) (boxCoordinates x) := by
  have he₀ : (fun y => (wallMatrix A B y*gradientColumns (fderiv ℝ (wallCoordinatePair v) y)).col 0)=
      (fun y => ![0,0,A (boxCoordinates y)]) := funext (fun y => (wallMatrix_columns (hv.differentiable (by simp)) A B y).1)
  have he₁ : (fun y => (wallMatrix A B y*gradientColumns (fderiv ℝ (wallCoordinatePair v) y)).col 1)=
      (fun y => ![A (boxCoordinates y)*wallDerivative v (boxCoordinates y),0,
        A (boxCoordinates y)*wallAlong (1,0) v (boxCoordinates y)+B (boxCoordinates y)*wallDerivative v (boxCoordinates y)]) :=
    funext (fun y => (wallMatrix_columns (hv.differentiable (by simp)) A B y).2)
  constructor
  · unfold symmetricSource
    rw [he₀,coordinateDivergence_wallFlux (differentiable_const 0) (hA.differentiable (by simp))]
    simp [wallAlong]
  · unfold symmetricSource
    rw [he₁]
    exact coordinateDivergence_wallFlux
      ((hA.mul (wallDerivative_smooth hv)).differentiable (by simp))
      (((hA.mul (wallAlong_smooth (1,0) hv)).add (hB.mul (wallDerivative_smooth hv))).differentiable (by simp)) x

theorem wallParticularTensor_source_eq {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    (x : Coord3) (hx : χ =ᶠ[𝓝 (boxCoordinates x)] (fun _ => 1)) :
    symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) 0 x=r₁ (boxCoordinates x) ∧
    symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) 1 x=r₂ (boxCoordinates x) := by
  let p := boxCoordinates x
  let A := fun q => χ q*wallPrimitive r₁ q
  let B := fun q => χ q*(wallQuotient (wallParticularNumerator (1,0) v r₁ r₂) q/wallQuotient (wallDerivative v) q)
  have hA := hχ.mul (wallPrimitive_smooth h₁)
  have hB := smooth_wall_cutoff_ratio hχ (wallParticularNumerator_smooth (1,0) hv h₁ h₂) (wallDerivative_smooth hv) hne
  have hxe : χ p=1 := hx.eq_of_nhds
  have hp : p∈tsupport χ := subset_tsupport χ (by change χ p≠0; rw [hxe]; norm_num)
  have hqn : ∀ᶠ q in 𝓝 p,wallQuotient (wallDerivative v) q≠0 :=
    (wallQuotient_smooth (wallDerivative_smooth hv)).continuous.continuousAt.eventually_ne (hne p hp)
  have hAe : A =ᶠ[𝓝 p] wallPrimitive r₁ := hx.mono (fun q hq => by dsimp [A]; rw [hq,one_mul])
  have hFe : (fun q => A q*wallDerivative v q) =ᶠ[𝓝 p]
      (fun q => wallPrimitive r₁ q*wallDerivative v q) := hAe.mono (fun q hq => by dsimp only; rw [hq])
  have hGe : (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) =ᶠ[𝓝 p]
      (fun q => wallPrimitive r₁ q*wallAlong (1,0) v q+wallParticularNumerator (1,0) v r₁ r₂ q) := by
    filter_upwards [hx,hqn] with q hq hqn
    dsimp [A,B]
    rw [hq,one_mul,one_mul,wall_ratio_multiply (wallParticularNumerator_smooth (1,0) hv h₁ h₂)
      (wallDerivative_smooth hv) (wallParticularNumerator_zero (1,0) v r₁ r₂) hz q hqn]
  have hsource := wallMatrix_sources hA hB hv x
  change symmetricSource (wallMatrix A B) (wallCoordinatePair v) 0 x=_ ∧
    symmetricSource (wallMatrix A B) (wallCoordinatePair v) 1 x=_
  rw [hsource.1,hsource.2]
  change wallDerivative A p=r₁ p ∧ _=r₂ p
  refine ⟨?_,?_⟩
  · change fderiv ℝ A p (0,1)=r₁ p
    rw [hAe.fderiv_eq]
    exact wallDerivative_primitive h₁ p
  · change fderiv ℝ (fun q => A q*wallDerivative v q) p ((1,0),0)+
      fderiv ℝ (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p (0,1)=r₂ p
    rw [hFe.fderiv_eq,hGe.fderiv_eq]
    exact (wall_particular_flux_equations (1,0) hv h₁ h₂ p).2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallHomogeneous
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem wallHomogeneousTensor_source_eq {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    (x : Coord3) (hx : χ =ᶠ[𝓝 (boxCoordinates x)] (fun _ => 1)) :
    symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) 0 x=0 ∧
    symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) 1 x=0 := by
  let p := boxCoordinates x
  let A := fun q => χ q*(fun q : Box3 => a q.1) q
  let B := fun q => χ q*(wallQuotient (wallHomogeneousNumerator (1,0) v a) q/wallQuotient (wallDerivative v) q)
  have hA := hχ.mul ((ha.comp contDiff_fst))
  have hB := smooth_wall_cutoff_ratio hχ (wallHomogeneousNumerator_smooth (1,0) hv ha) (wallDerivative_smooth hv) hne
  have hxe : χ p=1 := hx.eq_of_nhds
  have hp : p∈tsupport χ := subset_tsupport χ (by change χ p≠0; rw [hxe]; norm_num)
  have hqn : ∀ᶠ q in 𝓝 p,wallQuotient (wallDerivative v) q≠0 :=
    (wallQuotient_smooth (wallDerivative_smooth hv)).continuous.continuousAt.eventually_ne (hne p hp)
  have hAe : A =ᶠ[𝓝 p] (fun q : Box3 => a q.1) := hx.mono (fun q hq => by dsimp [A]; rw [hq,one_mul])
  have hFe : (fun q => A q*wallDerivative v q) =ᶠ[𝓝 p]
      (fun q => (fun q : Box3 => a q.1) q*wallDerivative v q) := hAe.mono (fun q hq => by dsimp only; rw [hq])
  have hGe : (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) =ᶠ[𝓝 p]
      (fun q => (fun q : Box3 => a q.1) q*wallAlong (1,0) v q+wallHomogeneousNumerator (1,0) v a q) := by
    filter_upwards [hx,hqn] with q hq hqn
    dsimp [A,B]
    rw [hq,one_mul,one_mul,wall_ratio_multiply (wallHomogeneousNumerator_smooth (1,0) hv ha)
      (wallDerivative_smooth hv) (wallHomogeneousNumerator_zero (1,0) v a) hz q hqn]
  change ContDiff ℝ (↑(⊤ : ℕ∞)) A at hA
  change ContDiff ℝ (↑(⊤ : ℕ∞)) B at hB
  have hsource := wallMatrix_sources hA hB hv x
  change symmetricSource (wallMatrix A B) (wallCoordinatePair v) 0 x=_ ∧
    symmetricSource (wallMatrix A B) (wallCoordinatePair v) 1 x=_
  rw [hsource.1,hsource.2]
  change wallDerivative A p=0 ∧ _=0
  refine ⟨?_,?_⟩
  · change fderiv ℝ A p (0,1)=0
    rw [hAe.fderiv_eq]
    exact wallDerivative_pullback (ha.differentiable (by simp)) p
  · change fderiv ℝ (fun q => A q*wallDerivative v q) p ((1,0),0)+
      fderiv ℝ (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p (0,1)=0
    rw [hFe.fderiv_eq,hGe.fderiv_eq]
    exact (wall_homogeneous_flux_equations (1,0) hv ha p).2

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology

theorem wallHomogeneousTensor_transfers {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    (hcut : ∀ q,χ (q,0)*a q=a q) :
    let H := wallHomogeneousTensor χ v a
    let u := wallCoordinatePair v
    let r := fun (j : Fin 2) (p : Box3) => symmetricSource H u j (boxCoordinates.symm p)
    let U := (Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ)
    (∫ p in U,r 0 p)= -(∫ q : ℝ×ℝ,a q) ∧
    (∫ p in U,r 1 p)= -(∫ q : ℝ×ℝ,a q*wallAlong (1,0) v (q,0)) ∧
    (∫ p in U,v p*r 0 p-p.1.1*r 1 p)=
      -(∫ q : ℝ×ℝ,a q*(v (q,0)-q.1*wallAlong (1,0) v (q,0))) := by
  dsimp only
  let A := fun p => χ p*a p.1
  let B := fun p => χ p*(wallQuotient (wallHomogeneousNumerator (1,0) v a) p/wallQuotient (wallDerivative v) p)
  have hA := hχ.mul (ha.comp contDiff_fst)
  have hB := smooth_wall_cutoff_ratio hχ (wallHomogeneousNumerator_smooth (1,0) hv ha) (wallDerivative_smooth hv) hne
  change ContDiff ℝ (↑(⊤ : ℕ∞)) A at hA
  change ContDiff ℝ (↑(⊤ : ℕ∞)) B at hB
  have he₀ (p : Box3) : symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) 0
        (boxCoordinates.symm p)=wallDerivative A p := by
    simpa only [boxCoordinates.apply_symm_apply,wallHomogeneousTensor,A,B] using (wallMatrix_sources hA hB hv (boxCoordinates.symm p)).1
  have he₁ (p : Box3) : symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) 1
        (boxCoordinates.symm p)=wallAlong (1,0) (fun q => A q*wallDerivative v q) p+
      wallDerivative (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p := by
    simpa only [boxCoordinates.apply_symm_apply,wallHomogeneousTensor,A,B] using (wallMatrix_sources hA hB hv (boxCoordinates.symm p)).2
  simp_rw [he₀,he₁]
  have hh := wall_matrix_halfspace_moments hA hB hs.mul_right hs.mul_right hv hz
  simpa only [A,hcut] using hh

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWall
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

lemma wallHomogeneousTensor_source_off_one {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    {x : Coord3} (hx : χ =ᶠ[𝓝 (boxCoordinates x)] (fun _ => 1)) (j : Fin 2) :
    x∉tsupport (symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) j) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have hloc : ∀ᶠ y in 𝓝 (boxCoordinates x),χ =ᶠ[𝓝 y] (fun _ => 1) := hx.eventually_nhds
  have hp : ∀ᶠ y in 𝓝 x,χ =ᶠ[𝓝 (boxCoordinates y)] (fun _ => 1) :=
    boxCoordinates.continuous.continuousAt.eventually hloc
  filter_upwards [hp] with y hy
  have he := wallHomogeneousTensor_source_eq hχ hv ha hz hne y hy
  fin_cases j
  · exact he.1
  · exact he.2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallResidual
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

lemma wallParticularResidual_off_one {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    {x : Coord3} (hx : χ =ᶠ[𝓝 (boxCoordinates x)] (fun _ => 1)) (j : Fin 2) :
    x∉tsupport (wallParticularResidual χ v r₁ r₂ j) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have hp : ∀ᶠ y in 𝓝 x,χ =ᶠ[𝓝 (boxCoordinates y)] (fun _ => 1) :=
    boxCoordinates.continuous.continuousAt.eventually hx.eventually_nhds
  filter_upwards [hp] with y hy
  have he := wallParticularTensor_source_eq hχ hv h₁ h₂ hz hne y hy
  fin_cases j
  · change r₁ (boxCoordinates y)-symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) 0 y=0
    rw [he.1,sub_self]
  · change r₂ (boxCoordinates y)-symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) 1 y=0
    rw [he.2,sub_self]

theorem exists_uniform_particular_residual_gap {χ : Box3 → ℝ}
    {K : Set (ℝ×ℝ)} {S : Set Box3}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hsχ : HasCompactSupport χ)
    (hK : IsClosed K) (hS : IsCompact S)
    (hcore : ∀ q∈K,χ =ᶠ[𝓝 (q,0)] (fun _ => 1)) :
    ∃ δ : ℝ,0<δ ∧ ∀ (v r₁ r₂ : Box3 → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) v → ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ →
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ → (∀ q,wallDerivative v (q,0)=0) →
      (∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) →
      tsupport r₁⊆S∩Prod.fst ⁻¹' K → tsupport r₂⊆S∩Prod.fst ⁻¹' K →
      ∀ (j : Fin 2) (x : Coord3),x∈tsupport (wallParticularResidual χ v r₁ r₂ j) →
        δ≤|(boxCoordinates x).2| := by
  let O : Set Box3 := {p | χ =ᶠ[𝓝 p] (fun _ => 1)}
  have ho : IsOpen O := isOpen_iff_mem_nhds.mpr (fun p hp => hp.eventually_nhds)
  let T : Set Box3 := ((S∪tsupport χ)∩Prod.fst ⁻¹' K)∩Oᶜ
  have hT : IsCompact T :=
    ((hS.union hsχ).inter_right (hK.preimage continuous_fst)).inter_right ho.isClosed_compl
  have hn (p : Box3) (hp : p∈T) : p.2≠0 := by
    intro hz
    have he : p=(p.1,0) := Prod.ext rfl hz
    have hon : χ =ᶠ[𝓝 p] (fun _ => 1) := by
      rw [he]
      exact hcore p.1 hp.1.2
    exact hp.2 hon
  obtain ⟨δ,hδ,hlo⟩ := hT.exists_forall_le' continuous_snd.abs.continuousOn
    (fun p hp => abs_pos.mpr (hn p hp))
  refine ⟨δ,hδ,?_⟩
  intro v r₁ r₂ hv h₁ h₂ hz hne hr₁ hr₂ j x hx
  have hr (j : Fin 2) : tsupport (fun x : Coord3 => ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j)⊆
      boxCoordinates ⁻¹' (S∩Prod.fst ⁻¹' K) := by
    fin_cases j
    · exact (tsupport_comp_subset_preimage r₁ boxCoordinates.continuous).trans (preimage_mono hr₁)
    · exact (tsupport_comp_subset_preimage r₂ boxCoordinates.continuous).trans (preimage_mono hr₂)
  have hH := (wallParticularTensor_compact hsχ (v:=v) (r₁:=r₁) (r₂:=r₂)).2
  have hHK := wallParticularTensor_tsupport_surface hK
    (hr₁.trans inter_subset_right) (hr₂.trans inter_subset_right) (χ:=χ) (v:=v)
  have hres := tsupport_sub (fun x : Coord3 => ![r₁ (boxCoordinates x),r₂ (boxCoordinates x)] j)
    (symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) j) hx
  apply hlo
  refine ⟨?_,?_⟩
  · rcases hres with h | h
    · have h := hr j h
      exact ⟨Or.inl h.1,h.2⟩
    · have h := symmetricSource_tsupport _ _ j h
      exact ⟨Or.inr (hH h),hHK h⟩
  · intro hc
    exact wallParticularResidual_off_one hχ hv h₁ h₂ hz hne hc j hx

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_ParametricWallTensors
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology

lemma wallCoordinatePair_surjective {v : Box3 → ℝ} (hv : Differentiable ℝ v)
    {x : Coord3} (hne : wallDerivative v (boxCoordinates x)≠0) :
    Function.Surjective (fderiv ℝ (wallCoordinatePair v) x) := by
  intro b
  let c := (b 1-wallAlong (1,0) v (boxCoordinates x)*b 0)/wallDerivative v (boxCoordinates x)
  refine ⟨![b 0,0,c],?_⟩
  rw [wallCoordinatePair_derivative hv]
  have he : boxCoordinates ![b 0,0,c]=
      b 0 • (((1:ℝ),0),0)+c • (((0:ℝ),0),1) := by
    ext <;> simp [boxCoordinates_apply]
  rw [he,map_add,map_smul,map_smul]
  ext j
  fin_cases j
  · rfl
  · change b 0*wallAlong (1,0) v (boxCoordinates x)+c*wallDerivative v (boxCoordinates x)=b 1
    dsimp [c]
    field_simp
    ring

lemma wallCoordinatePair_surjective_off_wall {v : Box3 → ℝ}
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (hz : ∀ q,wallDerivative v (q,0)=0)
    {x : Coord3} (hx : (boxCoordinates x).2≠0)
    (hne : wallQuotient (wallDerivative v) (boxCoordinates x)≠0) :
    Function.Surjective (fderiv ℝ (wallCoordinatePair v) x) := by
  apply wallCoordinatePair_surjective (hv.differentiable (by simp))
  rw [(smooth_wall_division (wallDerivative_smooth hv) hz).2 (boxCoordinates x)]
  exact mul_ne_zero hx hne

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallSideMoments
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology

lemma wallPositivePair_moment {v : Box3 → ℝ} {r : PhysicalSourcePair} {δ : ℝ}
    (hδ : 0<δ) (hs : ∀ j x,x∈tsupport (r j) → δ≤|x 2|) :
    physicalSourceMoment (wallCoordinatePair v) (fun j => wallPositiveCut δ (r j))=
      ![∫ p in (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ),r 0 (boxCoordinates.symm p),
        ∫ p in (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ),r 1 (boxCoordinates.symm p),
        ∫ p in (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ),
          v p*r 0 (boxCoordinates.symm p)-p.1.1*r 1 (boxCoordinates.symm p)] := by
  have hcut (j) := wallPositiveCut_indicator hδ (hs j)
  have hS : MeasurableSet {x : Coord3 | 0<x 2} :=
    (isOpen_lt continuous_const (continuous_apply 2)).measurableSet
  have he : (fun x => wallCoordinatePair v x 1*wallPositiveCut δ (r 0) x-
      wallCoordinatePair v x 0*wallPositiveCut δ (r 1) x)=
      {x : Coord3 | 0<x 2}.indicator (fun x => wallCoordinatePair v x 1*r 0 x-
        wallCoordinatePair v x 0*r 1 x) := by
    funext x
    rw [hcut 0,hcut 1]
    by_cases hx : 0<x 2
    · simp only [indicator_of_mem (show x∈{x : Coord3 | 0<x 2} from hx)]
    · simp only [indicator_of_notMem (show x∉{x : Coord3 | 0<x 2} from hx),mul_zero,sub_zero]
  ext i
  fin_cases i
  · change (∫ x,wallPositiveCut δ (r 0) x)=_
    rw [hcut 0,integral_indicator hS,boxCoordinates_positive_integral]
    rfl
  · change (∫ x,wallPositiveCut δ (r 1) x)=_
    rw [hcut 1,integral_indicator hS,boxCoordinates_positive_integral]
    rfl
  · change (∫ x,wallCoordinatePair v x 1*wallPositiveCut δ (r 0) x-
      wallCoordinatePair v x 0*wallPositiveCut δ (r 1) x)=_
    rw [he,integral_indicator hS,boxCoordinates_positive_integral]
    simp only [wallCoordinatePair,Matrix.cons_val_zero,Matrix.cons_val_one,boxCoordinates.apply_symm_apply]
    rfl

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wallPositiveSource_moment {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ} {δ : ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    (hcut : ∀ q,χ (q,0)*a q=a q) (hδ : 0<δ)
    (hgap : ∀ j x,x∈tsupport (symmetricSource (wallHomogeneousTensor χ v a)
      (wallCoordinatePair v) j) → δ≤|x 2|) :
    physicalSourceMoment (wallCoordinatePair v)
      (fun j => wallPositiveCut δ (symmetricSource (wallHomogeneousTensor χ v a)
        (wallCoordinatePair v) j))=
      fun i => -(∫ q,a q*wallActualMoment v q i) := by
  rw [wallPositivePair_moment hδ hgap]
  have hh := wallHomogeneousTensor_transfers hχ hχc hv ha hz hne hcut
  ext i
  fin_cases i
  · simpa [wallActualMoment] using hh.1
  · exact hh.2.1
  · exact hh.2.2

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_CriticalWallGap
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

theorem exists_uniform_wall_source_gap {χ : Box3 → ℝ} {K : Set (ℝ×ℝ)}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hsχ : HasCompactSupport χ)
    (hK : IsClosed K) (hcore : ∀ q∈K,χ =ᶠ[𝓝 (q,0)] (fun _ => 1)) :
    ∃ δ : ℝ,0<δ ∧ ∀ (v : Box3 → ℝ) (a : (ℝ×ℝ) → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) v → ContDiff ℝ (↑(⊤ : ℕ∞)) a →
      (∀ q,wallDerivative v (q,0)=0) →
      (∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) →
      tsupport a⊆K → ∀ (j : Fin 2) (x : Coord3),
        x∈tsupport (symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) j) →
        δ≤|(boxCoordinates x).2| := by
  let O : Set Box3 := {p | χ =ᶠ[𝓝 p] (fun _ => 1)}
  have ho : IsOpen O := isOpen_iff_mem_nhds.mpr (fun p hp => hp.eventually_nhds)
  let S : Set Box3 := (tsupport χ∩Prod.fst ⁻¹' K)∩Oᶜ
  have hS : IsCompact S :=
    (hsχ.inter_right (hK.preimage continuous_fst)).inter_right ho.isClosed_compl
  have hn (p : Box3) (hp : p∈S) : p.2≠0 := by
    intro hz
    have he : p=(p.1,0) := Prod.ext rfl hz
    have hon : χ =ᶠ[𝓝 p] (fun _ => 1) := by
      rw [he]
      exact hcore p.1 hp.1.2
    exact hp.2 hon
  obtain ⟨δ,hδ,hlo⟩ := hS.exists_forall_le' (continuous_snd.abs.continuousOn)
    (fun p hp => abs_pos.mpr (hn p hp))
  refine ⟨δ,hδ,?_⟩
  intro v a hv ha hz hne haK j x hx
  apply hlo
  have hxH := symmetricSource_tsupport _ _ j hx
  refine ⟨⟨(wallHomogeneousTensor_compact hsχ).2 hxH,
    haK (wallHomogeneousTensor_tsupport_surface hv ha hxH)⟩,?_⟩
  intro hone
  exact wallHomogeneousTensor_source_off_one hχ hv ha hz hne hone j hx

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricGlobalCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem parametric_source_finite_split
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U) :
    ∃ (s : Finset (ParametricCorrectionBox u p U)) (ρ : s → Coord3 → ℝ) (C : s → ℝ),
      (∀ i,0<C i) ∧ ∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r K →
      ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      let p : s → PhysicalSourcePair := fun i j x => ρ i x*r j x
      (∀ i,CompactSmoothPair (p i)) ∧ (∀ i,PairSupported (p i) i.val.region) ∧
      (∑ i,p i)=r ∧ ∀ i j,UniformC1Bound (p i j) (C i*M) := by
  classical
  have hcov : K⊆⋃ B : ParametricCorrectionBox u p U,B.region := by
    rwa [parametric_correction_boxes_cover hu p hU hD]
  obtain ⟨s,hsc⟩ := hK.elim_finite_subcover (fun B : ParametricCorrectionBox u p U => B.region)
    (fun B => B.region_open) hcov
  have hsc' : K⊆⋃ B : s,B.val.region := by
    intro x hx
    obtain ⟨B,hB,hxB⟩ := mem_iUnion₂.mp (hsc hx)
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hxB⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ Coord3) hK.isClosed (fun B : s => B.val.region)
    (fun B => B.val.region_open) hsc'
  have hsρ (i : s) : HasCompactSupport (ρ i) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _,i.val.region_bounded.subset (hρ i)⟩
  choose C hC hbC using fun i : s => exists_uniformC1Bound (ρ i).contMDiff.contDiff (hsρ i)
  refine ⟨s,fun i => ρ i,fun i => 2*C i,fun i => mul_pos (by norm_num) (hC i),?_⟩
  intro r hr hs M hM hb
  dsimp only
  refine ⟨fun i j => ⟨(ρ i).contMDiff.contDiff.mul (hr j).1,(hr j).2.mul_left⟩,
    fun i j => tsupport_mul_subset_left.trans (hρ i),?_,?_⟩
  · funext j x
    simp only [Finset.sum_apply]
    rw [←Finset.sum_mul]
    by_cases hx : x∈K
    · have he := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at he
      rw [he,one_mul]
    · have hz : r j x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs j h))
      simp [hz]
  · intro i j
    exact (hbC i).mul ((ρ i).contMDiff.contDiff.differentiable (by simp))
      ((hr j).1.differentiable (by simp)) (hC i).le hM (hb j)

theorem parametric_global_regular_symmetric_correction_C0
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ t in 𝓝 p,∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r K →
      physicalSourceMoment (fun x => u (t,x)) r=0 → ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      BoundedPhysicallyCorrectable (fun x => u (t,x)) U r (L*M) := by
  classical
  by_cases hne : U.Nonempty
  · obtain ⟨x,hx⟩ := hne
    obtain ⟨B,_⟩ := exists_parametric_correction_box hu p hU hx (hD x hx)
    obtain ⟨s,ρ,C,hC,split⟩ := parametric_source_finite_split hu p hU hD hK hKU
    choose D hDpos htransport using fun i : s => parametric_controlled_source_transport hu p hU hUc hD i.val B
    obtain ⟨R,hR,hsolve⟩ := B.bounded_solver
    let S : ℝ := (∑ i,D i*C i)+1
    have hS : 0<S := by
      have hn : 0≤∑ i,D i*C i := Finset.sum_nonneg (fun i _ => mul_nonneg (hDpos i).le (hC i).le)
      change 0<(∑ i : s,D i*C i)+1
      linarith
    refine ⟨(1+R)*S,by positivity,?_⟩
    have ht := Filter.eventually_all.mpr htransport
    filter_upwards [ht,hsolve] with t transport solve
    have hut : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (t,x)) := hu.comp (contDiff_const.prodMk contDiff_id)
    intro r hr hs hm M hM hb
    let p : s → PhysicalSourcePair := fun i j x => ρ i x*r j x
    obtain ⟨hp,hps,hpe,hpb⟩ := split r hr hs M hM hb
    change (∀ i,CompactSmoothPair (p i)) at hp
    change (∀ i,PairSupported (p i) i.val.region) at hps
    change (∑ i,p i)=r at hpe
    change (∀ i j,UniformC1Bound (p i j) (C i*M)) at hpb
    choose q hq hqs hqm hqb hqc using fun i : s =>
      transport i (p i) (hp i) (hps i) (C i*M) (mul_nonneg (hC i).le hM) (hpb i)
    have hN : (∑ i,D i*(C i*M))≤S*M := by
      have he : (∑ i,D i*(C i*M))=(∑ i,D i*C i)*M := by
        simp_rw [←mul_assoc]; exact (Finset.sum_mul _ _ _).symm
      rw [he]; dsimp [S]; nlinarith
    have hQ : CompactSmoothPair (∑ i,q i) := CompactSmoothPair.sum _ q (fun i _ => hq i)
    have hQs : PairSupported (∑ i,q i) B.region := PairSupported.sum _ q (fun i _ => hqs i)
    have hQm : physicalSourceMoment (fun x => u (t,x)) (∑ i,q i)=0 := by
      rw [physicalSourceMoment_sum _ q hut.continuous (fun i _ => hq i)]
      simp_rw [hqm]
      rw [←physicalSourceMoment_sum _ p hut.continuous (fun i _ => hp i),hpe,hm]
    have hQb (j) : UniformC1Bound ((∑ i,q i) j) (S*M) := by
      have he : ((∑ i,q i) j)=(∑ i,q i j) := by funext x; simp only [Finset.sum_apply]
      rw [he]
      exact (UniformC1Bound.sum _ _ _ (fun i _ => (hq i j).1.differentiable (by simp))
        (fun i _ => hqb i j)).mono hN
    have hbase := solve (∑ i,q i) hQ hQs hQm (S*M) (mul_nonneg hS.le hM) hQb
    have hall := ((BoundedPhysicallyCorrectable.sum Finset.univ (fun i => p i-q i)
      (fun i => D i*(C i*M)) hut (fun i _ => hqc i)).mono hN).add hut hbase
    rw [Finset.sum_sub_distrib,sub_add_cancel,hpe] at hall
    exact hall.mono (by ring_nf; rfl)
  · refine ⟨1,zero_lt_one,?_⟩
    apply Filter.Eventually.of_forall
    intro t r hr hs hm M hM hb
    have he : r=0 := by
      funext j x
      exact Function.notMem_support.mp (fun h => hne ⟨x,hKU (hs j (subset_tsupport (r j) h))⟩)
    rw [he]
    exact BoundedPhysicallyCorrectable.zero (by simpa using hM)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RegularVanishingFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem regular_vanishing_family_correction_of_moment
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U)
    {r : Fin 2 → P×Coord3 → ℝ} {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    (hz : ∀ j x,r j (p,x)=0)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x))=0 →
      BoundedPhysicallyCorrectable (fun x => u (q,x)) U (fun j x => r j (q,x)) ε := by
  obtain ⟨L,hL,hsolve⟩ := parametric_global_regular_symmetric_correction_C0 hu p hU hUc hD hK hKU
  have hsmall (j) := compact_supported_family_C1_small hV hp (hr j) hK
    (hs.mono (fun q hq => hq j)) (hz j) (div_pos hε hL)
  have hall := Filter.eventually_all.mpr hsmall
  filter_upwards [hsolve,hall,hs,hV.mem_nhds hp] with q solve small supp hq mom
  have hsm (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => r j (q,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((hr j).contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hcomp (j) : HasCompactSupport (fun x => r j (q,x)) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (supp j)
  have hh := solve (fun j x => r j (q,x)) (fun j => ⟨hsm j,hcomp j⟩) supp mom
    (ε/L) (div_pos hε hL).le small
  simpa only [mul_div_cancel₀ ε hL.ne'] using hh

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricMomentSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem two_sided_vanishing_family_correction
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {U : Set Coord3} (hU : IsOpen U)
    (hcpos : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcneg : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hD : ∀ x∈U,x 2≠0 → Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U)
    {δ : ℝ} (hδ : 0<δ) {r : Fin 2 → P×Coord3 → ℝ}
    {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    (hgap : ∀ᶠ q in 𝓝 p,∀ j x,x∈tsupport (fun y => r j (q,y)) → δ≤|x 2|)
    (hz : ∀ j x,r j (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,
      physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x))=0 →
      physicalSourceMoment (fun x => u (q,x))
        (fun j => wallPositiveCut δ (fun x => r j (q,x)))=0 →
      BoundedPhysicallyCorrectable (fun x => u (q,x)) U (fun j x => r j (q,x)) ε := by
  let rp : Fin 2 → P×Coord3 → ℝ := fun j q =>
    wallPositiveCut δ (fun x => r j (q.1,x)) q.2
  let rn : Fin 2 → P×Coord3 → ℝ := fun j q => r j q-rp j q
  have hrp (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (rp j) (V×ˢuniv) :=
    ((Real.smoothTransition.contDiff.comp
      (((contDiff_apply ℝ ℝ (2:Fin 3)).comp contDiff_snd).div_const δ)).contDiffOn).mul (hr j)
  have hrn (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (rn j) (V×ˢuniv) := (hr j).sub (hrp j)
  have hup : IsOpen (U∩{x : Coord3 | 0<x 2}) := hU.inter (isOpen_lt continuous_const (continuous_apply 2))
  have hun : IsOpen (U∩{x : Coord3 | x 2<0}) := hU.inter (isOpen_lt (continuous_apply 2) continuous_const)
  have hKp : IsCompact (K∩{x : Coord3 | δ≤x 2}) :=
    hK.inter_right (isClosed_le continuous_const (continuous_apply 2))
  have hKn : IsCompact (K∩{x : Coord3 | x 2≤ -δ}) :=
    hK.inter_right (isClosed_le (continuous_apply 2) continuous_const)
  have hsp : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => rp j (q,x)) (K∩{x : Coord3 | δ≤x 2}) := by
    filter_upwards [hs,hgap] with q hq hg
    intro j x hx
    have hh := wallPositiveCut_tsupport hδ (hg j) hx
    exact ⟨hq j hh.1,hh.2⟩
  have hsn : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => rn j (q,x)) (K∩{x : Coord3 | x 2≤ -δ}) := by
    filter_upwards [hs,hgap] with q hq hg
    intro j x hx
    have hh := wallNegativeCut_tsupport hδ (hg j) hx
    exact ⟨hq j hh.1,hh.2⟩
  have hrpz (j x) : rp j (p,x)=0 := by simp [rp,wallPositiveCut,hz]
  have hrnz (j x) : rn j (p,x)=0 := by simp [rn,hz,hrpz]
  have hsolvep := regular_vanishing_family_correction_of_moment hu p hup hcpos
    (fun x hx => hD x hx.1 (ne_of_gt hx.2)) hKp
    (fun x hx => ⟨hKU hx.1,hδ.trans_le hx.2⟩) hV hp hrp hsp hrpz (by linarith : 0<ε/2)
  have hsolven := regular_vanishing_family_correction_of_moment hu p hun hcneg
    (fun x hx => hD x hx.1 (ne_of_lt hx.2)) hKn
    (fun x hx => ⟨hKU hx.1,lt_of_le_of_lt hx.2 (neg_neg_of_pos hδ)⟩)
    hV hp hrn hsn hrnz (by linarith : 0<ε/2)
  filter_upwards [hsolvep,hsolven,hs,hV.mem_nhds hp] with q solvep solven supp hq hm hmp
  have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (q,x)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hrq : CompactSmoothPair (fun j x => r j (q,x)) := by
    intro j
    refine ⟨?_,hK.of_isClosed_subset (isClosed_tsupport _) (supp j)⟩
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((hr j).contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hmn : physicalSourceMoment (fun x => u (q,x)) (fun j x => rn j (q,x))=0 := by
    change physicalSourceMoment (fun x => u (q,x))
      ((fun j x => r j (q,x))-(fun j => wallPositiveCut δ (fun x => r j (q,x))))=0
    rw [physicalSourceMoment_sub huq.continuous hrq
      (fun index => ⟨wallPositiveCut_smooth (hrq index).1,(hrq index).2.mul_left⟩),hm,hmp,sub_self]
  have hh := ((solvep hmp).region_mono inter_subset_left).add huq
    ((solven hmn).region_mono inter_subset_left)
  have he : (fun j x => rp j (q,x))+(fun j x => rn j (q,x))=(fun j x => r j (q,x)) := by
    ext j x; simp only [Pi.add_apply,rn]; ring
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallTransferParametric
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wall_transfer_balanced_residual
    {χ v : Box3 → ℝ} {a : ℝ×ℝ → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a)
    (hz : ∀ z,wallDerivative v (z,0)=0)
    (hne : ∀ z∈tsupport χ,wallQuotient (wallDerivative v) z≠0)
    (hcut : ∀ z,χ (z,0)*a z=a z)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ j x,x∈tsupport (symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) j) → δ≤|x 2|)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r)
    (hm : physicalSourceMoment (wallCoordinatePair v) r=0)
    (hp : ∀ i,(∫ z,a z*wallActualMoment v z i)=
      -physicalSourceMoment (wallCoordinatePair v) (fun j => wallPositiveCut δ (r j)) i) :
    physicalSourceMoment (wallCoordinatePair v)
      (r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v))=0 ∧
    physicalSourceMoment (wallCoordinatePair v)
      (fun j => wallPositiveCut δ ((r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v)) j))=0 := by
  let H := wallHomogeneousTensor χ v a
  let u := wallCoordinatePair v
  have hH : ContDiff ℝ (↑(⊤:ℕ∞)) H := wallHomogeneousTensor_smooth hχ hv ha hne
  have hHc : HasCompactSupport H := (wallHomogeneousTensor_compact (v:=v) (a:=a) hχc).1
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) u := wallCoordinatePair_smooth hv
  have hs := symmetricSource_compactSmoothPair hH hHc hu
  have hpos : physicalSourceMoment u (fun j => wallPositiveCut δ (symmetricSource H u j))=
      physicalSourceMoment u (fun j => wallPositiveCut δ (r j)) := by
    rw [wallPositiveSource_moment hχ hχc hv ha hz hne hcut hδ hgap]
    ext i
    rw [hp i,neg_neg]
  constructor
  · rw [physicalSourceMoment_sub hu.continuous hr hs,hm,
      physicalSourceMoment_symmetricSource hH hHc (wallMatrix_symmetric _ _) hu,sub_self]
  · have he : (fun j => wallPositiveCut δ ((r-symmetricSource H u) j))=
        (fun j => wallPositiveCut δ (r j))-(fun j => wallPositiveCut δ (symmetricSource H u j)) := by
      ext j x
      exact congrFun (wallPositiveCut_sub δ (r j) (symmetricSource H u j)) x
    change physicalSourceMoment u (fun j => wallPositiveCut δ ((r-symmetricSource H u) j))=0
    rw [he,physicalSourceMoment_sub hu.continuous (hr.wallPositiveCut δ) (hs.wallPositiveCut δ),hpos,sub_self]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma wall_transfer_residual_solver
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {U : Set Coord3} (hU : IsOpen U)
    (hcp : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcn : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hD : ∀ x∈U,x 2≠0 → Function.Surjective
      (fderiv ℝ (wallCoordinatePair (fun y => v (p,y))) x))
    {χ : Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    {θ η : ℝ → ℝ} (hθ : ContDiff ℝ (↑(⊤:ℕ∞)) θ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    (σ lam : ℝ) {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hne : ∀ q∈V,∀ z∈tsupport χ,wallQuotient (wallDerivative (fun y => v (q,y))) z≠0)
    {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U)
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ᶠ q in 𝓝 p,∀ j x,x∈tsupport (fun y => r j (q,y)) → δ≤|x 2|)
    (hG : ∀ q∈V,∀ c j x,x∈tsupport (fun y => wallTransferSource χ v θ η σ lam j ((q,c),y)) → δ≤|x 2|)
    (hrz : ∀ j x,r j (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    let R : Fin 2 → (P×Coord3)×Coord3 → ℝ := fun j q =>
      r j (q.1.1,q.2)-wallTransferSource χ v θ η σ lam j q
    ∀ᶠ q in 𝓝 (p,(0:Coord3)),
      physicalSourceMoment (wallCoordinatePair (fun y => v (q.1,y))) (fun j x => R j (q,x))=0 →
      physicalSourceMoment (wallCoordinatePair (fun y => v (q.1,y)))
        (fun j => wallPositiveCut δ (fun x => R j (q,x)))=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q.1,y))) U (fun j x => R j (q,x)) ε := by
  let u : P×Coord3 → Fin 2 → ℝ := fun q => wallCoordinatePair (fun y => v (q.1,y)) q.2
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) u := wallCoordinatePair_parametric_smooth hv
  let R : Fin 2 → (P×Coord3)×Coord3 → ℝ := fun j q =>
    r j (q.1.1,q.2)-wallTransferSource χ v θ η σ lam j q
  have hR (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (R j) ((V×ˢuniv)×ˢuniv) := by
    exact ((hr j).comp (contDiff_fst.fst.prodMk contDiff_snd).contDiffOn
      (fun q hq => ⟨hq.1.1,mem_univ q.2⟩)).sub
        (wallTransferSource_smoothOn σ lam hχ hv hθ hη hV hne j)
  have hRz (j x) : R j ((p,0),x)=0 := by
    simp only [R,hrz,wallTransferSource_zero,sub_self]
  have hlift : Tendsto (Prod.fst : P×Coord3 → P) (𝓝 (p,0)) (𝓝 p) := continuous_fst.tendsto _
  have hRs : ∀ᶠ q in 𝓝 (p,(0:Coord3)),PairSupported (fun j x => R j (q,x))
      (K∪boxCoordinates ⁻¹' tsupport χ) := by
    filter_upwards [hlift.eventually hs] with q hq
    intro j
    exact (tsupport_sub _ _).trans (union_subset ((hq j).trans subset_union_left)
      ((wallTransferSource_tsupport hχc v θ η σ lam q j).trans subset_union_right))
  have hRg : ∀ᶠ q in 𝓝 (p,(0:Coord3)),∀ j x,x∈tsupport (fun y => R j (q,y)) → δ≤|x 2| := by
    filter_upwards [hlift.eventually hgap,hlift.eventually (hV.mem_nhds hp)] with q hq hqV
    intro j x hx
    rcases tsupport_sub _ _ hx with hx | hx
    · exact hq j x hx
    · exact hG q.1 hqV q.2 j x hx
  exact two_sided_vanishing_family_correction
    (u:=fun q : (P×Coord3)×Coord3 => u (q.1.1,q.2))
    (r:=R) (hu.comp (contDiff_fst.fst.prodMk contDiff_snd)) (p,(0:Coord3)) hU hcp hcn hD
    (hK.union (boxCoordinates.toHomeomorph.isCompact_preimage.mpr hχc))
    (union_subset hKU hχU) hδ (hV.prod isOpen_univ) ⟨hp,mem_univ 0⟩ hR hRs hRg hRz hε

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallVanishingMomentCoefficients
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wall_transfer_finishes
    {χ v : Box3 → ℝ} {a : ℝ×ℝ → ℝ} {U : Set Coord3}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a)
    (hz : ∀ z,wallDerivative v (z,0)=0)
    (hne : ∀ z∈tsupport χ,wallQuotient (wallDerivative v) z≠0)
    (hcut : ∀ z,χ (z,0)*a z=a z)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ j x,x∈tsupport (symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) j) → δ≤|x 2|)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r)
    (hm : physicalSourceMoment (wallCoordinatePair v) r=0)
    (hp : ∀ i,(∫ z,a z*wallActualMoment v z i)=
      -physicalSourceMoment (wallCoordinatePair v) (fun j => wallPositiveCut δ (r j)) i)
    {ε : ℝ} (hsmall : ∀ x,‖wallHomogeneousTensor χ v a x‖≤ε/2)
    (hsolve : physicalSourceMoment (wallCoordinatePair v)
        (r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v))=0 →
      physicalSourceMoment (wallCoordinatePair v)
        (fun j => wallPositiveCut δ ((r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v)) j))=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair v) U
        (r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v)) (ε/2)) :
    BoundedPhysicallyCorrectable (wallCoordinatePair v) U r ε := by
  let H := wallHomogeneousTensor χ v a
  let u := wallCoordinatePair v
  have hH : ContDiff ℝ (↑(⊤:ℕ∞)) H := wallHomogeneousTensor_smooth hχ hv ha hne
  have hc := wallHomogeneousTensor_compact (χ:=χ) (v:=v) (a:=a) hχc
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) u := wallCoordinatePair_smooth hv
  have hbal := wall_transfer_balanced_residual hχ hχc hv ha hz hne hcut hδ hgap hr hm hp
  have hcor : BoundedPhysicallyCorrectable u U (symmetricSource H u) (ε/2) :=
    ⟨H,hH,hc.1,hc.2.trans hχU,wallMatrix_symmetric _ _,fun _ => rfl,hsmall⟩
  have hh := hcor.add hu (hsolve hbal.1 hbal.2)
  rw [add_sub_cancel] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem critical_wall_vanishing_transfer_correction
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {U : Set Coord3} (hU : IsOpen U)
    (hcp : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcn : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hD : ∀ x∈U,x 2≠0 → Function.Surjective
      (fderiv ℝ (wallCoordinatePair (fun y => v (p,y))) x))
    {χ : Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    {l t a b σ lam : ℝ} (hlt : l<t) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    (hcore : ∀ z∈Icc l t×ˢIcc a b,χ =ᶠ[𝓝 (z,0)] (fun _ => 1))
    (hlim : ∀ z : ℝ×ℝ,v (p,(z,0))=σ*Real.exp (-lam*z.1))
    {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hz : ∀ q∈V,∀ z,wallDerivative (fun y => v (q,y)) (z,0)=0)
    (hne : ∀ q∈V,∀ z∈tsupport χ,wallQuotient (wallDerivative (fun y => v (q,y))) z≠0)
    {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U)
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    {δr : ℝ} (hδr : 0<δr)
    (hgap : ∀ᶠ q in 𝓝 p,∀ j x,x∈tsupport (fun y => r j (q,y)) → δr≤|x 2|)
    (hrz : ∀ j x,r j (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,
      physicalSourceMoment (wallCoordinatePair (fun y => v (q,y))) (fun j x => r j (q,x))=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U
        (fun j x => r j (q,x)) ε := by
  have hvq (q : P) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨δh,hδh,hsourcegap⟩ := exists_uniform_wall_source_gap hχ hχc
    (isClosed_Icc.prod isClosed_Icc) hcore
  let δ := min δr δh
  have hδ : 0<δ := lt_min hδr hδh
  obtain ⟨θ,η,hθ,hη,hθc,hηc,hθs,hηs,c,hc,hcm⟩ :=
    wall_vanishing_moment_coefficients hv p hlt hab hσ hlam hlim hV hp hr hK hs hrz δ
  have haSmooth (c : Coord3) : ContDiff ℝ (↑(⊤:ℕ∞)) (wallMomentAmplitude θ η σ lam c) :=
    (wallMomentAmplitude_parametric_smooth σ lam hθ hη).comp (contDiff_const.prodMk contDiff_id)
  have haSupp (c : Coord3) : tsupport (wallMomentAmplitude θ η σ lam c)⊆Icc l t×ˢIcc a b :=
    (wallMomentAmplitude_compact σ lam hθc hηc c).2.trans
      (prod_mono hθs (hηs.trans Ioo_subset_Icc_self))
  have hG (q : P) (hq : q∈V) (c : Coord3) (j : Fin 2) (x : Coord3)
      (hx : x∈tsupport (fun y => wallTransferSource χ v θ η σ lam j ((q,c),y))) :
      δ≤|x 2| :=
    (min_le_right δr δh).trans (hsourcegap (fun y => v (q,y))
      (wallMomentAmplitude θ η σ lam c) (hvq q) (haSmooth c) (hz q hq) (hne q hq)
      (haSupp c) j x hx)
  have hRsolve := wall_transfer_residual_solver hv p hU hcp hcn hD hχ hχc hχU
    hθ hη σ lam hV hp hne hr hK hKU hs hδ
    (hgap.mono (fun q hq j x hx => (min_le_left δr δh).trans (hq j x hx))) hG hrz
    (by linarith : 0<ε/2)
  have hHsmall := wallTransferFamily_small σ lam hχ hχc hv hθ hη hV hp hne (by linarith : 0<ε/2)
  have hqc : Tendsto (fun q => (q,c q)) (𝓝 p) (𝓝 (p,0)) := tendsto_id.prodMk_nhds hc
  filter_upwards [hqc.eventually hRsolve,hqc.eventually hHsmall,hcm,hs,hV.mem_nhds hp]
    with q hsolve hsmall hcmq hsq hq hmom
  have hrc : CompactSmoothPair (fun j x => r j (q,x)) := by
    intro j
    refine ⟨?_,hK.of_isClosed_subset (isClosed_tsupport _) (hsq j)⟩
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((hr j).contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hcut (z) : χ (z,0)*wallMomentAmplitude θ η σ lam (c q) z=
      wallMomentAmplitude θ η σ lam (c q) z := by
    by_cases hn : wallMomentAmplitude θ η σ lam (c q) z=0
    · simp only [hn,mul_zero]
    · rw [(hcore z (haSupp (c q) (subset_tsupport _ hn))).eq_of_nhds,one_mul]
  exact wall_transfer_finishes hχ hχc hχU (hvq q) (haSmooth (c q))
    (hz q hq) (hne q hq) hcut hδ (hG q hq (c q)) hrc hmom hcmq hsmall hsolve

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallFamilyCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem critical_wall_family_correction
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (hz : ∀ q z,wallDerivative (fun y => v (q,y)) (z,0)=0)
    {U : Set Coord3} (hU : IsOpen U)
    (hcp : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcn : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hne₀ : ∀ x∈U,wallQuotient (wallDerivative (fun y => v (p,y))) (boxCoordinates x)≠0)
    {χ : Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    {S : Set Box3} (hS : IsCompact S) (hSU : boxCoordinates ⁻¹' S⊆U)
    {K : Set (ℝ×ℝ)} (hK : IsClosed K)
    (hcore : ∀ z∈K,χ =ᶠ[𝓝 (z,0)] (fun _ => 1))
    {l t a b σ lam : ℝ} (hlt : l<t) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    (hrect : Icc l t×ˢIcc a b⊆K)
    (hlim : ∀ z : ℝ×ℝ,v (p,(z,0))=σ*Real.exp (-lam*z.1))
    {r : Fin 2 → P×Box3 → ℝ}
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    (hs : ∀ᶠ q in 𝓝 p,∀ j,tsupport (fun y => r j (q,y))⊆S∩Prod.fst ⁻¹' K)
    (hrz : ∀ j y,r j (p,y)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,
      physicalSourceMoment (wallCoordinatePair (fun y => v (q,y))) (wallInputPair r q)=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U (wallInputPair r q) ε := by
  have hvq (q : P) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  have hrq (q : P) (j : Fin 2) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => r j (q,y)) :=
    (hr j).comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨V,hV,hp,hne⟩ := compact_parameter_nonzero_neighborhood
    (wallQuotient_parametric_smooth (wallDerivative_parametric_smooth hv)).continuous hχc
    (fun z hz => by
      have h := hne₀ (boxCoordinates.symm z) (hχU (by
        change boxCoordinates (boxCoordinates.symm z)∈tsupport χ
        simpa only [boxCoordinates.apply_symm_apply] using hz))
      simpa only [boxCoordinates.apply_symm_apply] using h)
  obtain ⟨δ,hδ,hgap⟩ := exists_uniform_particular_residual_gap hχ hχc hK hS hcore
  let R := wallResidualFamily χ v r
  have hRs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => R j (q,x))
      (boxCoordinates ⁻¹' (S∪tsupport χ)) := by
    filter_upwards [hs] with q hq
    exact fun j => wallResidualFamily_tsupport hχc (fun j => (hq j).trans inter_subset_left) j
  have hRg : ∀ᶠ q in 𝓝 p,∀ j x,x∈tsupport (fun y => R j (q,y)) → δ≤|x 2| := by
    filter_upwards [hs,hV.mem_nhds hp] with q hq hqV
    exact hgap (fun y => v (q,y)) (fun y => r 0 (q,y)) (fun y => r 1 (q,y))
      (hvq q) (hrq q 0) (hrq q 1) (hz q) (hne q hqV) (hq 0) (hq 1)
  have hD (x : Coord3) (hx : x∈U) (hn : x 2≠0) :
      Function.Surjective (fderiv ℝ (wallCoordinatePair (fun y => v (p,y))) x) :=
    wallCoordinatePair_surjective_off_wall (hvq p) (hz p) hn (hne₀ x hx)
  have hRU : boxCoordinates ⁻¹' (S∪tsupport χ)⊆U := by
    intro x hx
    rcases hx with hx | hx
    · exact hSU hx
    · exact hχU hx
  have hsolve := critical_wall_vanishing_transfer_correction hv p hU hcp hcn hD hχ hχc hχU
    hlt hab hσ hlam (fun z hz => hcore z (hrect hz)) hlim hV hp
    (fun q _ => hz q) hne (wallResidualFamily_smoothOn hχ hv hr hV hne)
    (boxCoordinates.toHomeomorph.isCompact_preimage.mpr (hS.union hχc)) hRU hRs hδ hRg
    (wallResidualFamily_zero hrz) (by linarith : 0<ε/2)
  have hsmall := wallParticularFamily_small hχ hχc hv hr hV hp hne hrz (by linarith : 0<ε/2)
  filter_upwards [hsolve,hsmall,hs,hV.mem_nhds hp] with q solve small supp hq hm
  have hrs (j) : HasCompactSupport (fun y => r j (q,y)) :=
    hS.of_isClosed_subset (isClosed_tsupport _) ((supp j).trans inter_subset_left)
  exact wall_particular_family_finishes hχ hχc hv hr q hχU hrs (hne q hq) hm small solve

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CriticalWallRegion
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def criticalWallRegion
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (hz : ∀ q z,wallDerivative (fun y => v (q,y)) (z,0)=0)
    {U W : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUW : U⊆W) (hneU : U.Nonempty)
    (hcp : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcn : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hproj : ∀ x∈U,boxCoordinates.symm ((boxCoordinates x).1,0)∈U)
    (hne₀ : ∀ x∈U,wallQuotient (wallDerivative (fun y => v (p,y))) (boxCoordinates x)≠0)
    {l t a b σ lam : ℝ} (hlt : l<t) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    (hrectU : ∀ z∈Icc l t×ˢIcc a b,boxCoordinates.symm (z,0)∈U)
    (hlim : ∀ z : ℝ×ℝ,v (p,(z,0))=σ*Real.exp (-lam*z.1)) :
    VanishingCorrectionRegion (fun z => wallCoordinatePair (fun y => v (z.1,y)) z.2) p W := by
  classical
  refine ⟨U,hU,hneU,hUW,hUb,?_⟩
  intro r hr ε hε
  obtain ⟨S,hS,hSU,hss⟩ := hr.2.2
  let T : Set Box3 := boxCoordinates '' S
  have hT : IsCompact T := hS.image boxCoordinates.continuous
  let K : Set (ℝ×ℝ) := Prod.fst '' T ∪ (Icc l t×ˢIcc a b)
  have hK : IsCompact K := (hT.image continuous_fst).union (isCompact_Icc.prod isCompact_Icc)
  let J : Set Box3 := (fun z : ℝ×ℝ => (z,(0:ℝ))) '' K
  have hJ : IsCompact J := hK.image (continuous_id.prodMk continuous_const)
  let Ω : Set Box3 := boxCoordinates.symm ⁻¹' U
  have hΩ : IsOpen Ω := hU.preimage boxCoordinates.symm.continuous
  have hΩb : Bornology.IsBounded Ω := by
    rw [show Ω=boxCoordinates '' U from by
      ext z
      constructor
      · intro hz; exact ⟨boxCoordinates.symm z,hz,boxCoordinates.apply_symm_apply z⟩
      · rintro ⟨x,hx,rfl⟩; simpa only [Ω,mem_preimage,boxCoordinates.symm_apply_apply] using hx]
    exact boxCoordinates.toContinuousLinearMap.lipschitz.isBounded_image hUb
  have hJU : J⊆Ω := by
    rintro _ ⟨z,hz,rfl⟩
    rcases hz with hz | hz
    · rcases hz with ⟨w,⟨x,hx,rfl⟩,rfl⟩
      exact hproj x (hSU hx)
    · exact hrectU z hz
  obtain ⟨χ,hχ,hχc,hχU,_,hχone⟩ := exists_smooth_core_cutoff hJ hΩ hΩb hJU
  let R : Fin 2 → P×Box3 → ℝ := fun j z => r j (z.1,boxCoordinates.symm z.2)
  have hR (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (R j) :=
    (hr.1 j).comp (contDiff_fst.prodMk (boxCoordinates.symm.contDiff.comp contDiff_snd))
  have hRs : ∀ q j,tsupport (fun y => R j (q,y))⊆T∩Prod.fst ⁻¹' K := by
    intro q j y hy
    have hh : boxCoordinates.symm y∈S := hss q j
      ((tsupport_comp_subset_preimage (fun x => r j (q,x)) boxCoordinates.symm.continuous) hy)
    have hyT : y∈T := ⟨boxCoordinates.symm y,hh,boxCoordinates.apply_symm_apply y⟩
    exact ⟨hyT,Or.inl ⟨y,hyT,rfl⟩⟩
  have hsolve := critical_wall_family_correction hv p hz hU hcp hcn hne₀ hχ hχc
    (fun x hx => by
      have hh : boxCoordinates.symm (boxCoordinates x)∈U := hχU hx
      simpa only [boxCoordinates.symm_apply_apply] using hh) hT
    (fun x hx => by rcases hx with ⟨y,hy,he⟩; exact hSU (boxCoordinates.injective he ▸ hy))
    hK.isClosed (fun z hz => hχone (z,0) ⟨z,hz,rfl⟩) hlt hab hσ hlam
    (fun _ hz => Or.inr hz) hlim hR (Filter.Eventually.of_forall hRs)
    (fun j y => hr.2.1 j _) hε
  filter_upwards [hsolve] with q hq hm
  have he : wallInputPair R q=(fun j x => r j (q,x)) := by
    funext j x
    simp only [wallInputPair,R,boxCoordinates.symm_apply_apply]
  rw [he] at hq
  exact (hq hm).region_mono hUW

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_VoltageJetCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

lemma compactVoltageJets_zero (μ : Measure Coord3) (U : Set Coord3) :
    (0 : VoltageJetSpace μ U) ∈ compactVoltageJets μ U := by
  refine ⟨0,contDiff_const,HasCompactSupport.zero,?_,MemLp.zero,?_,?_⟩
  · simp
  · rw [voltageGradient_zero]; exact MemLp.zero
  · simp only [voltageGradient_zero,MemLp.toLp_zero,Prod.zero_eq_mk]

lemma compactVoltageJets_smul (μ : Measure Coord3) (U : Set Coord3)
    (c : ℝ) {z : VoltageJetSpace μ U} (hz : z ∈ compactVoltageJets μ U) :
    c • z ∈ compactVoltageJets μ U := by
  obtain ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩ := hz
  have he := voltageGradient_smul c (hv.differentiable (by simp))
  have hmg : MemLp (voltageGradient (c • v)) 2 (μ.restrict U) := by
    rw [he]; exact hvg.const_smul c
  refine ⟨c • v,hv.const_smul c,hvc.smul_left,
    (tsupport_smul_subset_right (fun _ : Coord3 => c) v).trans hvs,
    hvm.const_smul c,hmg,?_⟩
  apply Prod.ext
  · exact (MemLp.toLp_const_smul c hvm).symm
  · change c • hvg.toLp _ = hmg.toLp _
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun he x |>.symm)

def compactVoltageJetModule (μ : Measure Coord3) (U : Set Coord3) :
    Submodule ℝ (VoltageJetSpace μ U) where
  carrier := compactVoltageJets μ U
  zero_mem' := compactVoltageJets_zero μ U
  add_mem' := compactVoltageJets_add μ U
  smul_mem' := compactVoltageJets_smul μ U

def zeroVoltageJets (μ : Measure Coord3) (U : Set Coord3) :
    Submodule ℝ (VoltageJetSpace μ U) :=
  (compactVoltageJetModule μ U).topologicalClosure

instance zeroVoltageJets_complete (μ : Measure Coord3) (U : Set Coord3) :
    CompleteSpace (zeroVoltageJets μ U) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def zeroVoltageGradientMap (μ : Measure Coord3) (U : Set Coord3) :
    zeroVoltageJets μ U →L[ℝ] Lp FieldVector 2 (μ.restrict U) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (zeroVoltageJets μ U).subtypeL

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_TorusEndingCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

def torusInitialPair (s : Fin 3 → ℝ) (f : Fin 2 → TorusL2) (x : Coord3) : Fin 2 → ℝ :=
  fun j => torusAffineField s (normalizedSlope j) (f j) x

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedSplicedGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal

local instance attachedSplicedGreenMeasureSpace_rebe034_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {s : Fin 3 → ℝ} (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))

def splicedAttachedGradient (j : Fin 2) (a b : ℝ) (y : Coord3) : Coord3 :=
  fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y+
    (fun k => lineDeriv ℝ (attachedPeriodicField (branchCorrection i z j) a b) y (Pi.single k 1))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalBlockTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

def physicalEndTensor (s a : Fin 3 → ℝ) (i : Fin 3) :
    (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  Fin.cases (attachedCollarTensor s (a 0))
    (fun k => sourceChildTensorPush k (attachedCollarTensor s (a k.succ))) i

def physicalBlockTensorList (s a : Fin 3 → ℝ) (is : List (Fin 3))
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := by
  classical
  exact is.foldr (fun i A => if y∈physicalEndRegion i then physicalEndTensor s a i y else A) 1

def physicalBlockTensor (s a : Fin 3 → ℝ) :
    (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  physicalBlockTensorList s a (Finset.univ : Finset (Fin 3)).toList

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_BranchCombine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

def sourceAveragePull : H1 →L[ℝ] H1 := (1/2:ℝ) • (childH1Pullback 0+childH1Pullback 1)
def sourceDifferencePull : H1 →L[ℝ] H1 := childH1Pullback 0-childH1Pullback 1

end

open Set MeasureTheory Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_CopiedEnergyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def sourceAveragePullIter : ℕ → H1 →L[ℝ] H1
  | 0 => ContinuousLinearMap.id ℝ H1
  | n+1 => (sourceAveragePullIter n).comp sourceAveragePull

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WordTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

def sourceWordPull : SourceWord → H1 →L[ℝ] H1
  | [] => ContinuousLinearMap.id ℝ H1
  | k::ν => (sourceWordPull ν).comp (childH1Pullback k)

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_13
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_13_rebe034_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def sourceWordTraceCLM (ν : SourceWord) : H1 →L[ℝ] Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  (physicalRealTraceCLM 0).comp (sourceWordPull ν)

end ScalarConductivity

end
end

end OAI
end


