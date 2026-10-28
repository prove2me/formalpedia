-- Prove2me | Definitions.Def_OAIQ059C000
-- name    : OAIQ059C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:32:15.660991+00:00
-- url     : https://prove2.me/theorems/9a72fe97-674e-4f24-972c-558c632da912
-- title:
--   Definitions bundle OAIQ059C000 of the split of OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 385 declarations of OpenAI's Lean: 158 definitions, 2 inductive types or structures, 4 instances and 221 theorems. The definitions and types are `OAI.ScalarConductivity.AnalyticNullProperty`, `OAI.ScalarConductivity.AngularPeriodic`, `OAI.ScalarConductivity.ApproxScalar`, `OAI.ScalarConductivity.BoundedPhysicallyCorrectable`, `OAI.ScalarConductivity.Box3`, `OAI.ScalarConductivity.CentralAmbient`, `OAI.ScalarConductivity.CentralJets`, `OAI.ScalarConductivity.CentralL2`, `OAI.ScalarConductivity.CentralTraceFields`, `OAI.ScalarConductivity.CompactSmoothPair`, `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.Mat3`, `OAI.ScalarConductivity.PairSupported`, `OAI.ScalarConductivity.PhysicalSourcePair`, `OAI.ScalarConductivity.RectFootprint`, `OAI.ScalarConductivity.RectFootprint.carrier`, `OAI.ScalarConductivity.RectFootprint.inter`, `OAI.ScalarConductivity.RectFootprint.prism`, `OAI.ScalarConductivity.RegularPatch`, `OAI.ScalarConductivity.SmoothScalar`, `OAI.ScalarConductivity.SourceWord`, `OAI.ScalarConductivity.SpectralJet`, `OAI.ScalarConductivity.SpectralL2`, `OAI.ScalarConductivity.Symmetric3`, `OAI.ScalarConductivity.TorusModes`, `OAI.ScalarConductivity.TwoFieldRankRegular`, `OAI.ScalarConductivity.WeakFiniteTensorPair`, `OAI.ScalarConductivity.WeakFiniteTensorPair.linear`, `OAI.ScalarConductivity.WeakFiniteTensorPair.onEq`, `OAI.ScalarConductivity.WeakFiniteTensorPair.output`, `OAI.ScalarConductivity.WeakFiniteTensorPair.translate`, `OAI.ScalarConductivity.actualChildSign`, `OAI.ScalarConductivity.angularArea`, `OAI.ScalarConductivity.angularInverseLift`, `OAI.ScalarConductivity.angularInverseLinear`, `OAI.ScalarConductivity.angularNormalization`, `OAI.ScalarConductivity.angularNormalizedEquiv`, `OAI.ScalarConductivity.angularNormalizedLift`, `OAI.ScalarConductivity.angularNormalizedLinear`, `OAI.ScalarConductivity.angularShift` and 120 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Conductivity_Branching_CentralChildCollar`, `Conductivity_Branching_ChildCentralL2`, `Conductivity_Branching_ChildCoordinateAnalysis`, `Conductivity_Branching_ChildInverse`, `Conductivity_Branching_LinearFiniteEndTransport`, `Conductivity_Branching_PhysicalBlockEnergy`, `Conductivity_Branching_PhysicalChildIntegral`, `Conductivity_Flux_AntisymmetricFlux`, `Conductivity_Flux_CollarCartesianDifferential`, `Conductivity_Flux_CompactFluxDivergence`, `Conductivity_Flux_FiniteEndPhysicalTensor`, `Conductivity_Flux_LinearFluxWeakTransport`, `Conductivity_Flux_LinearTensorEllipticity`, `Conductivity_Flux_LocalTensorBounds`, `Conductivity_Flux_PhysicalTensorPatch`, `Conductivity_Flux_PiolaFluxAdd`, `Conductivity_Flux_TwoFluxColumns`, `Conductivity_Fourier_AnalyticNull`, `Conductivity_Fourier_AngularFourierConjugacy`, `Conductivity_Fourier_AngularIntegratedTrace`, `Conductivity_Fourier_AngularNormalTrace`, `Conductivity_Fourier_AngularPeriodization`, `Conductivity_Fourier_CollarAngularInverse`, `Conductivity_Fourier_GeneralModeFiniteEndNormal`, `Conductivity_Fourier_LeadingFrequencyAlignment`, `Conductivity_Fourier_RectangularRayTrace`, `Conductivity_Fourier_RectangularTorusAtlas`, `Conductivity_Fourier_SmoothPhase`, `Conductivity_Fourier_TorusFourierTranslation`, `Conductivity_Fourier_TorusNonresonance`, `Conductivity_Fourier_TorusPoissonContinuous`, `Conductivity_Fourier_UndoAngularWeakPair`, `Conductivity_Geometry_BoxEnergyPoincare`, `Conductivity_Geometry_CollarInteriorFacts`, `Conductivity_Geometry_ControlledCorrectionBoxes`, `Conductivity_Geometry_ExtendedCollar`, `Conductivity_Geometry_PhysicalBoxCorrection`, `Conductivity_Geometry_PhysicalCollarBand`, `Conductivity_Geometry_PhysicalCollarTrace`, `Conductivity_Geometry_PhysicalEndRegions`, `Conductivity_Geometry_RegularPatch`, `Conductivity_Geometry_RegularPatchLinear`, `Conductivity_Geometry_RegularPatchTranslation`, `Conductivity_Geometry_TorusExponential`, `Conductivity_Geometry_TorusFaceIntegration`, `Conductivity_Geometry_TorusLipschitzTrace`, `Conductivity_Scalarization_ApproxScalar`, `Conductivity_Scalarization_SmoothScalarAlgebra`, `Conductivity_Sobolev_CentralPairRegularity`, `Conductivity_Sobolev_CentralPhysicalTrace`, `Conductivity_Sobolev_CentralPhysicalVariational`, `Conductivity_Sobolev_CentralPoincare`, `Conductivity_Sobolev_ChildH10Transport`, `Conductivity_Sobolev_LocalPiolaFlux`, `Conductivity_Sobolev_LpExtension`, `Conductivity_Sobolev_NonlinearLp`, `Conductivity_Sobolev_PhysicalProductJet`, `Conductivity_Sobolev_SobolevSmoothTests`, `Conductivity_Sources_AngularTrace`, `Conductivity_Sources_LocalPiola`, `Conductivity_Sources_LocalRegular`, `Conductivity_Sources_NestedGeometry`, `Conductivity_Sources_SymmetricCutoffSources`, `Conductivity_Sources_WeightedSpectralSpace`, `Conductivity_Sources_WordGeometry`, `Conductivity_Variational_AirySymbol`, `Conductivity_Variational_CentralAnchor`, `Conductivity_Variational_CentralEnergySpace`, `Conductivity_Variational_CentralSmoothTrace`, `Conductivity_Variational_CentralUnnormalizedVariational`, `Conductivity_Variational_CompactDepthReductionTwo`, `Conductivity_Variational_CompactPhysicalCorrections`, `Conductivity_Variational_ContDiffClmDet`, `Conductivity_Variational_CrossingHxx`, `Conductivity_Variational_DerivativeEquiv`, `Conductivity_Variational_DirectionCalculus`, `Conductivity_Variational_FiniteEndPhysicalDescent`, `Conductivity_Variational_GradientColumns`, `Conductivity_Variational_LocalBoundedPiolaCorrection`, `Conductivity_Variational_LocalSymmetricPiola`, `Conductivity_Variational_MatrixFiniteLaminate`, `Conductivity_Variational_MatrixOperator`, `Conductivity_Variational_MetricControlledPiola`, `Conductivity_Variational_ParametricLocalRegularCorrection`, `Conductivity_Variational_PhysicalFlatEllipticity`, `Conductivity_Variational_PhysicalOuterTrace`, `Conductivity_Variational_PhysicalSmoothTest`, `Conductivity_Variational_PhysicalTraceBounds`, `Conductivity_Variational_PreliminaryQ`, `Conductivity_Variational_QuantitativeGlobalCorrection`, `Conductivity_Variational_QuantitativeLocalTwoFieldSplit`, `Conductivity_Variational_RankProjectionFirst`, `Conductivity_Variational_SmoothCompose`, `Conductivity_Variational_SmoothPrimitive`, `Conductivity_Variational_SymmetricCorrection`, `Conductivity_Variational_SynchronizedChartWaves`, `Conductivity_Variational_UnitSquarePoincare`, `Conductivity_Variational_WholeBallJet`, `Conductivity_Variational_WholeBallJetFormula`.
--
--   **Imports.** It imports the published bundle `Def_Conductivity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ059C003`, `OAIQ059C004` and `OAIQ059C005`.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Conductivity

section
-- module Solutions.OAIQ059_CD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_NestedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def sourceScale : ℝ := 57/100
def sourceOffset : ℝ := 81/100
def sourceLength : ℝ := 8/5
def sourceHole : ℝ := 3/100

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_RectangularTorusAtlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def squareFaceBase : Fin 4 → Fin 2 → ℝ := ![![1,0],![0,1],![-1,0],![0,-1]]
def squareFaceDirection : Fin 4 → Fin 2 → ℝ := ![![0,1],![-1,0],![0,-1],![1,0]]
def squareFace (i : Fin 4) (a : ℝ) : Fin 2 → ℝ := squareFaceBase i+a • squareFaceDirection i

lemma squareFace_max (i : Fin 4) {a : ℝ} (ha : |a|≤1) :
    max |squareFace i a 0| |squareFace i a 1|=1 := by
  fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,abs_neg,
    max_eq_left ha,max_eq_right ha]

lemma squareFace_min_max (v : Fin 2 → ℝ) (hm : max |v 0| |v 1|=1) :
    ∃ i : Fin 4, ∃ a : ℝ, |a|≤1 ∧ squareFace i a=v := by
  have h0 : |v 0|≤1 := le_max_left _ _ |>.trans hm.le
  have h1 : |v 1|≤1 := le_max_right _ _ |>.trans hm.le
  rcases max_cases |v 0| |v 1| with h | h
  · have he : |v 0|=1 := h.1.symm.trans hm
    rcases abs_cases (v 0) with hp | hn
    · refine ⟨0,v 1,h1,?_⟩
      have hv : v 0=1 := hp.1.symm.trans he
      ext k; fin_cases k <;> simp [squareFace,squareFaceBase,squareFaceDirection,hv]
    · refine ⟨2,-v 1,by simpa using h1,?_⟩
      have hv : v 0= -1 := by linarith [hn.1,he]
      ext k; fin_cases k <;> simp [squareFace,squareFaceBase,squareFaceDirection,hv]
  · have he : |v 1|=1 := h.1.symm.trans hm
    rcases abs_cases (v 1) with hp | hn
    · refine ⟨1,-v 0,by simpa using h0,?_⟩
      have hv : v 1=1 := hp.1.symm.trans he
      ext k; fin_cases k <;> simp [squareFace,squareFaceBase,squareFaceDirection,hv]
    · refine ⟨3,v 0,h0,?_⟩
      have hv : v 1= -1 := by linarith [hn.1,he]
      ext k; fin_cases k <;> simp [squareFace,squareFaceBase,squareFaceDirection,hv]

def sourceRadialCenter : ℝ := (1+sourceHole)/2
def sourceRadialWidth : ℝ := (1-sourceHole)/2

def sourceCollarRadius (j : Fin 4) (t b : ℝ) : ℝ :=
  sourceRadialCenter+sourceRadialWidth*(1-t)*squareFace j b 0

def sourceCollarPiece (i j : Fin 4) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0,
    sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1,
    (1-x 0)*squareFace j (x 2) 1]

def sourceRadial (x : Fin 3 → ℝ) : ℝ := max (|x 0|/sourceLength) |x 1|

def sourceCrossCoordinates (x : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![(sourceRadial x-sourceRadialCenter)/sourceRadialWidth,x 2]

def sourceCollarTime (x : Fin 3 → ℝ) : ℝ :=
  1-max |sourceCrossCoordinates x 0| |sourceCrossCoordinates x 1|

lemma sourceCollarPiece_contDiff (i j : Fin 4) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (sourceCollarPiece i j) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases k <;> simp [sourceCollarPiece,sourceCollarRadius,squareFace] <;> fun_prop

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_UnitSquarePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

abbrev Box3 := (ℝ×ℝ)×ℝ

def cubePartial (f : Box3 → ℝ) (v : Box3) (z : Box3) : ℝ := fderiv ℝ f z v

lemma continuous_cubePartial {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (v : Box3) : Continuous (cubePartial f v) :=
  (hf.fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_BoxEnergyPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

structure RectFootprint where
  xl : ℝ
  xu : ℝ
  yl : ℝ
  yu : ℝ

def RectFootprint.carrier (Q : RectFootprint) : Set (ℝ×ℝ) :=
  Icc Q.xl Q.xu ×ˢ Icc Q.yl Q.yu

def RectFootprint.inter (Q R : RectFootprint) : RectFootprint :=
  ⟨max Q.xl R.xl,min Q.xu R.xu,max Q.yl R.yl,min Q.yu R.yu⟩

lemma RectFootprint.inter_carrier (Q R : RectFootprint) :
    (Q.inter R).carrier=Q.carrier∩R.carrier := by
  ext z
  simp only [RectFootprint.carrier,RectFootprint.inter,mem_prod,mem_Icc,mem_inter_iff,
    max_le_iff,le_min_iff]
  tauto

def RectFootprint.prism (Q : RectFootprint) (lo hi : ℝ) : Set Box3 :=
  Q.carrier ×ˢ Icc lo hi

lemma RectFootprint.prism_compact (Q : RectFootprint) (lo hi : ℝ) :
    IsCompact (Q.prism lo hi) := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

def centralThickness : ℝ := 1/1000
def centralOuterX : ℝ := sourceLength*(1-sourceRadialWidth*centralThickness)
def centralInnerX : ℝ := sourceLength*(sourceHole+sourceRadialWidth*centralThickness)
def centralOuterY : ℝ := 1-sourceRadialWidth*centralThickness
def centralInnerY : ℝ := sourceHole+sourceRadialWidth*centralThickness
def centralHeight : ℝ := 1-centralThickness
def centralChildHeight : ℝ := sourceScale*(1+centralThickness)
def centralChildOuterX : ℝ := sourceScale*(1+sourceRadialWidth*centralThickness)
def centralChildOuterY : ℝ := sourceScale*sourceLength*(1+sourceRadialWidth*centralThickness)
def centralChildInnerX : ℝ := sourceScale*(sourceHole-sourceRadialWidth*centralThickness)
def centralChildInnerY : ℝ := sourceScale*sourceLength*(sourceHole-sourceRadialWidth*centralThickness)

def centralParentStrip (i : Fin 4) : RectFootprint :=
  ![⟨centralInnerX,centralOuterX,-centralOuterY,centralOuterY⟩,
    ⟨-centralOuterX,centralOuterX,centralInnerY,centralOuterY⟩,
    ⟨-centralOuterX,-centralInnerX,-centralOuterY,centralOuterY⟩,
    ⟨-centralOuterX,centralOuterX,-centralOuterY,-centralInnerY⟩] i

def centralChildOption (σ : ℝ) (k : Fin 5) : RectFootprint :=
  ![⟨σ*sourceOffset+centralChildOuterX,centralOuterX,-centralOuterY,centralOuterY⟩,
    ⟨-centralOuterX,centralOuterX,centralChildOuterY,centralOuterY⟩,
    ⟨-centralOuterX,σ*sourceOffset-centralChildOuterX,-centralOuterY,centralOuterY⟩,
    ⟨-centralOuterX,centralOuterX,-centralOuterY,-centralChildOuterY⟩,
    ⟨σ*sourceOffset-centralChildInnerX,σ*sourceOffset+centralChildInnerX,
      -centralChildInnerY,centralChildInnerY⟩] k

def centralParentFootprint (z : ℝ×ℝ) : Prop :=
  |z.1| ≤ centralOuterX ∧ |z.2| ≤ centralOuterY ∧
    (centralInnerX ≤ |z.1| ∨ centralInnerY ≤ |z.2|)

def centralAvoidChild (σ : ℝ) (z : ℝ×ℝ) : Prop :=
  centralChildOuterX ≤ |z.1-σ*sourceOffset| ∨ centralChildOuterY ≤ |z.2| ∨
    (|z.1-σ*sourceOffset| ≤ centralChildInnerX ∧ |z.2| ≤ centralChildInnerY)

lemma centralParentStrip_mem {z : ℝ×ℝ} :
    (∃ i,z∈(centralParentStrip i).carrier) ↔ centralParentFootprint z := by
  simp only [centralParentStrip,Fin.exists_fin_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.exists_fin_zero,or_false,RectFootprint.carrier,mem_prod,mem_Icc,
    centralParentFootprint,abs_le,le_abs]
  have hx : 0 ≤ centralInnerX ∧ centralInnerX ≤ centralOuterX := by
    norm_num [centralInnerX,centralOuterX,sourceLength,sourceHole,sourceRadialWidth,centralThickness]
  have hy : 0 ≤ centralInnerY ∧ centralInnerY ≤ centralOuterY := by
    norm_num [centralInnerY,centralOuterY,sourceHole,sourceRadialWidth,centralThickness]
  constructor
  · rintro (h|h|h|h)
    · exact ⟨⟨by linarith [h.1.1],h.1.2⟩,h.2,Or.inl (Or.inl h.1.1)⟩
    · exact ⟨h.1,⟨by linarith [h.2.1],h.2.2⟩,Or.inr (Or.inl h.2.1)⟩
    · exact ⟨⟨h.1.1,by linarith [h.1.2]⟩,h.2,Or.inl (Or.inr (by linarith [h.1.2]))⟩
    · exact ⟨h.1,⟨h.2.1,by linarith [h.2.2]⟩,Or.inr (Or.inr (by linarith [h.2.2]))⟩
  · intro hp
    rcases hp.2.2 with (h|h)|(h|h)
    · left; exact ⟨⟨h,hp.1.2⟩,hp.2.1⟩
    · right; right; left; exact ⟨⟨hp.1.1,by linarith⟩,hp.2.1⟩
    · right; left; exact ⟨hp.1,⟨h,hp.2.1.2⟩⟩
    · right; right; right; exact ⟨hp.1,⟨hp.2.1.1,by linarith⟩⟩

lemma centralChildOption_mem {σ : ℝ} {z : ℝ×ℝ}
    (hbox : |z.1| ≤ centralOuterX ∧ |z.2| ≤ centralOuterY) :
    (∃ k,z∈(centralChildOption σ k).carrier) ↔ centralAvoidChild σ z := by
  simp only [centralChildOption,Fin.exists_fin_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.exists_fin_zero,or_false,RectFootprint.carrier,mem_prod,mem_Icc,
    centralAvoidChild,abs_le,le_abs]
  have hx := abs_le.mp hbox.1
  have hy := abs_le.mp hbox.2
  constructor
  · rintro (h|h|h|h|h)
    · exact Or.inl (Or.inl (by linarith [h.1.1]))
    · exact Or.inr (Or.inl (Or.inl h.2.1))
    · exact Or.inl (Or.inr (by linarith [h.1.2]))
    · exact Or.inr (Or.inl (Or.inr (by linarith [h.2.2])))
    · exact Or.inr (Or.inr ⟨⟨by linarith [h.1.1],by linarith [h.1.2]⟩,h.2⟩)
  · rintro ((h|h)|(h|h)|h)
    · exact Or.inl ⟨⟨by linarith,hx.2⟩,hy⟩
    · exact Or.inr (Or.inr (Or.inl ⟨⟨hx.1,by linarith⟩,hy⟩))
    · exact Or.inr (Or.inl ⟨hx,⟨h,hy.2⟩⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hx,⟨hy.1,by linarith⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨by linarith [h.1.1],by linarith [h.1.2]⟩,h.2⟩)))

def centralColumn (i : Fin 4) (j k : Fin 5) : RectFootprint :=
  ((centralParentStrip i).inter (centralChildOption 1 j)).inter (centralChildOption (-1) k)

lemma centralColumn_cover {z : ℝ×ℝ} :
    (∃ i j k,z∈(centralColumn i j k).carrier) ↔
      centralParentFootprint z ∧ centralAvoidChild 1 z ∧ centralAvoidChild (-1) z := by
  simp only [centralColumn,RectFootprint.inter_carrier,mem_inter_iff]
  constructor
  · rintro ⟨i,j,k,⟨hp,hj⟩,hk⟩
    have hh := centralParentStrip_mem.mp ⟨i,hp⟩
    exact ⟨hh,(centralChildOption_mem ⟨hh.1,hh.2.1⟩).mp ⟨j,hj⟩,
      (centralChildOption_mem ⟨hh.1,hh.2.1⟩).mp ⟨k,hk⟩⟩
  · rintro ⟨hp,hj,hk⟩
    obtain ⟨i,hi⟩ := centralParentStrip_mem.mpr hp
    obtain ⟨j,hj⟩ := (centralChildOption_mem ⟨hp.1,hp.2.1⟩).mpr hj
    obtain ⟨k,hk⟩ := (centralChildOption_mem ⟨hp.1,hp.2.1⟩).mpr hk
    exact ⟨i,j,k,⟨hi,hj⟩,hk⟩

def centralClosed : Set Box3 := {z | centralParentFootprint z.1 ∧ |z.2| ≤ centralHeight ∧
  (centralChildHeight ≤ |z.2| ∨ (centralAvoidChild 1 z.1 ∧ centralAvoidChild (-1) z.1))}

def centralTop (i : Fin 4) : Set Box3 :=
  (centralParentStrip i).prism centralChildHeight centralHeight

def centralBottom (i : Fin 4) : Set Box3 :=
  (centralParentStrip i).prism (-centralHeight) (-centralChildHeight)

theorem centralClosed_cover : centralClosed =
    (⋃ i,centralTop i) ∪ (⋃ i,centralBottom i) ∪
      ⋃ i : Fin 4,⋃ j : Fin 5,⋃ k : Fin 5,(centralColumn i j k).prism (-centralHeight) centralHeight := by
  ext z
  simp only [centralClosed,mem_ofPred_eq,mem_union,mem_iUnion,centralTop,centralBottom,
    RectFootprint.prism,mem_prod,mem_Icc]
  constructor
  · rintro ⟨hp,hz,ht|⟨hj,hk⟩⟩
    · obtain ⟨i,hi⟩ := centralParentStrip_mem.mpr hp
      have hb := abs_le.mp hz
      rcases le_abs.mp ht with h|h
      · exact Or.inl (Or.inl ⟨i,hi,h,hb.2⟩)
      · exact Or.inl (Or.inr ⟨i,hi,hb.1,by linarith⟩)
    · obtain ⟨i,j,k,hh⟩ := centralColumn_cover.mpr ⟨hp,hj,hk⟩
      exact Or.inr ⟨i,j,k,hh,abs_le.mp hz⟩
  · rintro ((⟨i,hi,hz⟩|⟨i,hi,hz⟩)|⟨i,j,k,hi,hz⟩)
    · refine ⟨centralParentStrip_mem.mp ⟨i,hi⟩,abs_le.mpr ⟨?_,hz.2⟩,Or.inl (le_abs.mpr (Or.inl hz.1))⟩
      have hh : 0 ≤ centralChildHeight+centralHeight := by norm_num [centralChildHeight,centralHeight,sourceScale,centralThickness]
      linarith
    · refine ⟨centralParentStrip_mem.mp ⟨i,hi⟩,abs_le.mpr ⟨hz.1,?_⟩,Or.inl (le_abs.mpr (Or.inr (by linarith [hz.2])))⟩
      have hh : 0 ≤ centralChildHeight+centralHeight := by norm_num [centralChildHeight,centralHeight,sourceScale,centralThickness]
      linarith
    · have hh := centralColumn_cover.mp ⟨i,j,k,hi⟩
      exact ⟨hh.1,abs_le.mpr hz,Or.inr hh.2⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_ExtendedCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def sourceExtendedBox (l r : ℝ) : Set (Fin 3 → ℝ) := Icc ![l,-1,-1] ![r,1,1]

lemma mem_sourceExtendedBox {l r : ℝ} {x : Fin 3 → ℝ} :
    x∈sourceExtendedBox l r ↔ x 0∈Icc l r ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1 := by
  simp [sourceExtendedBox,mem_Icc,Pi.le_def,Fin.forall_fin_succ,abs_le]
  tauto

def sourcePairCoordinates (y : Fin 3 → ℝ) : Box3 := ((y 0,y 1),y 2)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CentralChildCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def sourceChildCoordinates (σ : ℝ) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![sourceScale*y 1+σ*sourceOffset,sourceScale*y 0,sourceScale*y 2]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusNonresonance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory

def torusQuadratic (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) : ℝ :=
  s 0*(h 0 : ℝ)^2+2*s 1*(h 0 : ℝ)*(h 1 : ℝ)+s 2*(h 1 : ℝ)^2

end

open Set

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

def torusRate (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) : ℝ := √(torusQuadratic s h)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_RectangularRayTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def rayDirection (θ : UnitAddCircle) : Fin 2 → ℝ :=
  ![(fourier 1 θ).re,(fourier 1 θ).im]

def rayDenominator (w : ℝ) (θ : UnitAddCircle) : ℝ :=
  max (|rayDirection θ 0|/w) |rayDirection θ 1|

def rectangularRay (w : ℝ) (θ : UnitAddCircle) : Fin 2 → ℝ :=
  fun i => rayDirection θ i/rayDenominator w θ

lemma rayDirection_unit (θ : UnitAddCircle) :
    (rayDirection θ 0)^2+(rayDirection θ 1)^2=1 := by
  have hh : ‖fourier 1 θ‖=1 := by simp [fourier_apply,Circle.norm_coe]
  have hs := Complex.sq_norm (fourier 1 θ)
  rw [hh,Complex.normSq_apply] at hs
  simpa [rayDirection,pow_two] using hs.symm

lemma rayDirection_abs (θ : UnitAddCircle) (i : Fin 2) :
    |rayDirection θ i|≤1 := by
  have hh : ‖fourier 1 θ‖=1 := by simp [fourier_apply,Circle.norm_coe]
  fin_cases i
  · exact (Complex.abs_re_le_norm (fourier 1 θ)).trans_eq hh
  · exact (Complex.abs_im_le_norm (fourier 1 θ)).trans_eq hh

lemma rayDenominator_lower {w : ℝ} (hw : 0<w) (hw' : w≤1) (θ : UnitAddCircle) :
    1/2 ≤ rayDenominator w θ := by
  have h0 : |rayDirection θ 0| ≤ rayDenominator w θ := by
    apply le_trans _ (le_max_left _ _)
    exact (le_div_iff₀ hw).mpr (mul_le_of_le_one_right (abs_nonneg _) hw')
  have h1 : |rayDirection θ 1| ≤ rayDenominator w θ := le_max_right _ _
  have hd : 0 ≤ rayDenominator w θ := (abs_nonneg _).trans h1
  have hh := rayDirection_unit θ
  have h0' := sq_abs (rayDirection θ 0)
  have h1' := sq_abs (rayDirection θ 1)
  nlinarith [sq_nonneg (rayDenominator w θ-|rayDirection θ 0|),
    sq_nonneg (rayDenominator w θ-|rayDirection θ 1|),
    mul_self_le_mul_self (abs_nonneg _) h0,mul_self_le_mul_self (abs_nonneg _) h1]

lemma continuous_rayDirection : Continuous rayDirection := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp (fourier 1).continuous
  · exact Complex.continuous_im.comp (fourier 1).continuous

lemma continuous_rectangularRay {w : ℝ} (hw : 0<w) (hw' : w≤1) :
    Continuous (rectangularRay w) := by
  have hd : Continuous (rayDenominator w) :=
    (((continuous_apply 0).comp continuous_rayDirection).abs.div_const w).max
      (((continuous_apply 1).comp continuous_rayDirection).abs)
  apply continuous_pi
  intro i
  exact (((continuous_apply i).comp continuous_rayDirection).div hd
    (fun θ => ne_of_gt (lt_of_lt_of_le (by norm_num) (rayDenominator_lower hw hw' θ))))

lemma fourier_one_translation_bound (θ : UnitAddCircle) (t : ℝ) :
    ‖fourier 1 (θ+(t:UnitAddCircle))-fourier 1 θ‖≤2*Real.pi*|t| := by
  have he : fourier 1 (θ+(t:UnitAddCircle))=fourier 1 θ*fourier 1 (t:UnitAddCircle) := by
    simp [fourier_apply,AddCircle.toCircle_add,Circle.coe_mul]
  rw [he,←mul_sub_one,norm_mul]
  have hh : ‖fourier 1 θ‖=1 := by simp [fourier_apply,Circle.norm_coe]
  rw [hh,one_mul,fourier_coe_apply]
  have hx := Real.norm_exp_I_mul_ofReal_sub_one_le (x:=2*Real.pi*t)
  have he' : (2*Real.pi*Complex.I*(1:ℤ)*(t:ℂ))=
      Complex.I*((2*Real.pi*t:ℝ):ℂ) := by push_cast; ring
  rw [←he'] at hx
  simpa only [Int.cast_one,Complex.ofReal_one,mul_one,div_one,Real.norm_eq_abs,abs_mul,
    abs_of_pos Real.pi_pos,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] using hx

lemma rayDirection_difference (θ : UnitAddCircle) (t : ℝ) (i : Fin 2) :
    |rayDirection (θ+(t:UnitAddCircle)) i-rayDirection θ i|≤2*Real.pi*|t| := by
  apply le_trans _ (fourier_one_translation_bound θ t)
  fin_cases i
  · simpa [rayDirection] using Complex.abs_re_le_norm
      (fourier 1 (θ+(t:UnitAddCircle))-fourier 1 θ)
  · simpa [rayDirection] using Complex.abs_im_le_norm
      (fourier 1 (θ+(t:UnitAddCircle))-fourier 1 θ)

lemma rayDenominator_difference {w : ℝ} (hw : 0<w) (hw' : w≤1)
    (θ : UnitAddCircle) (t : ℝ) :
    |rayDenominator w (θ+(t:UnitAddCircle))-rayDenominator w θ|≤
      (2*Real.pi*|t|)/w := by
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le
  · rw [←sub_div,abs_div,abs_of_pos hw]
    exact div_le_div_of_nonneg_right ((abs_abs_sub_abs_le _ _).trans
      (rayDirection_difference θ t 0)) hw.le
  · apply ((abs_abs_sub_abs_le _ _).trans (rayDirection_difference θ t 1)).trans
    exact (le_div_iff₀ hw).mpr (mul_le_of_le_one_right (by positivity) hw')

lemma rectangularRay_difference {w : ℝ} (hw : 0<w) (hw' : w≤1)
    (θ : UnitAddCircle) (t : ℝ) (i : Fin 2) :
    |rectangularRay w (θ+(t:UnitAddCircle)) i-rectangularRay w θ i|≤
      (2+4/w)*(2*Real.pi*|t|) := by
  let A := rayDenominator w (θ+(t:UnitAddCircle))
  let B := rayDenominator w θ
  have hA : 1/2≤A := rayDenominator_lower hw hw' _
  have hB : 1/2≤B := rayDenominator_lower hw hw' _
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  let x := rayDirection (θ+(t:UnitAddCircle)) i
  let y := rayDirection θ i
  let K := 2*Real.pi*|t|
  have hK : 0≤K := by dsimp [K]; positivity
  have hD : |x-y|≤K := rayDirection_difference θ t i
  have hy : |y|≤1 := rayDirection_abs θ i
  have hAB : |A-B|≤K/w := rayDenominator_difference hw hw' θ t
  have he : x/A-y/B=(x-y)/A+y*(B-A)/(A*B) := by field_simp; ring
  change |x/A-y/B|≤(2+4/w)*K
  rw [he]
  apply (abs_add_le _ _).trans
  have hb1 : |(x-y)/A|≤2*K := by
    rw [abs_div,abs_of_pos hAp]
    apply (div_le_iff₀ hAp).mpr
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hA)]
  have hb2 : |y*(B-A)/(A*B)|≤4*(K/w) := by
    rw [abs_div,abs_mul,abs_sub_comm,abs_of_pos (mul_pos hAp hBp)]
    apply (div_le_iff₀ (mul_pos hAp hBp)).mpr
    have hh := mul_le_mul hy hAB (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hAB' : 1/4≤A*B := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
    have hKw : 0≤K/w := div_nonneg hK hw.le
    nlinarith [mul_nonneg hKw (sub_nonneg.mpr hAB')]
  calc
    _≤2*K+4*(K/w) := add_le_add hb1 hb2
    _=(2+4/w)*K := by ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance instMeasureSpaceUnitAddCircle_solutions : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsAddHaarMeasureUnitAddCircleVolume_solutions : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma mFourier_spatial_add {d : Type*} [Fintype d] (h : d → ℤ)
    (x y : UnitAddTorus d) : mFourier h (x+y)=mFourier h x*mFourier h y := by
  simp only [mFourier,ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,
    smul_add,AddCircle.toCircle_add,Circle.coe_mul,Finset.prod_mul_distrib]

lemma mFourierCoeff_translation {d : Type*} [Fintype d]
    (f : UnitAddTorus d → ℂ) (b : UnitAddTorus d) (h : d → ℤ) :
    mFourierCoeff (fun x => f (x+b)) h=mFourier h b*mFourierCoeff f h := by
  have hh := integral_add_right_eq_self (μ:=(volume : Measure (UnitAddTorus d)))
    (fun x => mFourier (-h) x*f x) b
  change (∫ x,mFourier (-h) x*f (x+b))=mFourier h b*(∫ x,mFourier (-h) x*f x)
  rw [←hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [mFourier_spatial_add]
  have hz : mFourier h b*mFourier (-h) b=1 := by
    rw [←mFourier_add]
    simp only [add_neg_cancel,mFourier_zero,ContinuousMap.one_apply]
  calc
    _=mFourier (-h) x*f (x+b)*1 := by ring
    _=mFourier (-h) x*f (x+b)*(mFourier h b*mFourier (-h) b) := by rw [hz]
    _=_ := by ring

def torusCoordinateShift (j : Fin 2) (t : ℝ) : UnitAddTorus (Fin 2) :=
  fun i => if i=j then (t : UnitAddCircle) else 0

lemma mFourier_coordinateShift (h : Fin 2 → ℤ) (j : Fin 2) (t : ℝ) :
    mFourier h (torusCoordinateShift j t)=
      Complex.exp (2*Real.pi*Complex.I*(h j)*t) := by
  fin_cases j <;> simp [mFourier,torusCoordinateShift,Fin.prod_univ_two]

lemma mFourierCoeff_difference (f g : C(UnitAddTorus (Fin 2),ℂ)) (h : Fin 2 → ℤ) :
    mFourierCoeff (f-g) h=mFourierCoeff f h-mFourierCoeff g h := by
  unfold mFourierCoeff
  simp only [ContinuousMap.coe_sub,Pi.sub_apply,smul_sub]
  apply integral_sub
  · exact ((mFourier (-h)).continuous.smul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((mFourier (-h)).continuous.smul g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma torus_fourier_difference_bessel (f : C(UnitAddTorus (Fin 2),ℂ))
    (j : Fin 2) (t : ℝ) (s : Finset (Fin 2 → ℤ)) :
    ∑ h∈s,‖(Complex.exp (2*Real.pi*Complex.I*(h j)*t)-1)*mFourierCoeff f h‖^2 ≤
      ∫ x : UnitAddTorus (Fin 2), ‖f (x+torusCoordinateShift j t)-f x‖^2 := by
  let g : C(UnitAddTorus (Fin 2),ℂ) :=
    (f.comp ⟨fun x => x+torusCoordinateShift j t,continuous_id.add continuous_const⟩)-f
  have hg (h : Fin 2 → ℤ) : mFourierCoeff g h=
      (Complex.exp (2*Real.pi*Complex.I*(h j)*t)-1)*mFourierCoeff f h := by
    rw [mFourierCoeff_difference]
    change mFourierCoeff (fun x => f (x+torusCoordinateShift j t)) h-_=_
    rw [mFourierCoeff_translation,mFourier_coordinateShift]; ring
  have hlp := hasSum_sq_mFourierCoeff (ContinuousMap.toLp 2 volume ℂ g)
  have he : ∫ x : UnitAddTorus (Fin 2),‖(ContinuousMap.toLp 2 volume ℂ g : UnitAddTorus (Fin 2) → ℂ) x‖^2=
      ∫ x : UnitAddTorus (Fin 2),‖g x‖^2 := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜:=ℂ) (p:=2) volume g] with x hx
    rw [hx]
  rw [he] at hlp
  simp only [mFourierCoeff_toLp,hg] at hlp
  exact sum_le_hasSum s (fun _ _ => sq_nonneg _) hlp

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance instMeasureSpaceUnitAddCircle_solutions_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torus_phase_difference_limit (n : ℤ) :
    Tendsto (fun t : ℝ => ‖t⁻¹ •
      (Complex.exp (2*Real.pi*Complex.I*n*t)-1)‖^2) (𝓝[≠] (0:ℝ))
      (𝓝 ((2*Real.pi*(n:ℝ))^2)) := by
  have hd := (((hasDerivAt_id (0:ℝ)).ofReal_comp).const_mul
    (2*Real.pi*Complex.I*(n:ℂ))).cexp
  have hl := hd.tendsto_slope_zero.norm.pow 2
  simpa only [id_eq,zero_add,Complex.ofReal_zero,mul_zero,Complex.exp_zero,
    mul_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one,
    Complex.norm_intCast,mul_pow,sq_abs,norm_one,one_pow,one_mul,abs_one] using hl

lemma torus_difference_integral_bound (f : C(UnitAddTorus (Fin 2),ℂ))
    (j : Fin 2) (K : ℝ) (hK : 0≤K)
    (hf : ∀ t x,‖f (x+torusCoordinateShift j t)-f x‖≤K*|t|) (t : ℝ) :
    (∫ x : UnitAddTorus (Fin 2), ‖f (x+torusCoordinateShift j t)-f x‖^2)≤K^2*t^2 := by
  have hint : Integrable (fun x : UnitAddTorus (Fin 2) =>
      ‖f (x+torusCoordinateShift j t)-f x‖^2) volume :=
    ((f.continuous.comp (continuous_id.add continuous_const)).sub f.continuous).norm.pow 2
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _≤∫ _ : UnitAddTorus (Fin 2),(K*|t|)^2 := by
      apply integral_mono hint (integrable_const _)
      intro x
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (abs_nonneg t))).mpr (hf t x)
    _=K^2*t^2 := by simp [mul_pow,sq_abs]

lemma torus_coordinate_fourier_bound (f : C(UnitAddTorus (Fin 2),ℂ))
    (j : Fin 2) (K : ℝ) (hK : 0≤K)
    (hf : ∀ t x,‖f (x+torusCoordinateShift j t)-f x‖≤K*|t|)
    (s : Finset (Fin 2 → ℤ)) :
    ∑ h∈s,(2*Real.pi*(h j:ℝ))^2*‖mFourierCoeff f h‖^2≤K^2 := by
  have hl := tendsto_finsetSum s (fun h _ =>
    (torus_phase_difference_limit (h j)).mul_const (‖mFourierCoeff f h‖^2))
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t≠0 := ht
  have hb := (torus_fourier_difference_bessel f j t s).trans
    (torus_difference_integral_bound f j K hK hf t)
  have hs := mul_le_mul_of_nonneg_left hb (sq_nonneg t⁻¹)
  calc
    _=t⁻¹^2*∑ h∈s,‖(Complex.exp (2*Real.pi*Complex.I*(h j)*t)-1)*
        mFourierCoeff f h‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      simp only [norm_smul,Real.norm_eq_abs,norm_mul,mul_pow,sq_abs]
      ring
    _≤t⁻¹^2*(K^2*t^2) := hs
    _=K^2 := by field_simp

theorem torus_coordinate_fourier_summable (f : C(UnitAddTorus (Fin 2),ℂ))
    (j : Fin 2) (K : ℝ) (hK : 0≤K)
    (hf : ∀ t x,‖f (x+torusCoordinateShift j t)-f x‖≤K*|t|) :
    Summable (fun h : Fin 2 → ℤ => (2*Real.pi*(h j:ℝ))^2*‖mFourierCoeff f h‖^2) := by
  apply summable_of_sum_le (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact torus_coordinate_fourier_bound f j K hK hf

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WeightedSpectralSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped ENNReal

abbrev SpectralL2 (ι : Type*) := lp (fun _ : ι => ℂ) 2
abbrev SpectralJet (ι : Type*) := PiLp 2 (fun _ : Fin 2 => SpectralL2 ι)

def spectralTraceGraph {ι : Type*} (w : ι → ℝ) : Submodule ℂ (SpectralJet ι) where
  carrier := {z | ∀ i, (z 1) i=(Real.sqrt (w i):ℂ)*(z 0) i}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro x y hx hy i
    change (x 1) i+(y 1) i=(Real.sqrt (w i):ℂ)*((x 0) i+(y 0) i)
    rw [hx i,hy i,mul_add]
  smul_mem' := by
    intro c x hx i
    change c*((x 1) i)=(Real.sqrt (w i):ℂ)*(c*((x 0) i))
    rw [hx i]; ring

lemma spectralTraceGraph_fst_injective {ι : Type*} (w : ι → ℝ) :
    Function.Injective (fun z : spectralTraceGraph w => z.val 0) := by
  intro x y h
  apply Subtype.ext
  apply PiLp.ext
  intro j
  fin_cases j
  · exact h
  · ext i
    exact (x.property i).trans ((congrArg (fun f : SpectralL2 ι =>
      (Real.sqrt (w i):ℂ)*f i) h).trans (y.property i).symm)

lemma sqrt_weight_norm_sq {ι : Type*} {w : ι → ℝ} (hw : ∀ i,0≤w i)
    (f : SpectralL2 ι) (i : ι) :
    ‖(Real.sqrt (w i):ℂ)*f i‖^2=w i*‖f i‖^2 := by
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hw i)]

lemma spectralTraceGraph_exists_iff {ι : Type*} {w : ι → ℝ} (hw : ∀ i,0≤w i)
    (f : SpectralL2 ι) :
    (∃ z : spectralTraceGraph w, z.val 0=f) ↔ Summable (fun i => w i*‖f i‖^2) := by
  constructor
  · rintro ⟨z,hz⟩
    have hh := (lp.memℓp (z.val 1)).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hh
    have he (i : ι) : ‖(z.val 1) i‖^2=w i*‖f i‖^2 := by
      rw [z.property i,hz]
      exact sqrt_weight_norm_sq hw f i
    simpa only [he] using hh
  · intro hs
    have hm : Memℓp (fun i => (Real.sqrt (w i):ℂ)*f i) 2 := by
      apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,sqrt_weight_norm_sq hw f] using hs
    let g : SpectralL2 ι := ⟨_,hm⟩
    refine ⟨⟨WithLp.toLp 2 ![f,g],?_⟩,?_⟩
    · intro i; rfl
    · rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusLipschitzTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance instMeasureSpaceUnitAddCircle_solutions_2 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_2 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torus_coordinate_H1_summable (f : C(UnitAddTorus (Fin 2),ℂ))
    (K : Fin 2 → ℝ) (hK : ∀ j,0≤K j)
    (hf : ∀ j t x,‖f (x+torusCoordinateShift j t)-f x‖≤K j*|t|) :
    Summable (fun h : Fin 2 → ℤ =>
      (1+(h 0:ℝ)^2+(h 1:ℝ)^2)*‖mFourierCoeff f h‖^2) := by
  have h0 : Summable (fun h : Fin 2 → ℤ => ‖mFourierCoeff f h‖^2) := by
    simpa only [mFourierCoeff_toLp] using
      (hasSum_sq_mFourierCoeff (ContinuousMap.toLp 2 volume ℂ f)).summable
  have hj (j : Fin 2) : Summable (fun h : Fin 2 → ℤ => (h j:ℝ)^2*‖mFourierCoeff f h‖^2) := by
    have hh := (torus_coordinate_fourier_summable f j (K j) (hK j) (hf j)).mul_left ((2*Real.pi)^2)⁻¹
    apply hh.congr
    intro h
    have hp : Real.pi≠0 := Real.pi_pos.ne'
    field_simp
  apply ((h0.add (hj 0)).add (hj 1)).congr
  intro h
  ring

lemma torusRate_polynomial_bound (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    torusRate s h≤(1+|s 0|+|s 1|+|s 2|)*(1+(h 0:ℝ)^2+(h 1:ℝ)^2) := by
  let C := 1+|s 0|+|s 1|+|s 2|
  let B := (h 0:ℝ)^2+(h 1:ℝ)^2
  have hC : 1≤C := by dsimp [C]; linarith [abs_nonneg (s 0),abs_nonneg (s 1),abs_nonneg (s 2)]
  have hB : 0≤B := by dsimp [B]; positivity
  have hcross : 2*s 1*(h 0:ℝ)*(h 1:ℝ)≤|s 1| * B := by
    have hab : 2*|(h 0:ℝ)| * |(h 1:ℝ)| ≤ B := by
      dsimp [B]
      nlinarith [sq_nonneg (|(h 0:ℝ)|-|(h 1:ℝ)|),sq_abs (h 0:ℝ),sq_abs (h 1:ℝ)]
    calc
      _≤|2*s 1*(h 0:ℝ)*(h 1:ℝ)| := le_abs_self _
      _=|s 1| * (2*|(h 0:ℝ)| * |(h 1:ℝ)|) := by rw [abs_mul,abs_mul,abs_mul]; norm_num; ring
      _≤|s 1| * B := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
  have hQ : torusQuadratic s h≤C*B := by
    have hx := mul_le_mul_of_nonneg_right (le_abs_self (s 0)) (sq_nonneg (h 0:ℝ))
    have hy := mul_le_mul_of_nonneg_right (le_abs_self (s 2)) (sq_nonneg (h 1:ℝ))
    have hx' : |s 0| * (h 0:ℝ)^2≤|s 0| * B := mul_le_mul_of_nonneg_left
      (by dsimp [B]; nlinarith [sq_nonneg (h 1:ℝ)]) (abs_nonneg _)
    have hy' : |s 2| * (h 1:ℝ)^2≤|s 2| * B := mul_le_mul_of_nonneg_left
      (by dsimp [B]; nlinarith [sq_nonneg (h 0:ℝ)]) (abs_nonneg _)
    dsimp [torusQuadratic,C]
    nlinarith
  have hroot : torusRate s h≤1+max (torusQuadratic s h) 0 := by
    dsimp [torusRate]
    by_cases hq : 0≤torusQuadratic s h
    · rw [max_eq_left hq]
      have hh := Real.sq_sqrt hq
      nlinarith [sq_nonneg (Real.sqrt (torusQuadratic s h)-1)]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hq),max_eq_right (le_of_not_ge hq)]
      norm_num
  have hm : max (torusQuadratic s h) 0≤C*B := max_le hQ (mul_nonneg (by linarith) hB)
  change torusRate s h≤C*(1+(h 0:ℝ)^2+(h 1:ℝ)^2)
  calc
    _≤1+C*B := hroot.trans (add_le_add (le_refl 1) hm)
    _≤C*(1+(h 0:ℝ)^2+(h 1:ℝ)^2) := by dsimp [B] at *; nlinarith

theorem torus_coordinate_trace_summable (s : Fin 3 → ℝ)
    (f : C(UnitAddTorus (Fin 2),ℂ)) (K : Fin 2 → ℝ) (hK : ∀ j,0≤K j)
    (hf : ∀ j t x,‖f (x+torusCoordinateShift j t)-f x‖≤K j*|t|) :
    Summable (fun h : Fin 2 → ℤ => torusRate s h*‖mFourierCoeff f h‖^2) := by
  refine ((torus_coordinate_H1_summable f K hK hf).mul_left (1+|s 0|+|s 1|+|s 2|)).of_nonneg_of_le
    (fun h => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (fun h => ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (torusRate_polynomial_bound s h) (sq_nonneg _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma rectangularRay_abs {w : ℝ} (hw : 0<w) (hw' : w≤1)
    (θ : UnitAddCircle) (i : Fin 2) : |rectangularRay w θ i|≤2 := by
  have hd := rayDenominator_lower hw hw' θ
  have hp : 0 < rayDenominator w θ := by linarith
  rw [rectangularRay,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  linarith [rayDirection_abs θ i]

lemma rectangularRay_coordinate_bound {w : ℝ} (hw : 0<w) (hw' : w≤1)
    (x : UnitAddTorus (Fin 2)) (j k i : Fin 2) (t : ℝ) :
    |rectangularRay w ((x+torusCoordinateShift j t) k) i-rectangularRay w (x k) i|≤
      ((2+4/w)*(2*Real.pi))*|t| := by
  by_cases h : k=j
  · subst k
    simpa [torusCoordinateShift,mul_assoc] using rectangularRay_difference hw hw' (x j) t i
  · simp only [Pi.add_apply,torusCoordinateShift,ite_eq_right h,add_zero,sub_self,abs_zero]
    positivity

def sourceRayCoordinates (x : UnitAddTorus (Fin 2)) : Fin 4 → ℝ :=
  ![rectangularRay 1 (x 0) 0,rectangularRay 1 (x 0) 1,
    rectangularRay sourceRadialWidth (x 1) 0,rectangularRay sourceRadialWidth (x 1) 1]

def sourceRayBox : Set (Fin 4 → ℝ) := Icc (fun _ => -2) (fun _ => 2)

lemma sourceRayCoordinates_mem (x : UnitAddTorus (Fin 2)) : sourceRayCoordinates x∈sourceRayBox := by
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hw' : sourceRadialWidth≤1 := by norm_num [sourceRadialWidth,sourceHole]
  have h (i : Fin 4) : |sourceRayCoordinates x i|≤2 := by
    fin_cases i
    · exact rectangularRay_abs (by norm_num) (by norm_num) _ _
    · exact rectangularRay_abs (by norm_num) (by norm_num) _ _
    · exact rectangularRay_abs hw hw' _ _
    · exact rectangularRay_abs hw hw' _ _
  exact ⟨fun i => (abs_le.mp (h i)).1,fun i => (abs_le.mp (h i)).2⟩

lemma continuous_sourceRayCoordinates : Continuous sourceRayCoordinates := by
  have hc1 := continuous_rectangularRay (w:=1) (by norm_num) (by norm_num)
  have hcw := continuous_rectangularRay (w:=sourceRadialWidth)
    (by norm_num [sourceRadialWidth,sourceHole]) (by norm_num [sourceRadialWidth,sourceHole])
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [sourceRayCoordinates]
  · exact (continuous_apply (0 : Fin 2)).comp (hc1.comp (continuous_apply (0 : Fin 2)))
  · exact (continuous_apply (1 : Fin 2)).comp (hc1.comp (continuous_apply (0 : Fin 2)))
  · exact (continuous_apply (0 : Fin 2)).comp (hcw.comp (continuous_apply (1 : Fin 2)))
  · exact (continuous_apply (1 : Fin 2)).comp (hcw.comp (continuous_apply (1 : Fin 2)))

def sourceRayConstant : ℝ := 6*(2*Real.pi)+(2+4/sourceRadialWidth)*(2*Real.pi)

lemma sourceRayConstant_nonneg : 0≤ sourceRayConstant := by
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  unfold sourceRayConstant
  positivity

lemma sourceRayCoordinates_difference (j : Fin 2) (t : ℝ) (x : UnitAddTorus (Fin 2)) :
    ‖sourceRayCoordinates (x+torusCoordinateShift j t)-sourceRayCoordinates x‖≤ sourceRayConstant*|t| := by
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hw' : sourceRadialWidth≤1 := by norm_num [sourceRadialWidth,sourceHole]
  have h1 : (2+4/(1:ℝ))*(2*Real.pi)≤ sourceRayConstant := by
    dsimp [sourceRayConstant]
    norm_num
    positivity
  have h2 : (2+4/sourceRadialWidth)*(2*Real.pi)≤ sourceRayConstant := by
    dsimp [sourceRayConstant]
    linarith [Real.pi_pos]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg sourceRayConstant_nonneg (abs_nonneg _))).mpr
  intro i
  change |sourceRayCoordinates (x+torusCoordinateShift j t) i-sourceRayCoordinates x i|≤_
  fin_cases i
  · exact (rectangularRay_coordinate_bound (w:=1) (by norm_num) (by norm_num) x j 0 0 t).trans
      (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
  · exact (rectangularRay_coordinate_bound (w:=1) (by norm_num) (by norm_num) x j 0 1 t).trans
      (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
  · exact (rectangularRay_coordinate_bound hw hw' x j 1 0 t).trans
      (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
  · exact (rectangularRay_coordinate_bound hw hw' x j 1 1 t).trans
      (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))

def sourceAngularPolynomial (t : ℝ) (z : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![sourceLength*(sourceRadialCenter+(1-t)*z 2)*z 0,
    (sourceRadialCenter+(1-t)*z 2)*z 1,(1-t)*z 3]

def sourceAngularCollar (t : ℝ) (x : UnitAddTorus (Fin 2)) : Fin 3 → ℝ :=
  sourceAngularPolynomial t (sourceRayCoordinates x)

lemma contDiff_sourceAngularPolynomial (t : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (sourceAngularPolynomial t) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [sourceAngularPolynomial] <;> fun_prop

lemma continuous_sourceAngularCollar (t : ℝ) : Continuous (sourceAngularCollar t) :=
  (contDiff_sourceAngularPolynomial t).continuous.comp continuous_sourceRayCoordinates

theorem sourceAngularTrace_summable (s : Fin 3 → ℝ) (t : ℝ) {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    Summable (fun h : Fin 2 → ℤ => torusRate s h*
      ‖mFourierCoeff (fun x => (f (sourceAngularCollar t x):ℂ)) h‖^2) := by
  let G : (Fin 4 → ℝ) → ℂ := fun z => (f (sourceAngularPolynomial t z):ℂ)
  have hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G := by
    exact Complex.ofRealCLM.contDiff.comp (hf.comp (contDiff_sourceAngularPolynomial t))
  obtain ⟨K,hK⟩ := hG.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_Icc _ _) isCompact_Icc
  let F : C(UnitAddTorus (Fin 2),ℂ) :=
    ⟨fun x => G (sourceRayCoordinates x),hG.continuous.comp continuous_sourceRayCoordinates⟩
  have hdiff (j : Fin 2) (u : ℝ) (x : UnitAddTorus (Fin 2)) :
      ‖F (x+torusCoordinateShift j u)-F x‖≤((K:ℝ)*sourceRayConstant)*|u| := by
    have hh := hK.dist_le_mul _ (sourceRayCoordinates_mem (x+torusCoordinateShift j u))
      _ (sourceRayCoordinates_mem x)
    rw [dist_eq_norm,dist_eq_norm] at hh
    apply hh.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (sourceRayCoordinates_difference j u x) K.coe_nonneg
  exact torus_coordinate_trace_summable s F (fun _ => (K:ℝ)*sourceRayConstant)
    (fun _ => mul_nonneg K.coe_nonneg sourceRayConstant_nonneg) hdiff

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularNormalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma rayDirection_coe_angle (a : ℝ) :
    rayDirection ((a/(2*Real.pi):ℝ):UnitAddCircle)=![Real.cos a,Real.sin a] := by
  have he : fourier 1 ((a/(2*Real.pi):ℝ):UnitAddCircle)=Complex.exp ((a:ℂ)*Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    field_simp
  ext i
  fin_cases i
  · simp [rayDirection,he]
  · simp [rayDirection,he]

lemma rectangularRay_of_direction {w k : ℝ} (hw : 0<w) (hk : 0<k)
    (θ : UnitAddCircle) (j : Fin 4) {b : ℝ} (hb : |b|≤1)
    (he : rayDirection θ=k • ![w*squareFace j b 0,squareFace j b 1]) :
    rectangularRay w θ=![w*squareFace j b 0,squareFace j b 1] := by
  have hd : rayDenominator w θ=k := by
    dsimp [rayDenominator]
    rw [he]
    simp only [Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
      abs_mul,abs_of_pos hk,abs_of_pos hw]
    have he' : k*(w*|squareFace j b 0|)/w=k*|squareFace j b 0| := by field_simp
    rw [he',←mul_max_of_nonneg _ _ hk.le,squareFace_max j hb,mul_one]
  ext i
  rw [rectangularRay,he,hd]
  simp only [Pi.smul_apply,smul_eq_mul]
  exact mul_div_cancel_left₀ _ hk.ne'

def faceRayAngle (w : ℝ) (j : Fin 4) (b : ℝ) : ℝ :=
  ![Real.arctan (b/w),Real.pi/2+Real.arctan (w*b),
    Real.pi+Real.arctan (b/w),3*Real.pi/2+Real.arctan (w*b)] j/(2*Real.pi)

lemma faceRayAngle_image {w : ℝ} (hw : 0<w) (j : Fin 4) {b : ℝ} (hb : |b|≤1) :
    rectangularRay w ((faceRayAngle w j b:ℝ):UnitAddCircle)=
      ![w*squareFace j b 0,squareFace j b 1] := by
  have hp (x : ℝ) : 0<Real.sqrt (1+x^2) := Real.sqrt_pos.mpr (by positivity)
  fin_cases j
  · apply rectangularRay_of_direction hw (k:=(w*Real.sqrt (1+(b/w)^2))⁻¹)
      (inv_pos.mpr (mul_pos hw (hp _))) _ 0 hb
    dsimp only [faceRayAngle]
    rw [rayDirection_coe_angle]
    ext i; fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,
      Real.cos_arctan,Real.sin_arctan] <;> field_simp
  · apply rectangularRay_of_direction hw (k:=(Real.sqrt (1+(w*b)^2))⁻¹)
      (inv_pos.mpr (hp _)) _ 1 hb
    dsimp only [faceRayAngle]
    rw [rayDirection_coe_angle]
    ext i; fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,
      Real.cos_add,Real.sin_add,Real.cos_arctan,Real.sin_arctan]; ring
  · apply rectangularRay_of_direction hw (k:=(w*Real.sqrt (1+(b/w)^2))⁻¹)
      (inv_pos.mpr (mul_pos hw (hp _))) _ 2 hb
    dsimp only [faceRayAngle]
    rw [rayDirection_coe_angle]
    ext i; fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,
      Real.cos_add,Real.sin_add,Real.cos_arctan,Real.sin_arctan] <;> field_simp
  · apply rectangularRay_of_direction hw (k:=(Real.sqrt (1+(w*b)^2))⁻¹)
      (inv_pos.mpr (hp _)) _ 3 hb
    dsimp only [faceRayAngle]
    rw [rayDirection_coe_angle]
    have he : 3*Real.pi/2=Real.pi+Real.pi/2 := by ring
    rw [he]
    ext i; fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,
      Real.cos_add,Real.sin_add,Real.cos_arctan,Real.sin_arctan]; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularIntegratedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def sourcePhysicalEnergy (f : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  64*‖fderiv ℝ f y‖^2+2*(f y)^2

lemma continuous_sourcePhysicalEnergy {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : Continuous (sourcePhysicalEnergy f) :=
  (continuous_const.mul ((hf.continuous_fderiv (by simp)).norm.pow 2)).add
    (continuous_const.mul (hf.continuous.pow 2))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildCoordinateAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def sourceChildHomeomorph (σ : ℝ) : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) where
  toFun := sourceChildCoordinates σ
  invFun := fun z => ![z 1/sourceScale,(z 0-σ*sourceOffset)/sourceScale,z 2/sourceScale]
  left_inv := by intro x; ext i; fin_cases i <;> simp [sourceChildCoordinates,sourceScale]
  right_inv := by intro x; ext i; fin_cases i <;> simp [sourceChildCoordinates,sourceScale] <;> ring
  continuous_toFun := by apply continuous_pi; intro i; fin_cases i <;> dsimp [sourceChildCoordinates] <;> fun_prop
  continuous_invFun := by apply continuous_pi; intro i; fin_cases i <;> dsimp <;> fun_prop

def sourceChildJacobian : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0,sourceScale,0],![sourceScale,0,0],![0,0,sourceScale]]

def sourceChildDerivative : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin' sourceChildJacobian).toContinuousLinearMap

lemma sourceChildDerivative_apply (x : Fin 3 → ℝ) :
    sourceChildDerivative x=![sourceScale*x 1,sourceScale*x 0,sourceScale*x 2] := by
  ext i; fin_cases i <;> simp [sourceChildDerivative,sourceChildJacobian,Matrix.toLin',LinearMap.toMatrix',Matrix.mulVecLin,
    Matrix.mulVecBilin,Matrix.mulVec,Fin.sum_univ_succ,dotProduct]

lemma sourceChildCoordinates_contDiff (σ : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (sourceChildCoordinates σ) := by
  apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp [sourceChildCoordinates] <;> fun_prop

lemma sourceChildCoordinates_hasFDeriv (σ : ℝ) (x : Fin 3 → ℝ) :
    HasFDerivAt (sourceChildCoordinates σ) sourceChildDerivative x := by
  have he : sourceChildCoordinates σ=fun y => sourceChildDerivative y+![σ*sourceOffset,0,0] := by
    funext y; rw [sourceChildDerivative_apply]; ext i; fin_cases i <;> simp [sourceChildCoordinates]
  rw [he]
  simpa using sourceChildDerivative.hasFDerivAt.add_const ![σ*sourceOffset,0,0]

lemma sourceChildDerivative_det : sourceChildDerivative.det= -sourceScale^3 := by
  change (Matrix.toLin' sourceChildJacobian).det= -sourceScale^3
  rw [LinearMap.det_toLin',Matrix.det_fin_three]
  simp [sourceChildJacobian]
  ring

lemma integral_sourceChild_preimage (σ : ℝ) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (g : (Fin 3 → ℝ) → ℝ) :
    (∫ x in sourceChildCoordinates σ ⁻¹' K,g (sourceChildCoordinates σ x))=
      (sourceScale^3)⁻¹*(∫ y in K,g y) := by
  have hs : sourceScale≠0 := by norm_num [sourceScale]
  have hc := (sourceChildHomeomorph σ).isCompact_preimage.mpr hK
  have hh := integral_image_eq_integral_abs_det_fderiv_smul volume hc.measurableSet
    (fun x _ => (sourceChildCoordinates_hasFDeriv σ x).hasFDerivWithinAt)
    (sourceChildHomeomorph σ).injective.injOn g
  have him : sourceChildCoordinates σ '' (sourceChildCoordinates σ ⁻¹' K)=K :=
    Set.image_preimage_eq K (sourceChildHomeomorph σ).surjective
  change (∫ x in sourceChildCoordinates σ '' (sourceChildCoordinates σ ⁻¹' K),g x)=
    ∫ x in sourceChildCoordinates σ ⁻¹' K,abs sourceChildDerivative.det • g (sourceChildCoordinates σ x) at hh
  rw [him] at hh
  simp only [sourceChildDerivative_det,abs_neg,abs_pow,abs_of_nonneg (show 0 ≤ sourceScale by norm_num [sourceScale]),
    smul_eq_mul,integral_const_mul] at hh
  norm_num [sourceScale] at hh ⊢
  linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusFaceIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma sourceAngular_face (t a b : ℝ) (i j : Fin 4) (ha : |a|≤1) (hb : |b|≤1) :
    sourceAngularCollar t
      ![((faceRayAngle 1 i a:ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j b:ℝ):UnitAddCircle)]=
      sourceCollarPiece i j ![t,a,b] := by
  have h0 := faceRayAngle_image (w:=1) (by norm_num) i ha
  have h1 := faceRayAngle_image (w:=sourceRadialWidth)
    (by norm_num [sourceRadialWidth,sourceHole]) j hb
  ext k
  fin_cases k <;>
    simp [sourceAngularCollar,sourceAngularPolynomial,sourceRayCoordinates,h0,h1,
      sourceCollarPiece,sourceCollarRadius] <;> ring_nf <;> simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma centralClosed_compact : IsCompact centralClosed := by
  rw [centralClosed_cover]
  exact ((isCompact_iUnion (fun i : Fin 4 => (centralParentStrip i).prism_compact _ _)).union
    (isCompact_iUnion (fun i : Fin 4 => (centralParentStrip i).prism_compact _ _))).union
    (isCompact_iUnion (fun i : Fin 4 => isCompact_iUnion (fun j : Fin 5 =>
      isCompact_iUnion (fun k : Fin 5 => (centralColumn i j k).prism_compact _ _))))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus

def physicalRayConstant : ℝ :=
  1600*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi))

lemma physicalRayConstant_pos : 0<physicalRayConstant := by
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  unfold physicalRayConstant
  positivity

end

open Set MeasureTheory

def sourcePairEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] Box3 where
  toFun := sourcePairCoordinates
  invFun := fun z => ![z.1.1,z.1.2,z.2]
  left_inv := by intro x; ext i; fin_cases i <;> rfl
  right_inv := by intro z; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def sourcePairCLE : (Fin 3 → ℝ) ≃L[ℝ] Box3 := sourcePairEquiv.toContinuousLinearEquiv

lemma linear_three_bound (A : (Fin 3 → ℝ) →L[ℝ] ℝ) :
    ‖A‖^2≤3*((A ![1,0,0])^2+(A ![0,1,0])^2+(A ![0,0,1])^2) := by
  have hn : ‖A‖≤|A ![1,0,0]|+|A ![0,1,0]|+|A ![0,0,1]| := by
    apply A.opNorm_le_bound (by positivity)
    intro v
    have he : v=v 0 • ![1,0,0]+v 1 • ![0,1,0]+v 2 • ![0,0,1] := by
      ext i; fin_cases i <;> simp
    have hh := abs_add_le (A (v 0 • ![1,0,0]+v 1 • ![0,1,0])) (A (v 2 • ![0,0,1]))
    have hh' := abs_add_le (A (v 0 • ![1,0,0])) (A (v 1 • ![0,1,0]))
    have hv (i : Fin 3) : |v i|≤‖v‖ := norm_le_pi_norm v i
    conv_lhs => rw [he]
    rw [map_add,map_add,map_smul,map_smul,map_smul]
    change |v 0 * A ![1,0,0]+v 1*A ![0,1,0]+v 2*A ![0,0,1]|≤_
    have ha := abs_add_le (v 0 * A ![1,0,0]+v 1*A ![0,1,0]) (v 2*A ![0,0,1])
    have hb := abs_add_le (v 0 * A ![1,0,0]) (v 1*A ![0,1,0])
    simp only [abs_mul] at ha hb
    have h0 := mul_le_mul_of_nonneg_right (hv 0) (abs_nonneg (A ![1,0,0]))
    have h1 := mul_le_mul_of_nonneg_right (hv 1) (abs_nonneg (A ![0,1,0]))
    have h2 := mul_le_mul_of_nonneg_right (hv 2) (abs_nonneg (A ![0,0,1]))
    nlinarith
  have hs := mul_self_le_mul_self (norm_nonneg A) hn
  nlinarith [sq_abs (A ![1,0,0]),sq_abs (A ![0,1,0]),sq_abs (A ![0,0,1]),
    sq_nonneg (|A ![1,0,0]|-|A ![0,1,0]|),sq_nonneg (|A ![1,0,0]|-|A ![0,0,1]|),
    sq_nonneg (|A ![0,1,0]|-|A ![0,0,1]|)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory UnitAddTorus

def centralBoundary (i : Fin 3) (x : UnitAddTorus (Fin 2)) : Box3 :=
  sourcePairCoordinates (![sourceAngularCollar centralThickness x,
    sourceChildCoordinates 1 (sourceAngularCollar (-centralThickness) x),
    sourceChildCoordinates (-1) (sourceAngularCollar (-centralThickness) x)] i)

lemma continuous_centralBoundary (i : Fin 3) : Continuous (centralBoundary i) := by
  fin_cases i <;> apply sourcePairCLE.continuous.comp
  · exact continuous_sourceAngularCollar _
  · exact (sourceChildCoordinates_contDiff 1).continuous.comp (continuous_sourceAngularCollar _)
  · exact (sourceChildCoordinates_contDiff (-1)).continuous.comp (continuous_sourceAngularCollar _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

open Set MeasureTheory
open scoped ENNReal

def centralMeasure : Measure Box3 := volume.restrict centralClosed

def centralSmoothFunctions : Submodule ℝ (Box3 → ℝ) where
  carrier := {f | ContDiff ℝ (↑(⊤ : ℕ∞)) f}
  zero_mem' := by change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : Box3 => (0 : ℝ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ (↑(⊤ : ℕ∞)) f from hf).add (show ContDiff ℝ (↑(⊤ : ℕ∞)) g from hg)
  smul_mem' := by
    intro c f hf
    exact (show ContDiff ℝ (↑(⊤ : ℕ∞)) f from hf).const_smul c

instance instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions : CoeFun centralSmoothFunctions (fun _ => Box3 → ℝ) := ⟨fun f => f.val⟩

lemma central_smooth (f : centralSmoothFunctions) : ContDiff ℝ (↑(⊤ : ℕ∞)) f := f.property

abbrev CentralL2 := Lp ℝ 2 centralMeasure
abbrev CentralJets := PiLp 2 (fun _ : Fin 4 => CentralL2)

lemma central_continuous_memLp {f : Box3 → ℝ} (hf : Continuous f) : MemLp f 2 centralMeasure := by
  exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    ((hf.pow 2).continuousOn.integrableOn_compact centralClosed_compact)

def centralJetField (f : Box3 → ℝ) (i : Fin 4) : Box3 → ℝ :=
  ![f,cubePartial f ((1,0),0),cubePartial f ((0,1),0),cubePartial f ((0,0),1)] i

lemma centralJetField_continuous (f : centralSmoothFunctions) (i : Fin 4) :
    Continuous (centralJetField f i) := by
  fin_cases i
  · exact (central_smooth f).continuous
  · exact continuous_cubePartial (central_smooth f) _
  · exact continuous_cubePartial (central_smooth f) _
  · exact continuous_cubePartial (central_smooth f) _

def centralSmoothJet (f : centralSmoothFunctions) : CentralJets :=
  WithLp.toLp 2 (fun i => (central_continuous_memLp (centralJetField_continuous f i)).toLp (centralJetField f i))

lemma centralSmoothJet_ae (f : centralSmoothFunctions) (i : Fin 4) :
    centralSmoothJet f i=ᵐ[centralMeasure] centralJetField f i := (central_continuous_memLp (centralJetField_continuous f i)).coeFn_toLp

lemma centralJetField_add (f g : centralSmoothFunctions) (i : Fin 4) :
    centralJetField (f+g) i=centralJetField f i+centralJetField g i := by
  funext z
  have he := fderiv_add ((central_smooth f).differentiable (by simp) z) ((central_smooth g).differentiable (by simp) z)
  change fderiv ℝ (fun y => f y+g y) z=_ at he
  fin_cases i
  · rfl
  · change (fderiv ℝ (fun y => f y+g y) z) ((1,0),0)=_
    rw [he]; rfl
  · change (fderiv ℝ (fun y => f y+g y) z) ((0,1),0)=_
    rw [he]; rfl
  · change (fderiv ℝ (fun y => f y+g y) z) ((0,0),1)=_
    rw [he]; rfl

lemma centralJetField_smul (c : ℝ) (f : centralSmoothFunctions) (i : Fin 4) :
    centralJetField (c•f) i=c•centralJetField f i := by
  funext z
  have he := fderiv_const_smul ((central_smooth f).differentiable (by simp) z) c
  change fderiv ℝ (fun y => c • f y) z=_ at he
  fin_cases i
  · rfl
  · change (fderiv ℝ (fun y => c • f y) z) ((1,0),0)=_
    rw [he]; rfl
  · change (fderiv ℝ (fun y => c • f y) z) ((0,1),0)=_
    rw [he]; rfl
  · change (fderiv ℝ (fun y => c • f y) z) ((0,0),1)=_
    rw [he]; rfl

def centralSmoothJetL : centralSmoothFunctions →ₗ[ℝ] CentralJets where
  toFun := centralSmoothJet
  map_add' := by
    intro f g
    apply PiLp.ext; intro i; apply Lp.ext
    filter_upwards [centralSmoothJet_ae (f+g) i,centralSmoothJet_ae f i,centralSmoothJet_ae g i,
      Lp.coeFn_add (centralSmoothJet f i) (centralSmoothJet g i)] with z hz hf hg ha
    change (centralSmoothJet (f+g) i) z=((centralSmoothJet f i)+(centralSmoothJet g i)) z
    rw [hz,ha]
    simp only [Pi.add_apply,hf,hg]
    exact congrFun (centralJetField_add f g i) z
  map_smul' := by
    intro c f
    apply PiLp.ext; intro i; apply Lp.ext
    filter_upwards [centralSmoothJet_ae (c•f) i,centralSmoothJet_ae f i,
      Lp.coeFn_smul c (centralSmoothJet f i)] with z hz hf ha
    change (centralSmoothJet (c•f) i) z=(c•(centralSmoothJet f i)) z
    rw [hz,ha]
    simp only [Pi.smul_apply,hf]
    exact congrFun (centralJetField_smul c f i) z

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralSmoothTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory UnitAddTorus
open scoped ENNReal

local instance instMeasureSpaceUnitAddCircle_solutions_3 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev TorusModes := Fin 2 → ℤ

def centralTraceFunction (f : centralSmoothFunctions) (i : Fin 3) :
    C(UnitAddTorus (Fin 2),ℂ) :=
  ⟨fun x => (f (centralBoundary i x):ℂ),
    Complex.continuous_ofReal.comp ((central_smooth f).continuous.comp (continuous_centralBoundary i))⟩

def centralTraceFourier (f : centralSmoothFunctions) (i : Fin 3) : SpectralL2 TorusModes :=
  ((mFourierBasis (d:=Fin 2)).repr.restrictScalars ℝ) (ContinuousMap.toLp 2 volume ℝ (centralTraceFunction f i))

lemma centralTraceFourier_apply (f : centralSmoothFunctions) (i : Fin 3) (h : TorusModes) :
    centralTraceFourier f i h=mFourierCoeff (fun x => (f (centralBoundary i x):ℂ)) h := by
  change (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (centralTraceFunction f i)) h=_
  rw [mFourierBasis_repr,mFourierCoeff_toLp]
  rfl

lemma centralTrace_summable (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    Summable (fun h => torusRate s h*‖centralTraceFourier f i h‖^2) := by
  simp only [centralTraceFourier_apply]
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : Fin 3 → ℝ => f (sourcePairCoordinates y)) :=
    (central_smooth f).comp sourcePairCLE.contDiff
  fin_cases i
  · simpa [centralBoundary] using
      (sourceAngularTrace_summable s centralThickness hf)
  · simpa [centralBoundary,Function.comp_def] using
      (sourceAngularTrace_summable s (-centralThickness) (hf.comp (sourceChildCoordinates_contDiff 1)))
  · simpa [centralBoundary,Function.comp_def] using
      (sourceAngularTrace_summable s (-centralThickness) (hf.comp (sourceChildCoordinates_contDiff (-1))))

def centralSmoothTrace (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    spectralTraceGraph (torusRate s) :=
  ((spectralTraceGraph_exists_iff (fun frequency => Real.sqrt_nonneg (torusQuadratic s frequency)) (centralTraceFourier f i)).mpr
    (centralTrace_summable s f i)).choose

lemma centralSmoothTrace_fst (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    (centralSmoothTrace s f i).val 0=centralTraceFourier f i :=
  ((spectralTraceGraph_exists_iff (fun frequency => Real.sqrt_nonneg (torusQuadratic s frequency)) (centralTraceFourier f i)).mpr
    (centralTrace_summable s f i)).choose_spec

lemma centralTraceFunction_add (f g : centralSmoothFunctions) (i : Fin 3) :
    centralTraceFunction (f+g) i=centralTraceFunction f i+centralTraceFunction g i := by
  ext x
  exact Complex.ofReal_add _ _

lemma centralTraceFunction_smul (c : ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    centralTraceFunction (c•f) i=c•centralTraceFunction f i := by
  ext x
  exact Complex.ofReal_mul _ _

def centralSmoothTraceL (s : Fin 3 → ℝ) (i : Fin 3) :
    centralSmoothFunctions →ₗ[ℝ] spectralTraceGraph (torusRate s) where
  toFun := fun f => centralSmoothTrace s f i
  map_add' := by
    intro f g
    apply spectralTraceGraph_fst_injective
    change (centralSmoothTrace s (f+g) i).val 0=(centralSmoothTrace s f i).val 0+(centralSmoothTrace s g i).val 0
    rw [centralSmoothTrace_fst,centralSmoothTrace_fst,centralSmoothTrace_fst]
    simp only [centralTraceFourier,centralTraceFunction_add,map_add]
  map_smul' := by
    intro c f
    apply spectralTraceGraph_fst_injective
    change (centralSmoothTrace s (c•f) i).val 0=c•(centralSmoothTrace s f i).val 0
    rw [centralSmoothTrace_fst,centralSmoothTrace_fst]
    simp only [centralTraceFourier,centralTraceFunction_smul,map_smul]

end

open Set MeasureTheory UnitAddTorus
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_SmoothScalarAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open scoped ContDiff

def smoothScalarAlgebra (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Subalgebra ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ (↑(⊤ : ℕ∞)) f}
  algebraMap_mem' r := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : E => r)
    exact contDiff_const
  zero_mem' := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : E => 0)
    exact contDiff_const
  one_mem' := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : E => 1)
    exact contDiff_const
  add_mem' hf hg := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _ at hf hg ⊢
    exact hf.add hg
  mul_mem' hf hg := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _ at hf hg ⊢
    exact hf.mul hg

abbrev SmoothScalar (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  smoothScalarAlgebra E

theorem smoothScalar_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SmoothScalar E) : ContDiff ℝ (↑(⊤ : ℕ∞)) f.val := by
  exact f.property

def smoothDirection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) : SmoothScalar E →ₗ[ℝ] SmoothScalar E where
  toFun f := ⟨fun x => fderiv ℝ f.val x v, by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _
    exact ((smoothScalar_contDiff f).fderiv_right
      (m := ↑(⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (f.val + g.val) x v = fderiv ℝ f.val x v + fderiv ℝ g.val x v
    rw [fderiv_add ((smoothScalar_contDiff f).differentiable (by simp) x)
      ((smoothScalar_contDiff g).differentiable (by simp) x)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (c • f.val) x v = c • fderiv ℝ f.val x v
    rw [fderiv_const_smul ((smoothScalar_contDiff f).differentiable (by simp) x)]
    rfl

@[simp] theorem smoothDirection_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (f : SmoothScalar E) (x : E) :
    (smoothDirection v f).val x = fderiv ℝ f.val x v := rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def smoothPrimitive (h : SmoothScalar ℝ) : SmoothScalar ℝ :=
  ⟨fun x => ∫ t in (0 : ℝ)..x, h.val t, by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _
    have hd : ∀ x : ℝ, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, h.val t) (h.val x) x :=
      fun x => intervalIntegral.integral_hasDerivAt_right
        ((smoothScalar_contDiff h).continuous.intervalIntegrable 0 x)
        ((smoothScalar_contDiff h).continuous.stronglyMeasurableAtFilter _ _)
        (smoothScalar_contDiff h).continuous.continuousAt
    exact contDiff_infty_iff_deriv.mpr
      ⟨fun x => (hd x).differentiableAt, by
        rw [deriv_eq hd]
        exact smoothScalar_contDiff h⟩⟩

@[simp] theorem smoothDirection_smoothPrimitive (h : SmoothScalar ℝ) :
    smoothDirection 1 (smoothPrimitive h) = h := by
  apply Subtype.ext
  funext x
  change deriv (fun x => ∫ t in (0 : ℝ)..x, h.val t) x = h.val x
  exact (intervalIntegral.integral_hasDerivAt_right
    ((smoothScalar_contDiff h).continuous.intervalIntegrable 0 x)
    ((smoothScalar_contDiff h).continuous.stronglyMeasurableAtFilter _ _)
    (smoothScalar_contDiff h).continuous.continuousAt).deriv

def meanZeroPrimitive (h : SmoothScalar ℝ) : SmoothScalar ℝ :=
  smoothPrimitive h - algebraMap ℝ (SmoothScalar ℝ)
    (∫ t in (0 : ℝ)..1, (smoothPrimitive h).val t)

@[simp] theorem smoothDirection_meanZeroPrimitive (h : SmoothScalar ℝ) :
    smoothDirection 1 (meanZeroPrimitive h) = h := by
  rw [meanZeroPrimitive, map_sub, smoothDirection_smoothPrimitive]
  have hc (c : ℝ) : smoothDirection (1 : ℝ)
      (algebraMap ℝ (SmoothScalar ℝ) c) = 0 := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (fun _ : ℝ => c) x 1 = 0
    simp
  rw [hc, sub_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPiolaFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
namespace ScalarConductivity

def localPiolaFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) (y : E) : E := by
  classical
  exact if y ∈ X.target then
    |(fderiv ℝ X (X.symm y)).det|⁻¹ • fderiv ℝ X (X.symm y) (F (X.symm y))
  else 0

lemma local_fderiv_symm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target) {x : E} (hx : x ∈ X.source) :
    (fderiv ℝ X.symm (X x)).comp (fderiv ℝ X x) = ContinuousLinearMap.id ℝ E := by
  have hd := (hX x hx).differentiableAt (X.open_source.mem_nhds hx)
  have hdi := (hXi _ (X.map_source hx)).differentiableAt
    (X.open_target.mem_nhds (X.map_source hx))
  rw [← fderiv_comp x hdi hd]
  have he : (X.symm ∘ X) =ᶠ[𝓝 x] id := by
    filter_upwards [X.open_source.mem_nhds hx] with y hy
    exact X.left_inv hy
  rw [he.fderiv_eq, fderiv_id]

lemma local_fderiv_det_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target) {x : E} (hx : x ∈ X.source) :
    (fderiv ℝ X x).det ≠ 0 := by
  have he := congrArg (fun L : E →L[ℝ] E => L.det) (local_fderiv_symm_comp X hX hXi hx)
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_id, LinearMap.det_comp, LinearMap.det_id] at he
  exact right_ne_zero_of_mul_eq_one he

lemma integral_eq_setIntegral_of_zero_off {E V : Type*} [MeasurableSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure E) (s : Set E)
    (f : E → V) (hf : ∀ x ∉ s, f x = 0) : (∫ x, f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_univ]
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (subset_univ s) (fun x hx => hf x hx.2))

theorem localPiolaFlux_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hdet : ∀ x ∈ X.source, (fderiv ℝ X x).det ≠ 0)
    (F : E → E) (hF : Function.support F ⊆ X.source)
    (ψ : E → ℝ) (hψ : Differentiable ℝ ψ) :
    (∫ y, fderiv ℝ ψ y (localPiolaFlux X F y) ∂μ) =
      ∫ x, fderiv ℝ (ψ ∘ X) x (F x) ∂μ := by
  rw [integral_eq_setIntegral_of_zero_off μ X.target _ (by
    intro y hy; simp [localPiolaFlux, hy])]
  have hs : X '' X.source = X.target := X.image_source_eq_target
  rw [← hs, integral_image_eq_integral_abs_det_fderiv_smul μ
    X.open_source.measurableSet
    (fun x hx => ((hX x hx).differentiableAt (X.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt)
    X.injOn]
  rw [integral_eq_setIntegral_of_zero_off μ X.source
    (fun x => fderiv ℝ (ψ ∘ X) x (F x)) (by
      intro x hx
      have hz : F x = 0 := Function.notMem_support.mp (notMem_subset hF hx)
      simp [hz])]
  apply setIntegral_congr_fun X.open_source.measurableSet
  intro x hx
  simp only [localPiolaFlux, ite_eq_left (X.map_source hx), X.left_inv hx,
    map_smul, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr (hdet x hx)), one_mul]
  rw [fderiv_comp x (hψ _) ((hX x hx).differentiableAt (X.open_source.mem_nhds hx))]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ContDiffClmDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
namespace ScalarConductivity

lemma contDiff_clm_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun L : E →L[ℝ] E => L.det) := by
  classical
  let b := Module.finBasis ℝ E
  simp_rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply',
    LinearMap.toMatrix_apply]
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  change ContDiff ℝ n (fun L : E →L[ℝ] E => (b.coord (σ i)).toContinuousLinearMap (L (b i)))
  exact (b.coord (σ i)).toContinuousLinearMap.contDiff.comp ((ContinuousLinearMap.apply ℝ E (b i)).contDiff)

lemma contDiff_of_contDiffOn_tsupport {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {n : WithTop ℕ∞} {f : E → V} {s : Set E}
    (hs : IsOpen s) (hf : ContDiffOn ℝ n f s) (hfS : tsupport f ⊆ s) : ContDiff ℝ n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt (hs.mem_nhds (hfS hx))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

lemma exists_smooth_extension_near_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (φ : E → ℝ) (hφ : ContDiffOn ℝ (↑(⊤ : ℕ∞)) φ U) :
    ∃ g : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] φ := by
  obtain ⟨χ, hχ₀, hχ₁, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hK.isClosed
      (disjoint_left.mpr (fun x hx hxK => hx (hKU hxK))) (n := ⊤)
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  refine ⟨fun x => χ x * φ x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hφ.contDiffAt (hU.mem_nhds hx))
    · have hzero : ∀ᶠ z in 𝓝 x, χ z = 0 := hχ₀.filter_mono (nhds_le_nhdsSet hx)
      apply (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun _ : E => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [hzero] with z hz
      simp [hz]
  · intro x hx
    have hone : ∀ᶠ z in 𝓝 x, χ z = 1 := hχ₁.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hone] with z hz
    simp [hz]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SmoothPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def smoothPhase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) : SmoothScalar ℝ →ₐ[ℝ] SmoothScalar E where
  toFun H := ⟨H.val ∘ L, by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _
    exact (smoothScalar_contDiff H).comp L.contDiff⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem smoothPhase_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) (H : SmoothScalar ℝ) (x : E) :
    (smoothPhase L H).val x = H.val (L x) := rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AirySymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Matrix

theorem tsupport_smoothDirection_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (f : SmoothScalar E) :
    tsupport (smoothDirection v f).val ⊆ tsupport f.val := by
  exact (tsupport_comp_subset (g := fun L : E →L[ℝ] ℝ => L v) (by simp)
    (fderiv ℝ f.val)).trans (tsupport_fderiv_subset ℝ)

theorem compactSupport_smoothDirection {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) {f : SmoothScalar E} (hf : HasCompactSupport f.val) :
    HasCompactSupport (smoothDirection v f).val :=
  hf.of_isClosed_subset isClosed_closure (tsupport_smoothDirection_subset v f)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TwoFluxColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def piolaFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (F : E → E) (y : E) : E :=
  |(fderiv ℝ X (X.symm y)).det|⁻¹ • fderiv ℝ X (X.symm y) (F (X.symm y))

theorem piolaFlux_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : E ≃ E) (hX : Differentiable ℝ X)
    (hdet : ∀ x, (fderiv ℝ X x).det ≠ 0)
    (F : E → E) (ψ : E → ℝ) (hψ : Differentiable ℝ ψ) :
    (∫ y, fderiv ℝ ψ y (piolaFlux X F y) ∂μ) =
      ∫ x, fderiv ℝ (ψ ∘ X) x (F x) ∂μ := by
  have hc := integral_image_eq_integral_abs_det_fderiv_smul μ
    MeasurableSet.univ (fun x _ => (hX x).hasFDerivAt.hasFDerivWithinAt)
    X.injective.injOn (fun y => fderiv ℝ ψ y (piolaFlux X F y))
  simp only [Set.image_univ, Set.range_eq_univ.mpr X.surjective, Measure.restrict_univ] at hc
  rw [hc]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [piolaFlux, X.symm_apply_apply, map_smul, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr (hdet x)), one_mul]
  rw [fderiv_comp x (hψ _) (hX x)]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PreliminaryQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

abbrev Symmetric3 := { A : Mat3 // A.IsHermitian }

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SymmetricCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

section
open Matrix

theorem gram_leftInverse {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (E : Matrix m n ℝ) (hE : LinearIndependent ℝ E.col) :
    ((Eᵀ * E)⁻¹ * Eᵀ) * E = 1 := by
  have hinj : Function.Injective E.mulVec := Matrix.mulVec_injective_iff.mpr hE
  have hker : LinearMap.ker (Eᵀ * E).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hinj
  have hunit : IsUnit (Eᵀ * E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hker))
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit]

end

open Filter Topology Set TopologicalSpace

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingHxx
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

def pushGradient {m : Type*} [Fintype m] (J : Mat3) (E : Matrix (Fin 3) m ℝ) :
    Matrix (Fin 3) m ℝ := J⁻¹ᵀ * E

lemma pushGradient_leftInverse {m : Type*} [Fintype m] (J : Mat3)
    (hJ : J.det ≠ 0) (E : Matrix (Fin 3) m ℝ) : Jᵀ * pushGradient J E = E := by
  have hj := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hJ)
  unfold pushGradient
  rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hj, Matrix.transpose_one, Matrix.one_mul]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DerivativeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
section

lemma fderiv_equiv_symm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) (x : E) :
    (fderiv ℝ X.symm (X x)).comp (fderiv ℝ X x) = ContinuousLinearMap.id ℝ E := by
  rw [← fderiv_comp x (hXi _) (hX _)]
  have hx : (X.symm ∘ X : E → E) = id := funext X.symm_apply_apply
  rw [hx, fderiv_id]

lemma fderiv_equiv_det_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) (x : E) :
    (fderiv ℝ X x).det ≠ 0 := by
  have hc := congrArg (fun L : E →L[ℝ] E => L.det) (fderiv_equiv_symm_comp X hX hXi x)
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_id, LinearMap.det_comp, LinearMap.det_id] at hc
  exact right_ne_zero_of_mul_eq_one hc

end

open Set MeasureTheory Filter Topology
open scoped BigOperators

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_GradientColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix
open scoped Matrix.Norms.Elementwise

def gradientColumns {m : Type*} [Fintype m] [DecidableEq m]
    (D : (Fin 3 → ℝ) →L[ℝ] (m → ℝ)) : Matrix (Fin 3) m ℝ :=
  (LinearMap.toMatrix' D.toLinearMap)ᵀ

lemma gradientColumns_apply {m : Type*} [Fintype m] [DecidableEq m]
    (D : (Fin 3 → ℝ) →L[ℝ] (m → ℝ)) (v : Fin 3 → ℝ) :
    (gradientColumns D)ᵀ *ᵥ v = D v := by
  simp only [gradientColumns, transpose_transpose, LinearMap.toMatrix'_mulVec,
    ContinuousLinearMap.coe_coe]

lemma gradientColumns_rank {m : Type*} [Fintype m] [DecidableEq m]
    (D : (Fin 3 → ℝ) →L[ℝ] (m → ℝ)) (hD : Function.Surjective D) :
    LinearIndependent ℝ (gradientColumns D).col := by
  obtain ⟨Q, hQ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hD
  let M := LinearMap.toMatrix' D.toLinearMap
  let N := LinearMap.toMatrix' Q.toLinearMap
  have hMN : M * N = 1 := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, M, N, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    apply LinearMap.ext
    intro v
    exact hQ v
  have hNM : Nᵀ * gradientColumns D = 1 := by
    rw [gradientColumns, ← Matrix.transpose_mul, hMN, transpose_one]
  apply Matrix.mulVec_injective_iff.mp
  intro v w hvw
  have h := congrArg Nᵀ.mulVec hvw
  simpa only [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] using h

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothCompose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Filter Topology

def smoothCompose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : SmoothScalar E) : SmoothScalar ℝ →ₐ[ℝ] SmoothScalar E where
  toFun H := ⟨H.val ∘ φ.val, (smoothScalar_contDiff H).comp (smoothScalar_contDiff φ)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma smoothCompose_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (φ : SmoothScalar E) (H : SmoothScalar ℝ) (x : E) :
    (smoothCompose φ H).val x = H.val (φ.val x) := rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SynchronizedChartWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

abbrev Coord3 := Fin 3 → ℝ

def operatorMatrix {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : (n → ℝ) →L[ℝ] (m → ℝ)) : Matrix m n ℝ :=
  LinearMap.toMatrix' D.toLinearMap

lemma operatorMatrix_comp {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r]
    (D : (n → ℝ) →L[ℝ] (m → ℝ)) (E : (r → ℝ) →L[ℝ] (n → ℝ)) :
    operatorMatrix (D.comp E) = operatorMatrix D * operatorMatrix E :=
  LinearMap.toMatrix'_comp D.toLinearMap E.toLinearMap

lemma operatorMatrix_id : operatorMatrix (ContinuousLinearMap.id ℝ Coord3) = 1 :=
  LinearMap.toMatrix'_id

lemma operatorMatrix_det (D : Coord3 →L[ℝ] Coord3) : (operatorMatrix D).det = D.det :=
  LinearMap.det_toMatrix' D.toLinearMap

lemma operatorMatrix_mulVec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : (n → ℝ) →L[ℝ] (m → ℝ)) (v : n → ℝ) : operatorMatrix D *ᵥ v = D v :=
  LinearMap.toMatrix'_mulVec D.toLinearMap v

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CollarAngularInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma rectangularRay_max {w : ℝ} (hw : 0<w) (hw' : w≤1) (θ : UnitAddCircle) :
    max (|rectangularRay w θ 0|/w) |rectangularRay w θ 1|=1 := by
  have hd : 0 < rayDenominator w θ := lt_of_lt_of_le (by norm_num) (rayDenominator_lower hw hw' θ)
  simp only [rectangularRay,abs_div,abs_of_pos hd]
  rw [div_right_comm _ _ w,max_div_div_right hd.le]
  exact div_self hd.ne'

lemma rectangularRay_first_abs {w : ℝ} (hw : 0<w) (hw' : w≤1) (θ : UnitAddCircle) :
    |rectangularRay w θ 0|≤w := by
  have hh := (le_max_left _ _).trans (rectangularRay_max hw hw' θ).le
  exact (div_le_iff₀ hw).mp hh |>.trans_eq (one_mul w)

lemma sourceAngular_radius_pos {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    0 < sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0 := by
  have hh := abs_le.mp (rectangularRay_first_abs (w:=sourceRadialWidth)
    (by norm_num [sourceRadialWidth,sourceHole]) (by norm_num [sourceRadialWidth,sourceHole]) (θ 1))
  have ht' : 0≤1-t := by linarith [ht.2]
  have hm := mul_le_mul_of_nonneg_left hh.1 ht'
  norm_num [sourceRadialWidth,sourceRadialCenter,sourceHole] at *
  linarith

lemma sourceAngular_radial {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    sourceRadial (sourceAngularCollar t θ)=
      sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0 := by
  have hr := sourceAngular_radius_pos ht θ
  have hL : 0 < sourceLength := by norm_num [sourceLength]
  let R := sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0
  change 0<R at hr
  change max (|sourceLength*R*rectangularRay 1 (θ 0) 0|/sourceLength)
    |R*rectangularRay 1 (θ 0) 1|=R
  simp only [abs_mul,abs_of_pos hL,abs_of_pos hr]
  rw [mul_assoc,mul_div_cancel_left₀ _ hL.ne',←mul_max_of_nonneg _ _ hr.le]
  have hh := rectangularRay_max (w:=1) (by norm_num) (by norm_num) (θ 0)
  simpa only [div_one,mul_one] using congrArg
    (fun z => (sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0)*z) hh

lemma sourceAngular_time {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) : sourceCollarTime (sourceAngularCollar t θ)=t := by
  have hs : 0<1-t := by linarith [ht.2]
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  rw [sourceCollarTime]
  simp only [sourceCrossCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [sourceAngular_radial ht,add_sub_cancel_left,mul_div_assoc,abs_mul,abs_of_pos hs]
  change 1-max ((1-t)*|(rectangularRay sourceRadialWidth (θ 1) 0)/sourceRadialWidth|)
    |(1-t)*rectangularRay sourceRadialWidth (θ 1) 1|=t
  rw [abs_div,abs_of_pos hw,abs_mul,abs_of_pos hs,←mul_max_of_nonneg _ _ hs.le,
    rectangularRay_max hw (by norm_num [sourceRadialWidth,sourceHole]) (θ 1), mul_one]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPoissonContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory Filter Topology UnitAddTorus Real Set
open scoped ENNReal

def torusAngles (x : Fin 3 → ℝ) : UnitAddTorus (Fin 2) :=
  ![(x 1/(2*Real.pi):ℝ),(x 2/(2*Real.pi):ℝ)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CollarCartesianDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped Matrix.Norms.Elementwise

def sourceFaceAngles (i j : Fin 4) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 0,2*Real.pi*faceRayAngle 1 i (x 1),
    2*Real.pi*faceRayAngle sourceRadialWidth j (x 2)]

lemma sourceFaceAngles_torus (i j : Fin 4) (x : Fin 3 → ℝ) :
    torusAngles (sourceFaceAngles i j x)=
      ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)] := by
  ext k
  fin_cases k <;> simp [torusAngles,sourceFaceAngles,Real.pi_ne_zero]

lemma sourceFaceAngles_physical (i j : Fin 4) {x : Fin 3 → ℝ}
    (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceAngularCollar (x 0) (torusAngles (sourceFaceAngles i j x))=
      sourceCollarPiece i j x := by
  rw [sourceFaceAngles_torus,sourceAngular_face _ _ _ _ _ ha hb]
  congr 1
  ext k
  fin_cases k <;> rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma squareFace_scaled_surjective (v : Fin 2 → ℝ) {r : ℝ} (hr : 0 < r)
    (hv : max |v 0| |v 1|=r) :
    ∃ i : Fin 4, ∃ a : ℝ, |a|≤1 ∧ v=r • squareFace i a := by
  have hs : max |(r⁻¹ • v) 0| |(r⁻¹ • v) 1|=1 := by
    simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr hr.le)]
    rw [←mul_max_of_nonneg _ _ (inv_nonneg.mpr hr.le),hv,inv_mul_cancel₀ hr.ne']
  obtain ⟨i,a,ha,he⟩ := squareFace_min_max (r⁻¹ • v) hs
  refine ⟨i,a,ha,?_⟩
  rw [he,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]

def sourceClosedCollarBand (l r : ℝ) : Set (Fin 3 → ℝ) :=
  sourceCollarTime ⁻¹' Icc l r

lemma sourceRadial_pos_of_time {y : Fin 3 → ℝ}
    (ht : -(1:ℝ)/100 ≤ sourceCollarTime y) : 0 < sourceRadial y := by
  have hm : |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth|≤1+(1:ℝ)/100 := by
    have h := le_max_left |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth| |y 2|
    change -(1:ℝ)/100≤1-max |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth| |y 2| at ht
    linarith
  have hn := (abs_le.mp hm).1
  norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole] at hn
  linarith

lemma sourceCollarPiece_cover_extended {y : Fin 3 → ℝ}
    (hr : 0 < sourceRadial y) (ht : sourceCollarTime y<1) :
    ∃ i j : Fin 4, ∃ a b : ℝ, |a|≤1 ∧ |b|≤1 ∧
      sourceCollarPiece i j ![sourceCollarTime y,a,b]=y := by
  have hL : 0 < sourceLength := by norm_num [sourceLength]
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hq : 0<1-sourceCollarTime y := sub_pos.mpr ht
  have havg : max |![y 0/sourceLength,y 1] 0| |![y 0/sourceLength,y 1] 1|=sourceRadial y := by
    simp [sourceRadial,abs_div,abs_of_pos hL]
  obtain ⟨i,a,ha,he⟩ := squareFace_scaled_surjective ![y 0/sourceLength,y 1] hr havg
  have hcross : max |sourceCrossCoordinates y 0| |sourceCrossCoordinates y 1|=1-sourceCollarTime y := by
    simp [sourceCollarTime]
  obtain ⟨j,b,hb,hb'⟩ := squareFace_scaled_surjective (sourceCrossCoordinates y) hq hcross
  have hrad : sourceCollarRadius j (sourceCollarTime y) b=sourceRadial y := by
    have hh := congrFun hb' 0
    change (sourceRadial y-sourceRadialCenter)/sourceRadialWidth=
      (1-sourceCollarTime y)*squareFace j b 0 at hh
    have hh' := (div_eq_iff hw.ne').mp hh
    dsimp [sourceCollarRadius]
    nlinarith [hh']
  refine ⟨i,j,a,b,ha,hb,?_⟩
  ext k
  fin_cases k
  · have hx := congrFun he 0
    change y 0/sourceLength=sourceRadial y*squareFace i a 0 at hx
    change sourceLength*sourceCollarRadius j (sourceCollarTime y) b*squareFace i a 0=y 0
    rw [hrad]
    have hh := (div_eq_iff hL.ne').mp hx
    nlinarith
  · have hx := congrFun he 1
    change y 1=sourceRadial y*squareFace i a 1 at hx
    change sourceCollarRadius j (sourceCollarTime y) b*squareFace i a 1=y 1
    rw [hrad]; exact hx.symm
  · have hx := congrFun hb' 1
    change y 2=(1-sourceCollarTime y)*squareFace j b 1 at hx
    exact hx.symm

lemma sourceClosedCollarBand_eq (l r : ℝ) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    sourceClosedCollarBand l r=
      ⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r := by
  ext y
  constructor
  · intro hy
    obtain ⟨i,j,a,b,ha,hb,he⟩ := sourceCollarPiece_cover_extended
      (sourceRadial_pos_of_time (hl.trans hy.1)) (by linarith [hy.2])
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,
      ⟨![sourceCollarTime y,a,b],mem_sourceExtendedBox.mpr ⟨hy,ha,hb⟩,he⟩⟩⟩
  · intro hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    obtain ⟨j,x,hx,rfl⟩ := mem_iUnion.mp hi
    obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
    have hb' := sourceFaceAngles_physical i j ha hb
    rw [←hb']
    change sourceCollarTime (sourceAngularCollar (x 0) _)∈Icc l r
    rw [sourceAngular_time ⟨hl.trans ht.1,ht.2.trans hr⟩]
    exact ht

lemma isCompact_sourceClosedCollarBand {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) : IsCompact (sourceClosedCollarBand l r) := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  apply isCompact_iUnion
  intro i
  apply isCompact_iUnion
  intro j
  exact isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralEnergySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory
open scoped ENNReal

instance spectralTraceGraph_realInner {ι : Type*} (w : ι → ℝ) :
    InnerProductSpace ℝ (spectralTraceGraph w) := InnerProductSpace.complexToReal

abbrev CentralTraceFields (s : Fin 3 → ℝ) := PiLp 2 (fun _ : Fin 3 => spectralTraceGraph (torusRate s))
abbrev CentralAmbient (s : Fin 3 → ℝ) := WithLp 2 (CentralJets × CentralTraceFields s)

instance centralAmbientInnerProductSpace (s : Fin 3 → ℝ) : InnerProductSpace ℝ (CentralAmbient s) := inferInstance

def centralEmbedL (s : Fin 3 → ℝ) : centralSmoothFunctions →ₗ[ℝ] CentralAmbient s :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ CentralJets (CentralTraceFields s)).symm.toLinearMap.comp
    (centralSmoothJetL.prod
      (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => spectralTraceGraph (torusRate s))).symm.toLinearMap).comp
        (LinearMap.pi (centralSmoothTraceL s))))

def centralEnergySpace (s : Fin 3 → ℝ) : Submodule ℝ (CentralAmbient s) :=
  (LinearMap.range (centralEmbedL s)).topologicalClosure

end

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

@[instance_reducible] def centralEnergy_inner (s : Fin 3 → ℝ) : InnerProductSpace ℝ (centralEnergySpace s) :=
  Submodule.innerProductSpace (centralEnergySpace s)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralUnnormalizedVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def angularArea : ℝ := (2*Real.pi)^2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixFiniteLaminate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
namespace ScalarConductivity

open Set Filter Topology

def jetLiftValue : ℝ →L[ℝ] JetFiber :=
  LinearMap.toContinuousLinearMap {
    toFun := fun r => WithLp.toLp 2 (Fin.cases r (fun _ => 0))
    map_add' := by intro x y; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    map_smul' := by intro c x; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }

def jetLiftGradient : R3 →L[ℝ] JetFiber :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => WithLp.toLp 2 (Fin.cases 0 (fun i => v i))
    map_add' := by intro x y; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    map_smul' := by intro c x; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_NonlinearLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

instance ballMeasure_finite : IsFiniteMeasure ballMeasure := by
  exact isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

lemma continuous_gradient_of_smooth {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : Continuous (gradient f) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ R3).symm.continuous.comp
    (hf.continuous_fderiv (by simp))

lemma smoothJet_continuous {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : Continuous (smoothJet f) := by
  have he : smoothJet f = fun x => jetLiftValue (f x)+jetLiftGradient (gradient f x) := by
    ext x i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [smoothJet,jetLiftValue,jetLiftGradient]
  rw [he]
  exact (jetLiftValue.continuous.comp hf.continuous).add
    (jetLiftGradient.continuous.comp (continuous_gradient_of_smooth hf))

lemma continuous_bound_ball {E : Type*} [NormedAddCommGroup E] {f : R3 → E}
    (hf : Continuous f) : ∃ M : ℝ, 0≤M ∧ ∀ᵐ x ∂ballMeasure, ‖f x‖≤M := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:R3) 3).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0,le_max_right _ _,?_⟩
  filter_upwards [ae_restrict_mem (s := ball) measurableSet_ball] with x hx
  exact (hM x (Metric.ball_subset_closedBall hx)).trans (le_max_left _ _)

lemma smoothJet_memLp {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    MemLp (smoothJet f) 2 ballMeasure := by
  obtain ⟨M,_,hM⟩ := continuous_bound_ball (smoothJet_continuous hf)
  exact MemLp.of_bound (smoothJet_continuous hf).aestronglyMeasurable M hM

def smoothH1 (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : H1 :=
  ⟨(smoothJet_memLp hf).toLp _, (Submodule.le_topologicalClosure _)
    (Submodule.subset_span ⟨f,hf,smoothJet_memLp hf,rfl⟩)⟩

open Set MeasureTheory Filter Topology Real

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CollarInteriorFacts
attribute [-instance] _root_.OAI.ScalarConductivity.ballMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceBand_euclidean_bound {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) :
    ‖WithLp.toLp 2 y‖≤(5:ℝ)/2 := by
  have hm : max |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth| |y 2|≤101/100 := by
    have ht := hy.1
    change -(1:ℝ)/100≤1-max |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth| |y 2| at ht
    linarith
  have hrad : sourceRadial y≤101/100 := by
    have hh := (le_abs_self ((sourceRadial y-sourceRadialCenter)/sourceRadialWidth)).trans
      ((le_max_left _ _).trans hm)
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole,div_eq_mul_inv] at hh
    linarith
  have h0 : |y 0|≤17/10 := by
    have hh := (le_max_left (|y 0|/sourceLength) |y 1|).trans hrad
    norm_num [sourceLength,div_eq_mul_inv] at hh
    linarith
  have h1 : |y 1|≤11/10 := by
    have hh := (le_max_right (|y 0|/sourceLength) |y 1|).trans hrad
    linarith
  have h2 : |y 2|≤11/10 := by
    have hh := (le_max_right _ _).trans hm
    linarith
  have h0' := pow_le_pow_left₀ (abs_nonneg _) h0 2
  have h1' := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hn := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : R3)
  simp [Fin.sum_univ_succ] at hn
  simp only [sq_abs] at h0' h1' h2'
  nlinarith [norm_nonneg (WithLp.toLp 2 y : R3)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LpExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {D : Set X}

def lpZeroExtensionL (hD : MeasurableSet D) : Lp E 2 (μ.restrict D) →ₗ[ℝ] Lp E 2 μ where
  toFun f := ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [((memLp_indicator_iff_restrict hD).mpr (Lp.memLp (f+g))).coeFn_toLp,
      ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).coeFn_toLp,
      ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp g)).coeFn_toLp,
      Lp.coeFn_add (((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f))
        (((memLp_indicator_iff_restrict hD).mpr (Lp.memLp g)).toLp (D.indicator g)),
      (ae_restrict_iff' hD).mp (Lp.coeFn_add f g)] with x hfg hf hg he hadd
    rw [hfg,he]
    simp only [Pi.add_apply,hf,hg]
    by_cases hx : x∈D
    · simp only [indicator_of_mem hx,hadd hx,Pi.add_apply]
    · simp [hx]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [((memLp_indicator_iff_restrict hD).mpr (Lp.memLp (c•f))).coeFn_toLp,
      ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).coeFn_toLp,
      Lp.coeFn_smul c (((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f)),
      (ae_restrict_iff' hD).mp (Lp.coeFn_smul c f)] with x hcf hf he hsmul
    change _=(c • _ : Lp E 2 μ) x
    rw [hcf,he]
    simp only [Pi.smul_apply,hf]
    by_cases hx : x∈D
    · simp only [indicator_of_mem hx,hsmul hx,Pi.smul_apply]
    · simp [hx]

lemma lpZeroExtensionL_ae (hD : MeasurableSet D) (f : Lp E 2 (μ.restrict D)) :
    lpZeroExtensionL hD f=ᵐ[μ] D.indicator f :=
  ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).coeFn_toLp

lemma lpZeroExtensionL_norm (hD : MeasurableSet D) (f : Lp E 2 (μ.restrict D)) :
    ‖lpZeroExtensionL hD f‖=‖f‖ := by
  change ‖((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f)‖=_
  rw [Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict hD,Lp.norm_def]

def lpZeroExtensionCLM (hD : MeasurableSet D) : Lp E 2 (μ.restrict D) →L[ℝ] Lp E 2 μ :=
  (lpZeroExtensionL hD).mkContinuous 1 (by intro f; rw [lpZeroExtensionL_norm,one_mul])

lemma lpZeroExtensionCLM_ae (hD : MeasurableSet D) (f : Lp E 2 (μ.restrict D)) :
    lpZeroExtensionCLM hD f=ᵐ[μ] D.indicator f := lpZeroExtensionL_ae hD f

lemma lpZeroExtensionCLM_ae_of_ae (hD : MeasurableSet D) (f : Lp E 2 (μ.restrict D))
    {g : X → E} (hg : f=ᵐ[μ.restrict D] g) :
    lpZeroExtensionCLM hD f=ᵐ[μ] D.indicator g := by
  filter_upwards [lpZeroExtensionCLM_ae hD f,(ae_restrict_iff' hD).mp hg] with x hx hg
  rw [hx]
  by_cases h : x∈D
  · simp only [indicator_of_mem h,hg h]
  · simp [h]

def lpRestrictionCLM (D : Set X) : Lp E 2 μ →L[ℝ] Lp E 2 (μ.restrict D) :=
  Lp.LpToLpOfMeasureLeSMul (c:=1) (by simp) (by simpa using Measure.restrict_le_self (μ:=μ) (s:=D))

lemma lpRestrictionCLM_ae (D : Set X) (f : Lp E 2 μ) :
    lpRestrictionCLM D f=ᵐ[μ.restrict D] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c:=1) (by simp) (by simpa using Measure.restrict_le_self (μ:=μ) (s:=D)) f

end

open Set MeasureTheory Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildCentralL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def actualChildSign (k : Fin 2) : ℝ := if k=0 then 1 else -1

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

lemma sourceChild_euclidean_norm (σ : ℝ) (y : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 (sourceChildCoordinates σ y)‖ ≤ sourceScale * ‖WithLp.toLp 2 y‖ + |σ*sourceOffset| := by
  let v : R3 := WithLp.toLp 2 ![y 1,y 0,y 2]
  have hv : ‖v‖=‖WithLp.toLp 2 y‖ := by
    have h₀ := EuclideanSpace.real_norm_sq_eq v
    have h₁ := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : R3)
    simp [v,Fin.sum_univ_succ] at h₀ h₁
    nlinarith [norm_nonneg v,norm_nonneg (WithLp.toLp 2 y : R3)]
  have he : (WithLp.toLp 2 (sourceChildCoordinates σ y) : R3)=
      sourceScale • v+EuclideanSpace.single 0 (σ*sourceOffset) := by
    ext i
    fin_cases i <;> simp [sourceChildCoordinates,v]
  rw [he]
  calc
    _ ≤ ‖sourceScale • v‖+‖EuclideanSpace.single 0 (σ*sourceOffset)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,hv,PiLp.norm_single,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ sourceScale by norm_num [sourceScale])]

def sourceChildEuclidean (σ : ℝ) : R3 ≃ₜ R3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph.trans
    ((sourceChildHomeomorph σ).trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph)

lemma sourceChildEuclidean_apply (σ : ℝ) (x : R3) :
    sourceChildEuclidean σ x=WithLp.toLp 2 (sourceChildCoordinates σ (WithLp.ofLp x)) := rfl

lemma sourceChildEuclidean_ball (k : Fin 2) : sourceChildEuclidean (actualChildSign k) '' ball⊆ball := by
  rintro x ⟨y,hy,rfl⟩
  have hn := sourceChild_euclidean_norm (actualChildSign k) (WithLp.ofLp y)
  have hσ : |actualChildSign k|=1 := by fin_cases k <;> norm_num [actualChildSign]
  rw [abs_mul,hσ,one_mul] at hn
  change ‖WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) (WithLp.ofLp y))‖ ≤ sourceScale * ‖y‖ + |sourceOffset| at hn
  change dist (sourceChildEuclidean (actualChildSign k) y) 0<3
  rw [dist_zero_right,sourceChildEuclidean_apply]
  have hy' : ‖y‖<3 := by simpa only [ball,Metric.mem_ball,dist_zero_right] using hy
  norm_num [sourceScale,sourceOffset] at hn
  linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WholeBallJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def ballWholePiJetCLM : JetSpace →L[ℝ] Lp JetFiber 2 (volume : Measure (Fin 3 → ℝ)) :=
  ((Lp.compMeasurePreservingₗᵢ ℝ
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.toMeasurableEquiv)
    (PiLp.volume_preserving_toLp (Fin 3))).toContinuousLinearMap).comp
      (lpZeroExtensionCLM Metric.isOpen_ball.measurableSet)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ChildH10Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

lemma gradient_apply_single (f : R3 → ℝ) (x : R3) (i : Fin 3) :
    gradient f x i=fderiv ℝ f x (EuclideanSpace.single i 1) := by
  rw [←toDual_gradient,InnerProductSpace.toDual_apply_apply,EuclideanSpace.inner_single_right]
  simp

open Set MeasureTheory Filter Topology

end

open Set MeasureTheory Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WholeBallJetFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Classical

lemma ballWholePiJetCLM_ae_of_ae (z : JetSpace) (f : (Fin 3 → ℝ) → JetFiber)
    (he : z=ᵐ[ballMeasure] (fun x => f (WithLp.ofLp x))) :
    ballWholePiJetCLM z=ᵐ[volume]
      (fun y => if WithLp.toLp 2 y∈ball then f y else 0) := by
  have hz := lpZeroExtensionCLM_ae_of_ae (D:=ball) Metric.isOpen_ball.measurableSet z he
  apply (Lp.coeFn_compMeasurePreserving _ (PiLp.volume_preserving_toLp (Fin 3))).trans
  have hp := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp hz
  filter_upwards [hp] with y hy
  change (lpZeroExtensionCLM (D:=ball) Metric.isOpen_ball.measurableSet z) (WithLp.toLp 2 y)=_
  rw [show (lpZeroExtensionCLM (D:=ball) Metric.isOpen_ball.measurableSet z) (WithLp.toLp 2 y)=
    ball.indicator (fun x => f (WithLp.ofLp x)) (WithLp.toLp 2 y) from hy]
  by_cases hb : WithLp.toLp 2 y∈ball <;> simp [hb]

lemma sourceBand_mem_ball {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) : WithLp.toLp 2 y∈ball := by
  have hn := sourceBand_euclidean_bound hy
  simpa only [ball,Metric.mem_ball,dist_zero_right] using hn.trans_lt (by norm_num : (5:ℝ)/2<3)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_PhysicalProductJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def piSmoothJet (q : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : JetFiber :=
  WithLp.toLp 2 (Fin.cases (q y) (fun j => fderiv ℝ q y (Pi.single j 1)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFlatEllipticity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma compact_matrix_energy_bounds {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (A : X → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContinuousOn A K)
    (hpos : ∀ x∈K,∀ v : Fin 3 → ℝ,v≠0 → 0<v ⬝ᵥ (A x*ᵥv)) :
    ∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ x∈K,∀ v : Fin 3 → ℝ,
      c*‖v‖^2≤v ⬝ᵥ (A x*ᵥv) ∧ v ⬝ᵥ (A x*ᵥv)≤C*‖v‖^2 := by
  let S := K×ˢMetric.sphere (0 : Fin 3 → ℝ) 1
  let g : X×(Fin 3 → ℝ) → ℝ := fun z => z.2 ⬝ᵥ (A z.1*ᵥz.2)
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hAc : ContinuousOn (fun z : X×(Fin 3 → ℝ) => A z.1) S :=
    hA.comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hg : ContinuousOn g S := by
    unfold g Matrix.mulVec dotProduct
    apply continuousOn_finsetSum
    intro k _
    apply ((continuous_apply k).comp continuous_snd).continuousOn.mul
    apply continuousOn_finsetSum
    intro l _
    exact ((continuous_apply_apply k l).comp_continuousOn hAc).mul
      ((continuous_apply l).comp continuous_snd).continuousOn
  have hn (v : Fin 3 → ℝ) (hv : v∈Metric.sphere (0:Fin 3 → ℝ) 1) : ‖v‖=1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using hv
  have hgp : ∀ z∈S,0<g z := by
    intro z hz
    apply hpos z.1 hz.1 z.2
    intro hv
    have h := hn z.2 hz.2
    rw [hv,norm_zero] at h
    norm_num at h
  obtain ⟨c,hc,hcg⟩ := hS.exists_forall_le' hg hgp
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hg
  refine ⟨c,max B (c+1),hc,lt_of_lt_of_le (by linarith) (le_max_right _ _),?_⟩
  intro x hx v
  by_cases hv : v=0
  · subst v
    simp
  have hnzero : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hun : ‖u‖=1 := by
    simp [u,norm_smul,hnzero]
  have hxu : (x,u)∈S := ⟨hx,by simpa only [Metric.mem_sphere,dist_zero_right] using hun⟩
  have he : g (x,u)*‖v‖^2=v ⬝ᵥ (A x*ᵥv) := by
    simp only [g,u,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    field_simp
  constructor
  · rw [←he]
    exact mul_le_mul_of_nonneg_right (hcg _ hxu) (sq_nonneg _)
  · rw [←he]
    exact mul_le_mul_of_nonneg_right
      (((le_abs_self _).trans (hB _ hxu)).trans (le_max_left _ _)) (sq_nonneg _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_FiniteEndPhysicalTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

local instance finiteEndPhysicalTensorMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

local instance finiteEndPhysicalTensorBorelSpace_r0281e9_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
lemma measurable_real_matrix_mul {α : Type*} [MeasurableSpace α]
    {A B : α → Mat3} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x => A x*B x) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ (fun k _ => hA.eval.eval.mul hB.eval.eval)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set
open scoped Matrix.Norms.Elementwise

def matrixOperator (Q : Mat3) : Coord3 →L[ℝ] Coord3 :=
  (Matrix.toLin' Q).toContinuousLinearMap

@[simp] lemma matrixOperator_apply (Q : Mat3) (v : Coord3) :
    matrixOperator Q v = Q *ᵥ v := rfl

@[simp] lemma operatorMatrix_matrixOperator (Q : Mat3) :
    operatorMatrix (matrixOperator Q) = Q := by
  simp [operatorMatrix, matrixOperator]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_QuantitativeLocalTwoFieldSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma contDiffAt_matrix_mul {X m n p : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [Fintype n] [Fintype p] {k : WithTop ℕ∞}
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) (hB : ContDiffAt ℝ k B x) :
    ContDiffAt ℝ k (fun y => A y * B y) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum (fun l _ =>
    ((contDiffAt_pi.mp (contDiffAt_pi.mp hA i)) l).mul
      ((contDiffAt_pi.mp (contDiffAt_pi.mp hB l)) j))

lemma contDiffAt_matrix_transpose {X m n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [Fintype n] {k : WithTop ℕ∞} {A : X → Matrix m n ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (fun y => (A y)ᵀ) x := by
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    contDiffAt_pi.mp (contDiffAt_pi.mp hA j) i))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PiolaFluxAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma operatorMatrix_contDiff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {k : WithTop ℕ∞} :
    ContDiff ℝ k (operatorMatrix : ((n → ℝ) →L[ℝ] (m → ℝ)) → Matrix m n ℝ) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  exact contDiff_pi.mp (contDiff_id.clm_apply contDiff_const) i

lemma contDiff_gradientColumns {m : Type*} [Fintype m] [DecidableEq m]
    (u : Coord3 → m → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => gradientColumns (fderiv ℝ u x)) := by
  rw [contDiff_iff_contDiffAt]; intro x
  exact contDiffAt_matrix_transpose ((operatorMatrix_contDiff (m := m) (n := Fin 3)).contDiffAt.comp x
    (hu.contDiffAt.fderiv_right (by simp)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactDepthReductionTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma gradientColumns_surjective {m : Type*} [Fintype m] [DecidableEq m]
    (D : Coord3 →L[ℝ] (m → ℝ))
    (hD : LinearIndependent ℝ (gradientColumns D).col) : Function.Surjective D := by
  let E := gradientColumns D
  have hh : Eᵀ * (((Eᵀ * E)⁻¹ * Eᵀ)ᵀ) = 1 := by
    rw [← Matrix.transpose_mul, gram_leftInverse E hD, Matrix.transpose_one]
  have hs := Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨_, hh⟩
  intro y
  obtain ⟨x, hx⟩ := hs y
  exact ⟨x, (gradientColumns_apply D x).symm.trans hx⟩

def TwoFieldRankRegular (u : Coord3 → Fin 2 → ℝ) (O : Set Coord3) : Prop :=
  (∀ x ∈ O, LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col) ∨
  (∃ (v : Coord3 → ℝ) (l κ : Fin 2 → ℝ),
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) v O ∧ (∃ j, l j ≠ 0) ∧
    (∀ x ∈ O, fderiv ℝ v x ≠ 0) ∧
    (∀ x ∈ O, ∀ j, u x j = l j * v x + κ j)) ∨
  ∃ κ : Fin 2 → ℝ, ∀ x ∈ O, u x = κ

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def RegularPatch (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (O : Set Coord3) : Prop :=
  IsOpen O ∧ ContDiffOn ℝ (↑(⊤ : ℕ∞)) u O ∧
  ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) O ∧ TwoFieldRankRegular u O

def regularRegion (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (U : Set Coord3) : Set Coord3 :=
  ⋃ (O : Set Coord3) (_ : O ⊆ U) (_ : RegularPatch u A O), O

lemma mem_regularRegion_iff {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} {p : Coord3} : p ∈ regularRegion u A U ↔
    ∃ O : Set Coord3, O ⊆ U ∧ RegularPatch u A O ∧ p ∈ O := by
  simp only [regularRegion, mem_iUnion, exists_prop]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatchLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma TwoFieldRankRegular.linearCoordinates {u : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (hO : IsOpen O) (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u O)
    (h : TwoFieldRankRegular u O) (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    TwoFieldRankRegular (fun x => Q (u (P x))) (P ⁻¹' O) := by
  rcases h with h|h|⟨κ,hκ⟩
  · left
    intro x hx
    have hd := (hu.differentiableOn (by simp) (P x) hx).differentiableAt (hO.mem_nhds hx)
    have he := Q.hasFDerivAt.comp x (hd.hasFDerivAt.comp x P.hasFDerivAt)
    change LinearIndependent ℝ (gradientColumns (fderiv ℝ (Q ∘ u ∘ P) x)).col
    rw [he.fderiv]
    apply gradientColumns_rank
    exact Q.surjective.comp ((gradientColumns_surjective _ (h (P x) hx)).comp P.surjective)
  · right; left
    obtain ⟨v,l,κ,hv,hl,hd,he⟩ := h
    refine ⟨fun x => v (P x),Q l,Q κ,?_,?_,?_,?_⟩
    · exact hv.comp P.contDiff.contDiffOn (fun _ hx => hx)
    · obtain ⟨j,hj⟩ := hl
      by_contra! hh
      have hz : Q l=0 := funext hh
      have hl0 : l=0 := Q.injective (hz.trans (map_zero Q).symm)
      exact hj (congrFun hl0 j)
    · intro x hx hz
      have hxv := (hv.differentiableOn (by simp) (P x) hx).differentiableAt (hO.mem_nhds hx)
      have hh := (hxv.hasFDerivAt.comp x P.hasFDerivAt).fderiv
      change fderiv ℝ (v ∘ P) x=0 at hz
      rw [hh] at hz
      apply hd (P x) hx
      ext y
      have h := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (P.symm y)) hz
      change (fderiv ℝ v (P x)) (P (P.symm y))=0 at h
      simpa only [P.apply_symm_apply,_root_.zero_apply] using h
    · intro x hx j
      have hh : u (P x)=v (P x) • l+κ := by
        ext i
        simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using he (P x) hx i
      change Q (u (P x)) j=Q l j*v (P x)+Q κ j
      rw [hh,map_add,map_smul]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  · exact Or.inr (Or.inr ⟨Q κ,fun x hx => congrArg Q (hκ (P x) hx)⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_LinearFiniteEndTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

local instance linearFiniteEndTransportMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

def linearTensorPullback (P : Coord3 ≃L[ℝ] Coord3) (A : Coord3 → Mat3) (x : Coord3) : Mat3 :=
  operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)*A (P x)*
    (operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3))ᵀ

lemma operatorMatrix_equiv_symm_mul (P : Coord3 ≃L[ℝ] Coord3) :
    operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)*operatorMatrix (P : Coord3 →L[ℝ] Coord3)=1 := by
  rw [←operatorMatrix_comp]
  have he : (P.symm : Coord3 →L[ℝ] Coord3).comp (P : Coord3 →L[ℝ] Coord3)=ContinuousLinearMap.id ℝ Coord3 := by
    ext x i
    exact congrFun (P.symm_apply_apply x) i
  rw [he,operatorMatrix_id]

lemma linearTensorPullback_symmetric (P : Coord3 ≃L[ℝ] Coord3)
    {A : Coord3 → Mat3} (hA : ∀ x,(A x).IsSymm) (x : Coord3) :
    (linearTensorPullback P A x).IsSymm := by
  unfold linearTensorPullback Matrix.IsSymm
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,(hA _).eq]
  simp only [Matrix.mul_assoc]

local instance linearFiniteEndTransportBorelSpace_r0281e9_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
lemma linearTensorPullback_measurable (P : Coord3 ≃L[ℝ] Coord3)
    {A : Coord3 → Mat3} (hA : Measurable A) : Measurable (linearTensorPullback P A) :=
  measurable_real_matrix_mul (measurable_real_matrix_mul measurable_const
    (hA.comp P.continuous.measurable)) measurable_const

lemma gradientColumns_linearCoordinates {u : Coord3 → Fin 2 → ℝ}
    {x : Coord3} (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (hu : DifferentiableAt ℝ u (P x)) :
    gradientColumns (fderiv ℝ (fun y => Q (u (P y))) x)=
      (operatorMatrix (P : Coord3 →L[ℝ] Coord3))ᵀ*gradientColumns (fderiv ℝ u (P x))*
        (operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)))ᵀ := by
  change gradientColumns (fderiv ℝ (Q ∘ u ∘ P) x)=_
  rw [(Q.hasFDerivAt.comp x (hu.hasFDerivAt.comp x P.hasFDerivAt)).fderiv]
  change (operatorMatrix ((Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)).comp
    ((fderiv ℝ u (P x)).comp (P : Coord3 →L[ℝ] Coord3))))ᵀ=_
  simp only [operatorMatrix_comp,Matrix.transpose_mul,Matrix.mul_assoc]
  rfl

lemma linearTensorPullback_columns (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (A : Coord3 → Mat3)
    {u : Coord3 → Fin 2 → ℝ} {x : Coord3} (hu : DifferentiableAt ℝ u (P x)) :
    linearTensorPullback P A x*gradientColumns (fderiv ℝ (fun y => Q (u (P y))) x)=
      operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)*
        (A (P x)*gradientColumns (fderiv ℝ u (P x)))*
        (operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)))ᵀ := by
  rw [gradientColumns_linearCoordinates P Q hu]
  have he : (operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3))ᵀ*
      (operatorMatrix (P : Coord3 →L[ℝ] Coord3))ᵀ=1 := by
    have he0 := operatorMatrix_equiv_symm_mul P.symm
    simp only [ContinuousLinearEquiv.symm_symm] at he0
    rw [←Matrix.transpose_mul,he0,Matrix.transpose_one]
  simp only [linearTensorPullback,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3))ᵀ,he,Matrix.one_mul]

lemma RegularPatch.linearCoordinates {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    RegularPatch (fun x => Q (u (P x)))
      (fun x => ⟨linearTensorPullback P (fun y => (A y).val) x,
        linearTensorPullback_symmetric P (fun y => (A y).property) x⟩) (P ⁻¹' O) := by
  refine ⟨h.1.preimage P.continuous,?_,?_,h.2.2.2.linearCoordinates h.1 h.2.1 P Q⟩
  · exact Q.contDiff.comp_contDiffOn (h.2.1.comp P.contDiff.contDiffOn (fun _ hx => hx))
  · change ContDiffOn ℝ (↑(⊤ : ℕ∞)) (linearTensorPullback P (fun y => (A y).val)) _
    apply (h.1.preimage P.continuous).contDiffOn_iff.mpr
    intro x hx
    exact contDiffAt_matrix_mul (contDiffAt_matrix_mul contDiffAt_const
      ((h.2.2.1.contDiffAt (h.1.mem_nhds hx)).comp x P.contDiff.contDiffAt)) contDiffAt_const

lemma mem_regularRegion_linearCoordinates {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) {x : Coord3}
    (h : P x∈regularRegion u A U) :
    x∈regularRegion (fun y => Q (u (P y)))
      (fun y => ⟨linearTensorPullback P (fun z => (A z).val) y,
        linearTensorPullback_symmetric P (fun z => (A z).property) y⟩) (P ⁻¹' U) := by
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp h
  exact mem_regularRegion_iff.mpr ⟨P ⁻¹' O,preimage_mono hOU,hO.linearCoordinates P Q,hxO⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalTensorPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma identity_matrix_energy_bounds : ∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ v : Fin 3 → ℝ,
    c*‖v‖^2≤v ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ)*ᵥv) ∧
      v ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ)*ᵥv)≤C*‖v‖^2 := by
  have hp (u : Unit) (_ : u∈({()} : Set Unit)) (v : Fin 3 → ℝ) (hv : v≠0) :
      0<v ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ)*ᵥv) := by
    rw [Matrix.one_mulVec]
    exact lt_of_le_of_ne (Finset.sum_nonneg (fun k _ => mul_self_nonneg (v k)))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hv))
  obtain ⟨c,C,hc,hcC,h⟩ := compact_matrix_energy_bounds isCompact_singleton
    (fun _ : Unit => (1 : Matrix (Fin 3) (Fin 3) ℝ)) continuousOn_const hp
  exact ⟨c,C,hc,hcC,h () (mem_singleton ())⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalChildIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceChild_image_ball (k : Fin 2) {D : Set (Fin 3 → ℝ)}
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    ∀ y∈sourceChildCoordinates (actualChildSign k) '' D,WithLp.toLp 2 y∈ball := by
  rintro _ ⟨y,hy,rfl⟩
  exact sourceChildEuclidean_ball k ⟨WithLp.toLp 2 y,hb y hy,rfl⟩

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalEndRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def physicalEndRegion (i : Fin 3) : Set (Fin 3 → ℝ) :=
  Fin.cases (sourceClosedCollarBand 0 centralThickness)
    (fun k => (sourceChildHomeomorph (actualChildSign k)).symm ⁻¹'
      sourceClosedCollarBand (-centralThickness) 0) i

lemma physicalEndRegion_compact (i : Fin 3) : IsCompact (physicalEndRegion i) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact isCompact_sourceClosedCollarBand (by norm_num) (by norm_num [centralThickness])
  · exact (sourceChildHomeomorph (actualChildSign k)).symm.isCompact_preimage.mpr
      (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma physicalEndRegion_subset_ball (i : Fin 3) {y : Fin 3 → ℝ}
    (hy : y∈physicalEndRegion i) : WithLp.toLp 2 y∈ball := by
  revert hy
  refine Fin.cases ?_ (fun k => ?_) i
  · intro hy
    exact sourceBand_mem_ball ⟨(show -(1:ℝ)/100≤0 by norm_num).trans hy.1,
      hy.2.trans (by norm_num [centralThickness])⟩
  · intro hy
    apply sourceChild_image_ball (D := sourceClosedCollarBand (-centralThickness) 0) k
      (fun z hz => sourceBand_mem_ball
      ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hz.1,
        hz.2.trans (show (0:ℝ)≤1/100 by norm_num)⟩) y
    exact ⟨(sourceChildHomeomorph (actualChildSign k)).symm y,hy,
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AntisymmetricFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (f : E → ℝ) (x : E) : ℝ := fderiv ℝ f x v

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CompactFluxDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def coordinateDivergence (F : Coord3 → Coord3) (x : Coord3) : ℝ :=
  ∑ i : Fin 3,fderiv ℝ (fun y => F y i) x (Pi.single i 1)

lemma coordinate_fderiv_expansion (ψ : Coord3 → ℝ) (x v : Coord3) :
    fderiv ℝ ψ x v=∑ i : Fin 3,v i*fderiv ℝ ψ x (Pi.single i 1) := by
  have he : v=∑ i : Fin 3,v i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp

lemma coordinateDivergence_smooth {F : Coord3 → Coord3}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coordinateDivergence F) := by
  apply ContDiff.sum; intro i _
  exact (((contDiff_pi.mp hF) i).fderiv_right (by simp)).clm_apply contDiff_const

theorem coordinateDivergence_weak {F : Coord3 → Coord3}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (hs : HasCompactSupport F)
    (ψ : Coord3 → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    (∫ x,fderiv ℝ ψ x (F x))= -(∫ x,ψ x*coordinateDivergence F x) := by
  have hc (i : Fin 3) : HasCompactSupport (fun x => F x i) :=
    hs.comp_left (g := fun v : Coord3 => v i) rfl
  have hFi (i : Fin 3) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => F x i) :=
    contDiff_pi.mp hF i
  have hdψ (i : Fin 3) : Continuous (fun x => fderiv ℝ ψ x (Pi.single i 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdF (i : Fin 3) : Continuous (fun x => fderiv ℝ (fun y => F y i) x (Pi.single i 1)) :=
    ((hFi i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hi₁ (i : Fin 3) : Integrable (fun x => F x i*fderiv ℝ ψ x (Pi.single i 1)) :=
    ((hFi i).continuous.mul (hdψ i)).integrable_of_hasCompactSupport (hc i).mul_right
  have hi₂ (i : Fin 3) : Integrable (fun x => ψ x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)) :=
    (hψ.continuous.mul (hdF i)).integrable_of_hasCompactSupport ((hc i).fderiv_apply ℝ _).mul_left
  have he (i : Fin 3) : (∫ x,F x i*fderiv ℝ ψ x (Pi.single i 1))=
      -(∫ x,ψ x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)) := by
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Coord3))
      (f := ψ) (g := fun x => F x i) (v := Pi.single i 1)
      (by simpa only [mul_comm] using hi₁ i) (hi₂ i)
      ((hψ.continuous.mul (hFi i).continuous).integrable_of_hasCompactSupport (hc i).mul_left)
      (fun x _ => hψ.differentiable (by simp) x)
      (fun x _ => (hFi i).differentiable (by simp) x)
    have hh' : (∫ x,fderiv ℝ ψ x (Pi.single i 1)*F x i)=
        (∫ x,F x i*fderiv ℝ ψ x (Pi.single i 1)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
    rw [hh'] at hh
    linarith
  have hex : (fun x => fderiv ℝ ψ x (F x))=
      (fun x => ∑ i : Fin 3,F x i*fderiv ℝ ψ x (Pi.single i 1)) := by
    funext x
    exact coordinate_fderiv_expansion ψ x (F x)
  rw [hex]
  simp only [coordinateDivergence,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),integral_finsetSum _ (fun i _ => hi₂ i)]
  simp_rw [he]
  simp only [Finset.sum_neg_distrib]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_LinearFluxWeakTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma continuousLinearEquiv_det_ne_zero (P : Coord3 ≃L[ℝ] Coord3) :
    (P : Coord3 →L[ℝ] Coord3).det≠0 := by
  have hd : (fderiv ℝ (P : Coord3 → Coord3) 0).det≠0 :=
    fderiv_equiv_det_ne_zero P.toEquiv P.differentiable P.symm.differentiable 0
  simpa only [ContinuousLinearEquiv.fderiv] using hd

lemma continuousLinearEquiv_quasiMeasurePreserving (P : Coord3 ≃L[ℝ] Coord3) :
    Measure.QuasiMeasurePreserving P volume volume :=
  Measure.ContinuousLinearMap.quasiMeasurePreserving volume (P : Coord3 →L[ℝ] Coord3)
    (continuousLinearEquiv_det_ne_zero P)

lemma pi_clm_apply_sum {n : ℕ} (D : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    D v=∑ i,v i*D (Pi.single i 1) := by
  have he : v=∑ i,v i • Pi.single i 1 := by
    simpa only [←Pi.single_smul,smul_eq_mul,mul_one] using
      (Finset.univ_sum_single v).symm
  calc
    D v=D (∑ i,v i • Pi.single i 1) := congrArg D he
    _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]

lemma coordinate_flux_pairing (F : Coord3 → Coord3) (ψ : SmoothScalar Coord3) (x : Coord3) :
    fderiv ℝ ψ.val x (F x)=∑ i,F x i*(smoothDirection (Pi.single i 1) ψ).val x :=
  pi_clm_apply_sum _ _

def linearFluxPullback (P : Coord3 ≃L[ℝ] Coord3) (F : Coord3 → Coord3) (x : Coord3) : Coord3 :=
  P.symm (F (P x))

lemma linearFluxPullback_weak (P : Coord3 ≃L[ℝ] Coord3)
    {F : Coord3 → Coord3} {U : Set Coord3}
    (hF : ∀ ψ : SmoothScalar Coord3,HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x (F x))=0)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val⊆P ⁻¹' U) :
    (∫ x,fderiv ℝ ψ.val x (linearFluxPullback P F x))=0 := by
  let φ : SmoothScalar Coord3 := ⟨ψ.val ∘ P.symm,(smoothScalar_contDiff ψ).comp P.symm.contDiff⟩
  have hφc : HasCompactSupport φ.val := hc.comp_homeomorph P.symm.toHomeomorph
  have hφs : tsupport φ.val⊆U := by
    intro y hy
    have hh : P.symm y∈tsupport ψ.val := tsupport_comp_subset_preimage ψ.val P.symm.continuous hy
    simpa only [mem_preimage,P.apply_symm_apply] using hs hh
  have he := piolaFlux_pairing volume P.symm.toEquiv P.symm.differentiable
    (fderiv_equiv_det_ne_zero P.symm.toEquiv P.symm.differentiable P.differentiable)
    F ψ.val ((smoothScalar_contDiff ψ).differentiable (by simp))
  have he' : (∫ x,|(P.symm : Coord3 →L[ℝ] Coord3).det|⁻¹ *
      fderiv ℝ ψ.val x (linearFluxPullback P F x))=(0 : ℝ) := by
    calc
      _=(∫ x,fderiv ℝ ψ.val x (piolaFlux P.symm.toEquiv F x)) := by
        congr 1
        funext x
        have hd : fderiv ℝ P.symm.toEquiv (P.symm.toEquiv.symm x)=
            (P.symm : Coord3 →L[ℝ] Coord3) := P.symm.fderiv
        simp only [piolaFlux,hd,map_smul,smul_eq_mul]
        rfl
      _ = _ := he.trans (hF φ hφc hφs)
  rw [integral_const_mul] at he'
  exact (mul_eq_zero.mp he').resolve_left (inv_ne_zero (abs_ne_zero.mpr
    (continuousLinearEquiv_det_ne_zero P.symm)))

lemma continuous_flux_compact_test_integrable {F : Coord3 → Coord3} (hF : Continuous F)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val) :
    Integrable (fun x => fderiv ℝ ψ.val x (F x)) := by
  simp_rw [coordinate_flux_pairing]
  apply integrable_finsetSum
  intro i _
  exact (((continuous_apply i).comp hF).mul
    (smoothScalar_contDiff (smoothDirection (Pi.single i 1) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (Pi.single i 1) hc).mul_left

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma matrix_mul_transpose_col_sum {n : ℕ} (M : Matrix (Fin 3) (Fin n) ℝ)
    (N : Matrix (Fin 2) (Fin n) ℝ) (j : Fin 2) :
    (M*Nᵀ).col j=∑ k,N j k • M.col k := by
  ext i
  simp only [Matrix.col_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,mul_comm]

def linearColumnsPullback (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    (G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) (x : Coord3) : Matrix (Fin 3) (Fin 2) ℝ :=
  operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)*G (P x)*
    (operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)))ᵀ

lemma linearColumnsPullback_col (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    (G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) (x : Coord3) (j : Fin 2) :
    (linearColumnsPullback P Q G x).col j=
      ∑ k,operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) j k •
        linearFluxPullback P (fun y => (G y).col k) x := by
  rw [linearColumnsPullback,matrix_mul_transpose_col_sum]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact operatorMatrix_mulVec (P.symm : Coord3 →L[ℝ] Coord3) ((G (P x)).col k)

lemma linearColumnsPullback_C1 (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    {G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ} (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (linearColumnsPullback P Q G) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_matrix_mul (contDiffAt_matrix_mul contDiffAt_const
    ((hG.comp P.contDiff).contDiffAt)) contDiffAt_const

lemma linearColumnsPullback_weak (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    {G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ} (hGc : Continuous G) {U : Set Coord3}
    (hG : ∀ (j : Fin 2) (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x ((G x).col j))=0)
    (j : Fin 2) (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val⊆P ⁻¹' U) :
    Integrable (fun x => fderiv ℝ ψ.val x ((linearColumnsPullback P Q G x).col j)) ∧
      (∫ x,fderiv ℝ ψ.val x ((linearColumnsPullback P Q G x).col j))=0 := by
  have hcont (k : Fin 2) : Continuous (linearFluxPullback P (fun y => (G y).col k)) := by
    have hgk : Continuous (fun y => (G y).col k) :=
      continuous_pi fun i => (continuous_apply k).comp ((continuous_apply i).comp hGc)
    exact P.symm.continuous.comp (hgk.comp P.continuous)
  have hI (k : Fin 2) := continuous_flux_compact_test_integrable (hcont k) ψ hc
  have hw (k : Fin 2) := linearFluxPullback_weak P (hG k) ψ hc hs
  have he (x : Coord3) : fderiv ℝ ψ.val x ((linearColumnsPullback P Q G x).col j)=
      ∑ k,operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) j k *
        fderiv ℝ ψ.val x (linearFluxPullback P (fun y => (G y).col k) x) := by
    rw [linearColumnsPullback_col,map_sum]
    simp only [map_smul,smul_eq_mul]
  simp_rw [he]
  constructor
  · exact integrable_finsetSum _ (fun k _ => (hI k).const_mul _)
  · rw [integral_finsetSum _ (fun k _ => (hI k).const_mul _)]
    simp only [integral_const_mul,hw,mul_zero,Finset.sum_const_zero]

lemma linearTensorPullback_C1_representative (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ))
    {u : Coord3 → Fin 2 → ℝ} (hu : Differentiable ℝ u) {A : Coord3 → Mat3}
    {G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ}
    (hG : ∀ᵐ x : Coord3,A x*gradientColumns (fderiv ℝ u x)=G x) :
    ∀ᵐ x : Coord3,linearTensorPullback P A x*
      gradientColumns (fderiv ℝ (fun y => Q (u (P y))) x)=linearColumnsPullback P Q G x := by
  filter_upwards [(continuousLinearEquiv_quasiMeasurePreserving P).ae hG] with x hx
  rw [linearTensorPullback_columns P Q A (hu _),hx]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DirectionCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

section Direction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

@[simp] lemma direction_const (v x : E) (c : ℝ) : direction v (fun _ : E => c) x = 0 := by
  simp [direction]
end Direction

@[simp] lemma direction_coord (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => y j) x = if j=i then 1 else 0 := by
  let P : Coord3 →L[ℝ] ℝ := ContinuousLinearMap.proj j
  change (fderiv ℝ P x) (Pi.single i 1) = _
  rw [P.fderiv]
  change (Pi.single i 1 : Coord3) j = _
  simp [Pi.single_apply,eq_comm]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatchTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.translate {u : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (h : TwoFieldRankRegular u O) (c : Coord3) (d : Fin 2 → ℝ) :
    TwoFieldRankRegular (fun x => u (x-c)+d) ((fun x => x-c) ⁻¹' O) := by
  rcases h with h|h|⟨κ,hκ⟩
  · left
    intro x hx
    rw [fderiv_add_const,fderiv_comp_sub]
    exact h (x-c) hx
  · right; left
    obtain ⟨v,l,κ,hv,hl,hd,he⟩ := h
    refine ⟨fun x => v (x-c),l,κ+d,?_,hl,?_,?_⟩
    · exact hv.comp (contDiff_id.sub contDiff_const).contDiffOn (fun _ hx => hx)
    · intro x hx
      rw [fderiv_comp_sub]
      exact hd (x-c) hx
    · intro x hx j
      simp only [Pi.add_apply,he (x-c) hx j]
      ring
  · exact Or.inr (Or.inr ⟨κ+d,fun x hx => by dsimp only; rw [hκ (x-c) hx]⟩)

lemma RegularPatch.translate {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3} {O : Set Coord3}
    (h : RegularPatch u A O) (c : Coord3) (d : Fin 2 → ℝ) :
    RegularPatch (fun x => u (x-c)+d) (fun x => A (x-c)) ((fun x => x-c) ⁻¹' O) := by
  refine ⟨h.1.preimage (continuous_id.sub continuous_const),?_,?_,h.2.2.2.translate c d⟩
  · exact (h.2.1.comp (contDiff_id.sub contDiff_const).contDiffOn (fun _ hx => hx)).add contDiffOn_const
  · exact h.2.2.1.comp (contDiff_id.sub contDiff_const).contDiffOn (fun _ hx => hx)

lemma mem_regularRegion_translate {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} {x c : Coord3} (h : x-c∈regularRegion u A U) (d : Fin 2 → ℝ) :
    x∈regularRegion (fun y => u (y-c)+d) (fun y => A (y-c)) ((fun y => y-c) ⁻¹' U) := by
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp h
  exact mem_regularRegion_iff.mpr ⟨(fun y => y-c) ⁻¹' O,preimage_mono hOU,hO.translate c d,hxO⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_LinearTensorEllipticity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma matrix_congruence_energy (N A : Mat3) (v : Coord3) :
    v ⬝ᵥ ((N*A*Nᵀ)*ᵥv)=(Nᵀ*ᵥv) ⬝ᵥ (A*ᵥ(Nᵀ*ᵥv)) := by
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  calc
    _ = (A*ᵥ(Nᵀ*ᵥv)) ⬝ᵥ (Nᵀ*ᵥv) := by
      simpa only [Matrix.transpose_transpose] using
        Matrix.dotProduct_transpose_mulVec Nᵀ v (A*ᵥ(Nᵀ*ᵥv))
    _ = _ := dotProduct_comm _ _

lemma linearTensorPullback_elliptic (P : Coord3 ≃L[ℝ] Coord3)
    {A : Coord3 → Mat3} {c C : ℝ} (hc : 0 < c) (hcC : c≤C)
    (hA : ∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ(A x*ᵥw) ∧ w ⬝ᵥ(A x*ᵥw)≤C*(w ⬝ᵥ w)) :
    ∃ l L : ℝ,0<l ∧ l<L ∧ ∀ x (v : Coord3),
      l*(v ⬝ᵥ v)≤v ⬝ᵥ(linearTensorPullback P A x*ᵥv) ∧
        v ⬝ᵥ(linearTensorPullback P A x*ᵥv)≤L*(v ⬝ᵥ v) := by
  let N := operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)
  have hn (v : Coord3) (hv : v≠0) : Nᵀ*ᵥv≠0 := by
    intro hz
    have he : (operatorMatrix (P : Coord3 →L[ℝ] Coord3))ᵀ*(Nᵀ)=1 := by
      rw [←Matrix.transpose_mul,operatorMatrix_equiv_symm_mul,Matrix.transpose_one]
    have hh := congrArg (fun w => (operatorMatrix (P : Coord3 →L[ℝ] Coord3))ᵀ*ᵥw) hz
    rw [Matrix.mulVec_mulVec,he,Matrix.one_mulVec,Matrix.mulVec_zero] at hh
    exact hv hh
  have he (v : Coord3) : v ⬝ᵥ ((N*Nᵀ)*ᵥv)=(Nᵀ*ᵥv) ⬝ᵥ (Nᵀ*ᵥv) := by
    simpa only [Matrix.mul_one,Matrix.one_mulVec] using matrix_congruence_energy N 1 v
  obtain ⟨l,L,hl,hlL,hbound⟩ := compact_matrix_energy_bounds isCompact_singleton
    (fun _ : Unit => N*Nᵀ) continuousOn_const (fun _ _ v hv => by
      rw [he]
      exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
        (Ne.symm (mt dotProduct_self_eq_zero.mp (hn v hv))))
  obtain ⟨d,D,hd,hdD,hid⟩ := identity_matrix_energy_bounds
  have hD : 0<D := hd.trans hdD
  have hL : 0<L := hl.trans hlL
  refine ⟨c*l/D,C*L/d,div_pos (mul_pos hc hl) hD,?_,?_⟩
  · have heq : (c*l/D)*D=c*l := div_mul_cancel₀ _ hD.ne'
    have heq' : (C*L/d)*d=C*L := div_mul_cancel₀ _ hd.ne'
    have hcl : c*l<C*L := (mul_lt_mul_of_pos_left hlL hc).trans_le
      (mul_le_mul_of_nonneg_right hcC hL.le)
    have hup : 0<C*L/d := div_pos (mul_pos (hc.trans_le hcC) hL) hd
    nlinarith [mul_lt_mul_of_pos_left hdD hup]
  · intro x v
    have h := hbound () (mem_singleton ()) v
    rw [he] at h
    have hi := hid v
    simp only [Matrix.one_mulVec] at hi
    have hg := hA (P x) (Nᵀ*ᵥv)
    change _ ≤ v ⬝ᵥ ((N*A (P x)*Nᵀ)*ᵥv) ∧ v ⬝ᵥ ((N*A (P x)*Nᵀ)*ᵥv) ≤ _
    simp only [matrix_congruence_energy]
    constructor
    · have h1 := mul_le_mul_of_nonneg_left hi.2 (div_nonneg (mul_nonneg hc.le hl.le) hD.le)
      have h2 := mul_le_mul_of_nonneg_left h.1 hc.le
      have heq : (c*l/D)*D=c*l := div_mul_cancel₀ _ hD.ne'
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_left hi.1 (div_nonneg
          (mul_nonneg (hc.le.trans hcC) hL.le) hd.le)
      have h2 := mul_le_mul_of_nonneg_left h.2 (hc.le.trans hcC)
      have heq : (C*L/d)*d=C*L := div_mul_cancel₀ _ hd.ne'
      nlinarith

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma flux_translate_weak {F : Coord3 → Coord3} {U : Set Coord3} (c : Coord3)
    (hF : ∀ ψ : SmoothScalar Coord3,HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x (F x))=0)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val⊆(fun x => x-c) ⁻¹' U) :
    (∫ x,fderiv ℝ ψ.val x (F (x-c)))=0 := by
  let φ : SmoothScalar Coord3 := ⟨fun y => ψ.val (y+c),
    (smoothScalar_contDiff ψ).comp (contDiff_id.add contDiff_const)⟩
  have hφc : HasCompactSupport φ.val := hc.comp_homeomorph (Homeomorph.addRight c)
  have hφs : tsupport φ.val⊆U := by
    intro y hy
    have hh : y+c∈tsupport ψ.val := tsupport_comp_subset_preimage ψ.val
      (continuous_id.add continuous_const) hy
    simpa only [mem_preimage,add_sub_cancel_right] using hs hh
  calc
    _ = ∫ y,fderiv ℝ ψ.val (y+c) (F y) := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x => fderiv ℝ ψ.val x (F (x-c))) c).symm
    _ = ∫ y,fderiv ℝ φ.val y (F y) := by simp only [φ,fderiv_comp_add_right]
    _ = 0 := hF φ hφc hφs

lemma translatedTensor_C1_representative {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Mat3}
    {G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ} (c : Coord3) (d : Fin 2 → ℝ)
    (hG : ∀ᵐ x : Coord3,A x*gradientColumns (fderiv ℝ u x)=G x) :
    ∀ᵐ x : Coord3,A (x-c)*gradientColumns
      (fderiv ℝ (fun y => u (y-c)+d) x)=G (x-c) := by
  filter_upwards [(measurePreserving_sub_right volume c).quasiMeasurePreserving.ae hG] with x hx
  simpa only [fderiv_add_const,fderiv_comp_sub] using hx

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

local instance instMeasurableSpaceMat3 : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

local instance instBorelSpaceMat3_r0281e9_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
structure WeakFiniteTensorPair (U : Set Coord3) where
  v : Coord3 → Fin 2 → ℝ
  E : Coord3 → Mat3
  symm : ∀ x,(E x).IsSymm
  smooth : ContDiff ℝ 2 v
  measurable : Measurable E
  elliptic : ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x w,
    c*(w ⬝ᵥ w)≤w ⬝ᵥ(E x*ᵥw) ∧ w ⬝ᵥ(E x*ᵥw)≤C*(w ⬝ᵥ w)
  regular : ∀ᵐ x : Coord3,x∈U → x∈regularRegion v (fun y => ⟨E y,symm y⟩) U
  G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ
  flux_C1 : ContDiff ℝ 1 G
  constitution : ∀ᵐ x : Coord3,E x*gradientColumns (fderiv ℝ v x)=G x
  weak : ∀ (j : Fin 2) (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val →
    tsupport ψ.val⊆U → (∫ x,fderiv ℝ ψ.val x ((G x).col j))=0

namespace WeakFiniteTensorPair

lemma linear_smooth {U : Set Coord3} (d : WeakFiniteTensorPair U)
    (P : Coord3 ≃L[ℝ] Coord3) (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    ContDiff ℝ 2 (fun x => Q (d.v (P x))) := Q.contDiff.comp (d.smooth.comp P.contDiff)

lemma linear_elliptic {U : Set Coord3} (d : WeakFiniteTensorPair U)
    (P : Coord3 ≃L[ℝ] Coord3) :
    ∃ l L : ℝ,0<l ∧ l≤L ∧ ∀ x w,
      l*(w ⬝ᵥ w)≤w ⬝ᵥ(linearTensorPullback P d.E x*ᵥw) ∧
        w ⬝ᵥ(linearTensorPullback P d.E x*ᵥw)≤L*(w ⬝ᵥ w) := by
  obtain ⟨c,C,hc,hcC,hb⟩ := d.elliptic
  obtain ⟨l,L,hl,hlL,hbound⟩ := linearTensorPullback_elliptic P hc hcC hb
  exact ⟨l,L,hl,hlL.le,hbound⟩

lemma linear_regular {U : Set Coord3} (d : WeakFiniteTensorPair U)
    (P : Coord3 ≃L[ℝ] Coord3) (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    ∀ᵐ x : Coord3,x∈P ⁻¹' U → x∈regularRegion (fun y => Q (d.v (P y)))
      (fun y => ⟨linearTensorPullback P d.E y,linearTensorPullback_symmetric P d.symm y⟩)
      (P ⁻¹' U) := by
  filter_upwards [(continuousLinearEquiv_quasiMeasurePreserving P).ae d.regular] with x hx
  intro hxU
  exact mem_regularRegion_linearCoordinates (u := d.v)
    (A := fun y => ⟨d.E y,d.symm y⟩) (U := U) P Q (x := x) (hx hxU)

def linear {U : Set Coord3} (d : WeakFiniteTensorPair U)
    (P : Coord3 ≃L[ℝ] Coord3) (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    WeakFiniteTensorPair (P ⁻¹' U) where
  v x := Q (d.v (P x))
  E := linearTensorPullback P d.E
  symm := linearTensorPullback_symmetric P d.symm
  smooth := d.linear_smooth P Q
  measurable := linearTensorPullback_measurable P d.measurable
  elliptic := d.linear_elliptic P
  regular := d.linear_regular P Q
  G := linearColumnsPullback P Q d.G
  flux_C1 := linearColumnsPullback_C1 P Q d.flux_C1
  constitution := linearTensorPullback_C1_representative P Q
    (d.smooth.differentiable (by norm_num)) d.constitution
  weak j ψ hc hs := (linearColumnsPullback_weak P Q d.flux_C1.continuous d.weak j ψ hc hs).2

local instance instBorelSpaceMat3_r0281e9_2 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
def translate {U : Set Coord3} (d : WeakFiniteTensorPair U) (c : Coord3) (b : Fin 2 → ℝ) :
    WeakFiniteTensorPair ((fun x => x-c) ⁻¹' U) where
  v x := d.v (x-c)+b
  E x := d.E (x-c)
  symm x := d.symm (x-c)
  smooth := (d.smooth.comp (contDiff_id.sub contDiff_const)).add contDiff_const
  measurable := d.measurable.comp (measurable_id.sub measurable_const)
  elliptic := by
    obtain ⟨l,L,hl,hlL,hb⟩ := d.elliptic
    exact ⟨l,L,hl,hlL,fun x => hb (x-c)⟩
  regular := by
    filter_upwards [(measurePreserving_sub_right volume c).quasiMeasurePreserving.ae d.regular] with x hx
    exact fun hxU => mem_regularRegion_translate (hx hxU) b
  G x := d.G (x-c)
  flux_C1 := d.flux_C1.comp (contDiff_id.sub contDiff_const)
  constitution := translatedTensor_C1_representative c b d.constitution
  weak j := flux_translate_weak c (d.weak j)

end WeakFiniteTensorPair
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalSymmetricPiola
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def localPiolaTensor (X : OpenPartialHomeomorph Coord3 Coord3)
    (B : Coord3 → Mat3) (y : Coord3) : Mat3 := by
  classical
  exact if y∈X.target then
    |(fderiv ℝ X (X.symm y)).det|⁻¹ •
      (operatorMatrix (fderiv ℝ X (X.symm y))*B (X.symm y)*
        (operatorMatrix (fderiv ℝ X (X.symm y)))ᵀ)
  else 0

lemma localPiolaTensor_isSymm (X : OpenPartialHomeomorph Coord3 Coord3)
    (B : Coord3 → Mat3) (hB : ∀ x,(B x).IsSymm) (y : Coord3) :
    (localPiolaTensor X B y).IsSymm := by
  by_cases hy : y∈X.target
  · simp only [localPiolaTensor,ite_eq_left hy]
    apply Matrix.IsSymm.smul
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,(hB _).eq]
    simp only [Matrix.mul_assoc]
  · simp only [localPiolaTensor,ite_eq_right hy]
    exact (Matrix.isSymm_zero (n := Fin 3) (α := ℝ))

lemma localPiolaTensor_support (X : OpenPartialHomeomorph Coord3 Coord3)
    (B : Coord3 → Mat3) :
    Function.support (localPiolaTensor X B)⊆X '' (Function.support B∩X.source) := by
  intro y hy
  by_cases hyt : y∈X.target
  · refine ⟨X.symm y,⟨?_,X.map_target hyt⟩,X.right_inv hyt⟩
    intro hz
    exact hy (by simp [localPiolaTensor,hyt,hz])
  · exact False.elim (hy (by simp [localPiolaTensor,hyt]))

lemma localPiolaTensor_compact (X : OpenPartialHomeomorph Coord3 Coord3)
    (B : Coord3 → Mat3) (hc : HasCompactSupport B) (hs : tsupport B⊆X.source) :
    HasCompactSupport (localPiolaTensor X B) ∧ tsupport (localPiolaTensor X B)⊆X.target := by
  have hci : IsCompact (X '' tsupport B) := hc.image_of_continuousOn (X.continuousOn.mono hs)
  have hsub : tsupport (localPiolaTensor X B)⊆X '' tsupport B :=
    closure_minimal ((localPiolaTensor_support X B).trans
      (image_mono (fun _ hx => subset_closure hx.1))) hci.isClosed
  exact ⟨hci.of_isClosed_subset isClosed_closure hsub,hsub.trans (by
    rintro y ⟨x,hx,rfl⟩; exact X.map_source (hs hx))⟩

lemma localPiolaTensor_smooth (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (B : Coord3 → Mat3) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B)
    (hc : HasCompactSupport B) (hs : tsupport B⊆X.source) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (localPiolaTensor X B) := by
  apply contDiff_of_contDiffOn_tsupport X.open_target _ (localPiolaTensor_compact X B hc hs).2
  apply X.open_target.contDiffOn_iff.mpr
  intro y hy
  have hxi := hXi.contDiffAt (X.open_target.mem_nhds hy)
  have hx := hX.contDiffAt (X.open_source.mem_nhds (X.map_target hy))
  have hd : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun z => fderiv ℝ X (X.symm z)) y :=
    (hx.fderiv_right (by simp)).comp y hxi
  have hd0 := local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
    (hXi.differentiableOn (by simp)) (X.map_target hy)
  have hdM := (operatorMatrix_contDiff (m := Fin 3) (n := Fin 3)).contDiffAt.comp y hd
  have hdet := ((contDiff_clm_det (E := Coord3) (↑(⊤ : ℕ∞))).contDiffAt.comp y hd).abs hd0
  have hformula := (hdet.inv (abs_ne_zero.mpr hd0)).smul
    (contDiffAt_matrix_mul (contDiffAt_matrix_mul hdM (hB.contDiffAt.comp y hxi))
      (contDiffAt_matrix_transpose hdM))
  apply hformula.congr_of_eventuallyEq
  filter_upwards [X.open_target.mem_nhds hy] with z hz
  simp only [localPiolaTensor,ite_eq_left hz]
  rfl

lemma operatorMatrix_local_inverse_fderiv (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    {x : Coord3} (hx : x∈X.source) :
    operatorMatrix (fderiv ℝ X.symm (X x))=(operatorMatrix (fderiv ℝ X x))⁻¹ := by
  have h := congrArg operatorMatrix (local_fderiv_symm_comp X hX hXi hx)
  rw [operatorMatrix_comp,operatorMatrix_id] at h
  exact (Matrix.inv_eq_left_inv h).symm

lemma gradientColumns_local_recomposition (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    (u : Coord3 → Fin 2 → ℝ) (hu : DifferentiableOn ℝ u X.source)
    {x : Coord3} (hx : x∈X.source) :
    gradientColumns (fderiv ℝ (u∘X.symm) (X x))=
      pushGradient (operatorMatrix (fderiv ℝ X x)) (gradientColumns (fderiv ℝ u x)) := by
  have hux : DifferentiableAt ℝ u (X.symm (X x)) := by
    rw [X.left_inv hx]
    exact (hu x hx).differentiableAt (X.open_source.mem_nhds hx)
  have hix := (hXi _ (X.map_source hx)).differentiableAt (X.open_target.mem_nhds (X.map_source hx))
  rw [fderiv_comp (X x) hux hix,X.left_inv hx]
  change (operatorMatrix ((fderiv ℝ u x).comp (fderiv ℝ X.symm (X x))))ᵀ=_
  rw [operatorMatrix_comp,Matrix.transpose_mul,operatorMatrix_local_inverse_fderiv X hX hXi hx]
  rfl

theorem localPiolaTensor_columns (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    (B : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ)
    (hu : DifferentiableOn ℝ u X.source) (j : Fin 2) (y : Coord3) :
    (localPiolaTensor X B y*gradientColumns (fderiv ℝ (u∘X.symm) y)).col j=
      localPiolaFlux X (fun x => (B x*gradientColumns (fderiv ℝ u x)).col j) y := by
  by_cases hy : y∈X.target
  · let x := X.symm y
    have hx : x∈X.source := X.map_target hy
    have hxy : X x=y := X.right_inv hy
    rw [←hxy,gradientColumns_local_recomposition X hX hXi u hu hx]
    have hd : (operatorMatrix (fderiv ℝ X x)).det≠0 := by
      rw [operatorMatrix_det]
      exact local_fderiv_det_ne_zero X hX hXi hx
    simp only [localPiolaTensor,ite_eq_left (X.map_source hx),X.left_inv hx,
      Matrix.smul_mul,Matrix.mul_assoc,pushGradient_leftInverse _ hd]
    simp only [localPiolaFlux,ite_eq_left (X.map_source hx),X.left_inv hx]
    change (|(fderiv ℝ X x).det|⁻¹ •
      (operatorMatrix (fderiv ℝ X x)*(B x*gradientColumns (fderiv ℝ u x)))).col j=_
    change |(fderiv ℝ X x).det|⁻¹ •
      ((operatorMatrix (fderiv ℝ X x)*(B x*gradientColumns (fderiv ℝ u x))).col j)=_
    congr 1
    exact (operatorMatrix_mulVec (fderiv ℝ X x) ((B x*gradientColumns (fderiv ℝ u x)).col j))
  · simp only [localPiolaTensor,localPiolaFlux,ite_eq_right hy,Matrix.zero_mul]
    rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_LocalTensorBounds
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

lemma matrix_three_product_norm_bound (A B : Mat3) : ‖A*B‖≤3*‖A‖*‖B‖ := by
  apply Matrix.norm_le_iff (by positivity) |>.mpr
  intro i j
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k : Fin 3,‖A i k*B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 3,‖A‖*‖B‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
        (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AnalyticNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter MeasureTheory Topology

def AnalyticNullProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∀ (U : Set E) (f : E → ℝ), IsOpen U → IsPreconnected U → AnalyticOnNhd ℝ f U →
    (∃ x ∈ U, f x ≠ 0) → μ (U ∩ f ⁻¹' {0}) = 0

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_LocalPiola
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def localPiolaSource (X : OpenPartialHomeomorph E E) (r : E → ℝ) (y : E) : ℝ := by
  classical
  exact if y∈X.target then |(fderiv ℝ X (X.symm y)).det|⁻¹*r (X.symm y) else 0

lemma localPiolaSource_pairing (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hdet : ∀ x∈X.source,(fderiv ℝ X x).det≠0)
    (r : E → ℝ) (hs : Function.support r⊆X.source) (φ : E → ℝ) :
    (∫ y,φ y*localPiolaSource X r y ∂μ)=(∫ x,φ (X x)*r x ∂μ) := by
  rw [integral_eq_setIntegral_of_zero_off μ X.target _ (by
    intro y hy; simp [localPiolaSource,hy])]
  rw [←X.image_source_eq_target,integral_image_eq_integral_abs_det_fderiv_smul μ
    X.open_source.measurableSet
    (fun x hx => ((hX x hx).differentiableAt (X.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt)
    X.injOn]
  rw [integral_eq_setIntegral_of_zero_off μ X.source (fun x => φ (X x)*r x) (by
    intro x hx
    rw [Function.notMem_support.mp (notMem_subset hs hx),mul_zero])]
  apply setIntegral_congr_fun X.open_source.measurableSet
  intro x hx
  simp only [localPiolaSource,ite_eq_left (X.map_source hx),X.left_inv hx,smul_eq_mul]
  have hn := abs_ne_zero.mpr (hdet x hx)
  field_simp

omit [BorelSpace E] in
lemma compactFlux_local_source (μ : Measure E) {U : Set E} (hU : IsOpen U)
    (F : E → E) (r : E → ℝ) (hcF : HasCompactSupport F) (hcr : HasCompactSupport r)
    (hsF : tsupport F⊆U) (hsr : tsupport r⊆U)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      (∫ x,fderiv ℝ φ x (F x) ∂μ)=-(∫ x,φ x*r x ∂μ))
    (ψ : E → ℝ) (hψ : ContDiffOn ℝ (↑(⊤ : ℕ∞)) ψ U) :
    (∫ x,fderiv ℝ ψ x (F x) ∂μ)=-(∫ x,ψ x*r x ∂μ) := by
  obtain ⟨g,hg,he⟩ := exists_smooth_extension_near_compact hU (hcF.union hcr)
    (union_subset hsF hsr) ψ hψ
  calc
    _ = ∫ x,fderiv ℝ g x (F x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈tsupport F
      · rw [(he x (mem_union_left _ hx)).fderiv_eq]
      · rw [image_eq_zero_of_notMem_tsupport hx,map_zero,map_zero]
    _ = -(∫ x,g x*r x ∂μ) := hweak g hg
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈tsupport r
      · rw [(he x (mem_union_right _ hx)).eq_of_nhds]
      · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,mul_zero]

theorem localPiolaFlux_weak_source (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (F : E → E) (r : E → ℝ) (hcF : HasCompactSupport F) (hcr : HasCompactSupport r)
    (hsF : tsupport F⊆X.source) (hsr : tsupport r⊆X.source)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      (∫ x,fderiv ℝ φ x (F x) ∂μ)=-(∫ x,φ x*r x ∂μ))
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    (∫ y,fderiv ℝ ψ y (localPiolaFlux X F y) ∂μ)=
      -(∫ y,ψ y*localPiolaSource X r y ∂μ) := by
  have hd := hX.differentiableOn (by simp)
  have hdi := hXi.differentiableOn (by simp)
  have hdet : ∀ x∈X.source,(fderiv ℝ X x).det≠0 :=
    fun _ hx => local_fderiv_det_ne_zero X hd hdi hx
  rw [localPiolaFlux_pairing μ X hd hdet F (subset_closure.trans hsF) ψ (hψ.differentiable (by simp)),
    localPiolaSource_pairing μ X hd hdet r (subset_closure.trans hsr) ψ]
  exact compactFlux_local_source μ X.open_source F r hcF hcr hsF hsr hweak _
    (hψ.comp_contDiffOn hX)

end ScalarConductivity



namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma tensorColumn_tsupport (B : Coord3 → Mat3) (D : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) (j : Fin 2) :
    tsupport (fun x => (B x*D x).col j)⊆tsupport B := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply subset_closure
  intro hz
  apply hx
  simp only [hz,Matrix.zero_mul]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalBoxCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

def coordinatePairCLM : Coord3 →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (j.castLE (by decide : 2≤3)))

def coordinatePair : Coord3 → Fin 2 → ℝ := coordinatePairCLM

@[simp] lemma coordinatePair_zero (x : Coord3) : coordinatePair x 0=x 0 := rfl
@[simp] lemma coordinatePair_one (x : Coord3) : coordinatePair x 1=x 1 := rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_LocalRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma localPiolaSource_support (X : OpenPartialHomeomorph E E) (r : E → ℝ) :
    Function.support (localPiolaSource X r)⊆X '' (Function.support r∩X.source) := by
  intro y hy
  by_cases hyt : y∈X.target
  · refine ⟨X.symm y,⟨?_,X.map_target hyt⟩,X.right_inv hyt⟩
    intro hz
    exact hy (by simp [localPiolaSource,hyt,hz])
  · exact False.elim (hy (by simp [localPiolaSource,hyt]))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma localPiolaSource_compact (X : OpenPartialHomeomorph E E)
    (r : E → ℝ) (hc : HasCompactSupport r) (hs : tsupport r⊆X.source) :
    HasCompactSupport (localPiolaSource X r) ∧ tsupport (localPiolaSource X r)⊆X.target := by
  have hci : IsCompact (X '' tsupport r) := hc.image_of_continuousOn (X.continuousOn.mono hs)
  have ht : tsupport (localPiolaSource X r)⊆X '' tsupport r :=
    closure_minimal ((localPiolaSource_support X r).trans
      (image_mono (fun _ hx => subset_closure hx.1))) hci.isClosed
  exact ⟨hci.of_isClosed_subset isClosed_closure ht,ht.trans (by
    rintro y ⟨x,hx,rfl⟩; exact X.map_source (hs hx))⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma localPiolaSource_smooth (X : OpenPartialHomeomorph E E)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (r : E → ℝ) (hr : ContDiff ℝ (↑(⊤ : ℕ∞)) r)
    (hc : HasCompactSupport r) (hs : tsupport r⊆X.source) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (localPiolaSource X r) := by
  apply contDiff_of_contDiffOn_tsupport X.open_target _ (localPiolaSource_compact X r hc hs).2
  apply X.open_target.contDiffOn_iff.mpr
  intro y hy
  have hxi := hXi.contDiffAt (X.open_target.mem_nhds hy)
  have hx := hX.contDiffAt (X.open_source.mem_nhds (X.map_target hy))
  have hd : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun z => fderiv ℝ X (X.symm z)) y :=
    (hx.fderiv_right (by simp)).comp y hxi
  have hd0 := local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
    (hXi.differentiableOn (by simp)) (X.map_target hy)
  have hdet := ((contDiff_clm_det (E:=E) (↑(⊤ : ℕ∞))).contDiffAt.comp y hd).abs hd0
  have hformula := (hdet.inv (abs_ne_zero.mpr hd0)).mul (hr.contDiffAt.comp y hxi)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [X.open_target.mem_nhds hy] with z hz
  simp only [localPiolaSource,ite_eq_left hz]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_SymmetricCutoffSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def symmetricSource (H : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) : Coord3 → ℝ :=
  coordinateDivergence (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j)

lemma symmetricFlux_smooth {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤ : ℕ∞)) H) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (j : Fin 2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j) := by
  have hm : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => H x*gradientColumns (fderiv ℝ u x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact contDiffAt_matrix_mul hH.contDiffAt (contDiff_gradientColumns u hu).contDiffAt
  apply contDiff_pi.mpr
  intro i
  exact contDiff_pi.mp (contDiff_pi.mp hm i) j

lemma symmetricFlux_compact {H : Coord3 → Mat3} (hH : HasCompactSupport H)
    (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) :
    HasCompactSupport (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j) :=
  hH.of_isClosed_subset isClosed_closure (tensorColumn_tsupport H _ j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactPhysicalCorrections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

abbrev PhysicalSourcePair := Fin 2 → Coord3 → ℝ

def CompactSmoothPair (r : PhysicalSourcePair) : Prop :=
  ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j) ∧ HasCompactSupport (r j)

def PairSupported (r : PhysicalSourcePair) (U : Set Coord3) : Prop :=
  ∀ j,tsupport (r j)⊆U

lemma symmetricSource_eq_of_weak
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {H : Coord3 → Mat3} (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hc : HasCompactSupport H)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r)
    (hw : ∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤:ℕ∞)) ψ →
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=-(∫ x,ψ x*r j x)) :
    ∀ j,symmetricSource H u j=r j := by
  intro j
  have hs := coordinateDivergence_smooth (symmetricFlux_smooth hH hu j)
  apply Measure.eq_of_ae_eq (μ := volume) _ hs.continuous (hr j).1.continuous
  apply ae_eq_of_integral_contDiff_smul_eq hs.continuous.locallyIntegrable
    (hr j).1.continuous.locallyIntegrable
  intro ψ hψ _
  have he := coordinateDivergence_weak (symmetricFlux_smooth hH hu j)
    (symmetricFlux_compact hc u j) ψ hψ
  have he' := hw j ψ hψ
  simp only [smul_eq_mul]
  change (∫ x,ψ x*coordinateDivergence (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j) x)=_
  linarith

lemma coordinateDivergence_add {F G : Coord3 → Coord3}
    (hF : ContDiff ℝ (↑(⊤:ℕ∞)) F) (hG : ContDiff ℝ (↑(⊤:ℕ∞)) G) :
    coordinateDivergence (F+G)=coordinateDivergence F+coordinateDivergence G := by
  funext x
  simp only [coordinateDivergence,Pi.add_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he := (((contDiff_pi.mp hF i).differentiable (by simp) x).hasFDerivAt.add
    ((contDiff_pi.mp hG i).differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun D : Coord3 →L[ℝ] ℝ => D (Pi.single i 1)) he

lemma symmetricSource_add {H K : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hK : ContDiff ℝ (↑(⊤:ℕ∞)) K)
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (j : Fin 2) :
    symmetricSource (H+K) u j=symmetricSource H u j+symmetricSource K u j := by
  have he : (fun x => ((H+K) x*gradientColumns (fderiv ℝ u x)).col j)=
      (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j)+
        (fun x => (K x*gradientColumns (fderiv ℝ u x)).col j) := by
    funext x i
    simp [Matrix.add_mul]
  unfold symmetricSource
  rw [he,coordinateDivergence_add (symmetricFlux_smooth hH hu j) (symmetricFlux_smooth hK hu j)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularPeriodization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

def angularShift (T : ℝ) (n : Fin 2 → ℤ) : Coord3 := ![0,T*(n 0:ℝ),T*(n 1:ℝ)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def AngularPeriodic (T : ℝ) (f : Coord3 → E) : Prop :=
  ∀ n x,f (x+angularShift T n)=f x

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_ControlledCorrectionBoxes
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

def BoundedPhysicallyCorrectable (u : Coord3 → Fin 2 → ℝ) (U : Set Coord3)
    (r : PhysicalSourcePair) (N : ℝ) : Prop :=
  ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ HasCompactSupport H ∧
    tsupport H⊆U ∧ (∀ x,(H x).IsSymm) ∧ (∀ j,symmetricSource H u j=r j) ∧
    ∀ x,‖H x‖≤N

namespace BoundedPhysicallyCorrectable
variable {u : Coord3 → Fin 2 → ℝ} {U : Set Coord3} {r s : PhysicalSourcePair} {M N : ℝ}
lemma mono (h : BoundedPhysicallyCorrectable u U r M) (hMN : M≤N) :
    BoundedPhysicallyCorrectable u U r N := by
  obtain ⟨H,hH,hc,hs,hsy,hr,hb⟩ := h
  exact ⟨H,hH,hc,hs,hsy,hr,fun x => (hb x).trans hMN⟩
lemma zero (hN : 0≤N) : BoundedPhysicallyCorrectable u U 0 N := by
  refine ⟨0,contDiff_const,HasCompactSupport.zero,by simp [tsupport_zero],fun _ => Matrix.isSymm_zero,?_,?_⟩
  · intro j; funext x; simp [symmetricSource,coordinateDivergence,Matrix.col]
  · intro x; simpa using hN
lemma add (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hr : BoundedPhysicallyCorrectable u U r M) (hs : BoundedPhysicallyCorrectable u U s N) :
    BoundedPhysicallyCorrectable u U (r+s) (M+N) := by
  obtain ⟨H,hH,hHc,hHs,hHsy,hHr,hHb⟩ := hr
  obtain ⟨K,hK,hKc,hKs,hKsy,hKr,hKb⟩ := hs
  refine ⟨H+K,hH.add hK,hHc.add hKc,(tsupport_add H K).trans (union_subset hHs hKs),
    fun x => (hHsy x).add (hKsy x),?_,fun x => (norm_add_le _ _).trans (add_le_add (hHb x) (hKb x))⟩
  intro j
  rw [symmetricSource_add hH hK hu j,hHr j,hKr j]
  rfl
end BoundedPhysicallyCorrectable

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MetricControlledPiola
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

lemma localPiolaTensor_bound_of_coefficient
    (X : OpenPartialHomeomorph Coord3 Coord3) {K : Set Coord3} {C : ℝ} (hC : 0≤C)
    (hc : ∀ x∈K,9*|(fderiv ℝ X x).det|⁻¹*‖operatorMatrix (fderiv ℝ X x)‖*
      ‖operatorMatrix (fderiv ℝ X x)‖≤C)
    (B : Coord3 → Mat3) (hB : Function.support B⊆K) (y : Coord3) :
    ‖localPiolaTensor X B y‖≤C*‖B (X.symm y)‖ := by
  let A := fun x => operatorMatrix (fderiv ℝ X x)
  by_cases hy : y∈X.target
  · by_cases hxy : X.symm y∈K
    · simp only [localPiolaTensor,ite_eq_left hy,norm_smul,Real.norm_eq_abs,abs_inv,abs_abs]
      calc
        _ ≤ |(fderiv ℝ X (X.symm y)).det|⁻¹ * (3*‖A (X.symm y)*B (X.symm y)‖*‖(A (X.symm y))ᵀ‖) :=
          mul_le_mul_of_nonneg_left (matrix_three_product_norm_bound _ _) (inv_nonneg.mpr (abs_nonneg _))
        _ ≤ |(fderiv ℝ X (X.symm y)).det|⁻¹ * (3*(3*‖A (X.symm y)‖*‖B (X.symm y)‖)*‖A (X.symm y)‖) := by
          rw [Matrix.norm_transpose]
          gcongr
          exact matrix_three_product_norm_bound _ _
        _ = (9*|(fderiv ℝ X (X.symm y)).det|⁻¹*‖A (X.symm y)‖*‖A (X.symm y)‖)*‖B (X.symm y)‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hc _ hxy) (norm_nonneg _)
    · have hz : B (X.symm y)=0 := by
        by_contra hn
        exact hxy (hB hn)
      simp [localPiolaTensor,hy,hz]
  · simp only [localPiolaTensor,ite_eq_right hy,norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricLocalRegularCorrection
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

lemma BoundedPhysicallyCorrectable.region_mono
    {u : Coord3 → Fin 2 → ℝ} {U V : Set Coord3} {r : PhysicalSourcePair} {N : ℝ}
    (h : BoundedPhysicallyCorrectable u U r N) (hUV : U⊆V) :
    BoundedPhysicallyCorrectable u V r N := by
  obtain ⟨H,hH,hc,hs,hsy,hr,hb⟩ := h
  exact ⟨H,hH,hc,hs.trans hUV,hsy,hr,hb⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_QuantitativeGlobalCorrection
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

lemma BoundedPhysicallyCorrectable.sum {ι : Type*} (s : Finset ι)
    (r : ι → PhysicalSourcePair) (N : ι → ℝ)
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {U : Set Coord3} (hr : ∀ i∈s,BoundedPhysicallyCorrectable u U (r i) (N i)) :
    BoundedPhysicallyCorrectable u U (∑ i∈s,r i) (∑ i∈s,N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BoundedPhysicallyCorrectable.zero (u := u) (U := U) (le_refl 0)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (hr a (Finset.mem_insert_self a s)).add hu (ih fun i hi => hr i (Finset.mem_insert_of_mem hi))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalBoundedPiolaCorrection
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

theorem BoundedPhysicallyCorrectable.piola_local
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤:ℕ∞)) X.symm X.target)
    {u v : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    {U : Set Coord3} (hUo : IsOpen U) (hU : U⊆X.source)
    (hpot : EqOn u (v∘X.symm) (X '' U)) {C N : ℝ} (hC : 0≤C)
    (hbound : ∀ x∈U,9*|(fderiv ℝ X x).det|⁻¹*‖operatorMatrix (fderiv ℝ X x)‖*
      ‖operatorMatrix (fderiv ℝ X x)‖≤C)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : PairSupported r U)
    (hc : BoundedPhysicallyCorrectable v U r N) :
    BoundedPhysicallyCorrectable u (X '' U) (fun j => localPiolaSource X (r j)) (C*N) := by
  obtain ⟨B,hB,hBc,hBs,hsy,hsrc,hBb⟩ := hc
  have hBs' := hBs.trans hU
  have hsr (j) := (hs j).trans hU
  have hweak (j) (φ : Coord3 → ℝ) (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
      (∫ x,fderiv ℝ φ x ((B x*gradientColumns (fderiv ℝ v x)).col j))=-(∫ x,φ x*r j x) := by
    have h := coordinateDivergence_weak (symmetricFlux_smooth hB hv j) (symmetricFlux_compact hBc v j) φ hφ
    change (∫ x,fderiv ℝ φ x ((B x*gradientColumns (fderiv ℝ v x)).col j))=
      -(∫ x,φ x*symmetricSource B v j x) at h
    simpa only [hsrc] using h
  let H := localPiolaTensor X B
  have hH := localPiolaTensor_smooth X hX hXi B hB hBc hBs'
  have hHc := (localPiolaTensor_compact X B hBc hBs').1
  have hHs : tsupport (localPiolaTensor X B)⊆X '' U := by
    have hh : tsupport (localPiolaTensor X B)⊆X '' tsupport B :=
      closure_minimal ((localPiolaTensor_support X B).trans
        (image_mono (fun _ hx => subset_closure hx.1)))
        (hBc.image_of_continuousOn (X.continuousOn.mono hBs')).isClosed
    exact hh.trans (image_mono hBs)
  have hIo : IsOpen (X '' U) := X.isOpen_image_of_subset_source hUo hU
  have hpr : CompactSmoothPair (fun j => localPiolaSource X (r j)) := fun j =>
    ⟨localPiolaSource_smooth X hX hXi (r j) (hr j).1 (hr j).2 (hsr j),
      (localPiolaSource_compact X (r j) (hr j).2 (hsr j)).1⟩
  refine ⟨H,hH,hHc,hHs,localPiolaTensor_isSymm X B hsy,?_,?_⟩
  · apply symmetricSource_eq_of_weak hu hH hHc hpr
    intro j ψ hψ
    have he : (∫ y,fderiv ℝ ψ y ((H y*gradientColumns (fderiv ℝ (v∘X.symm) y)).col j))=
        -(∫ y,ψ y*localPiolaSource X (r j) y) := by
      simp_rw [H,localPiolaTensor_columns X (hX.differentiableOn (by simp))
        (hXi.differentiableOn (by simp)) B v (hv.differentiable (by simp)).differentiableOn]
      have ht := tensorColumn_tsupport B (fun x => gradientColumns (fderiv ℝ v x)) j
      exact localPiolaFlux_weak_source volume X hX hXi _ _
        (hBc.of_isClosed_subset isClosed_closure ht) (hr j).2 (ht.trans hBs') (hsr j) (hweak j) ψ hψ
    refine (integral_congr_ae ?_).trans he
    filter_upwards [] with y
    by_cases hy : y∈X '' U
    · have hf : u =ᶠ[𝓝 y] v∘X.symm :=
        Filter.eventuallyEq_of_mem (hIo.mem_nhds hy) (fun z hz => hpot hz)
      rw [hf.fderiv_eq]
    · have hzero : H y=0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hHs h))
      change (fderiv ℝ ψ y) ((H y*gradientColumns (fderiv ℝ u y)).col j)=_
      simp only [hzero,Matrix.zero_mul]
  · intro y
    exact (localPiolaTensor_bound_of_coefficient X hC hbound B ((subset_tsupport _).trans hBs) y).trans
      (mul_le_mul_of_nonneg_left (hBb _) hC)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_LeadingFrequencyAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def angularNormalization (A : Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  (A 0 0:ℝ)^2+(A 0 1:ℝ)^2+(A 1 0:ℝ)^2+(A 1 1:ℝ)^2+1

lemma angularNormalization_pos (A : Matrix (Fin 2) (Fin 2) ℤ) :
    0<angularNormalization A := by unfold angularNormalization; positivity

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularFourierConjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def angularNormalizedLift (A : Matrix (Fin 2) (Fin 2) ℤ) (x : Coord3) : Coord3 :=
  ![Real.sqrt (angularNormalization A)*x 0,
    (A 0 0:ℝ)*x 1+(A 0 1:ℝ)*x 2,(A 1 0:ℝ)*x 1+(A 1 1:ℝ)*x 2]

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_ApproxScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal
noncomputable section
open Matrix Filter Topology
namespace ScalarConductivity
open Filter Topology Set TopologicalSpace

def ApproxScalar {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure X) (a b ε : ℝ) (Z : Lp V 2 μ × Lp V 2 μ) : Prop :=
  ∃ s : X → ℝ, Measurable s ∧
    (∀ᵐ x ∂μ, s x ∈ Icc a b) ∧
    μ {x | ε ≤ ‖Z.2 x - s x • Z.1 x‖} ≤ ENNReal.ofReal ε

end ScalarConductivity

end
end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_GeneralModeFiniteEndNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def angularInverseLift (A : Matrix (Fin 2) (Fin 2) ℤ) (x : Coord3) : Coord3 :=
  ![x 0/Real.sqrt (angularNormalization A),
    (A 1 1:ℝ)*x 1-(A 0 1:ℝ)*x 2,-(A 1 0:ℝ)*x 1+(A 0 0:ℝ)*x 2]

def angularNormalizedLinear (A : Matrix (Fin 2) (Fin 2) ℤ) : Coord3 →ₗ[ℝ] Coord3 where
  toFun := angularNormalizedLift A
  map_add' x y := by ext i; fin_cases i <;> simp [angularNormalizedLift] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [angularNormalizedLift] <;> ring

def angularInverseLinear (A : Matrix (Fin 2) (Fin 2) ℤ) : Coord3 →ₗ[ℝ] Coord3 where
  toFun := angularInverseLift A
  map_add' x y := by ext i; fin_cases i <;> simp [angularInverseLift] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [angularInverseLift] <;> ring

lemma real_angular_det_one {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) :
    (A 0 0:ℝ)*(A 1 1:ℝ)-(A 0 1:ℝ)*(A 1 0:ℝ)=1 := by
  have h : A 0 0*A 1 1-A 0 1*A 1 0=1 := by simpa only [Matrix.det_fin_two] using hA
  exact_mod_cast h

lemma angularNormalizedLift_inverse {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (x : Coord3) :
    angularNormalizedLift A (angularInverseLift A x)=x := by
  have hd := real_angular_det_one hA
  have hm : Real.sqrt (angularNormalization A)≠0 := (Real.sqrt_pos.mpr (angularNormalization_pos A)).ne'
  ext i
  fin_cases i
  · change Real.sqrt (angularNormalization A) * (x 0 / Real.sqrt (angularNormalization A)) = x 0
    field_simp [hm]
  · change (A 0 0:ℝ)*((A 1 1:ℝ)*x 1-(A 0 1:ℝ)*x 2)+
      (A 0 1:ℝ)*(-(A 1 0:ℝ)*x 1+(A 0 0:ℝ)*x 2)=x 1
    nlinarith [congrArg (fun z : ℝ => z*x 1) hd]
  · change (A 1 0:ℝ)*((A 1 1:ℝ)*x 1-(A 0 1:ℝ)*x 2)+
      (A 1 1:ℝ)*(-(A 1 0:ℝ)*x 1+(A 0 0:ℝ)*x 2)=x 2
    nlinarith [congrArg (fun z : ℝ => z*x 2) hd]

lemma angularInverseLift_normalized {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (x : Coord3) :
    angularInverseLift A (angularNormalizedLift A x)=x := by
  have hd := real_angular_det_one hA
  have hm : Real.sqrt (angularNormalization A)≠0 := (Real.sqrt_pos.mpr (angularNormalization_pos A)).ne'
  ext i
  fin_cases i
  · simp [angularNormalizedLift,angularInverseLift,hm]
  · change (A 1 1:ℝ)*((A 0 0:ℝ)*x 1+(A 0 1:ℝ)*x 2)-
      (A 0 1:ℝ)*((A 1 0:ℝ)*x 1+(A 1 1:ℝ)*x 2)=x 1
    nlinarith [congrArg (fun z : ℝ => z*x 1) hd]
  · change -(A 1 0:ℝ)*((A 0 0:ℝ)*x 1+(A 0 1:ℝ)*x 2)+
      (A 0 0:ℝ)*((A 1 0:ℝ)*x 1+(A 1 1:ℝ)*x 2)=x 2
    nlinarith [congrArg (fun z : ℝ => z*x 2) hd]

def angularNormalizedEquiv (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) : Coord3 ≃L[ℝ] Coord3 :=
  (LinearEquiv.ofLinearMap (angularNormalizedLinear A) (angularInverseLinear A)
    (by apply LinearMap.ext; intro x; exact angularNormalizedLift_inverse hA x)
    (by apply LinearMap.ext; intro x; exact angularInverseLift_normalized hA x)).toContinuousLinearEquiv

@[simp] lemma angularNormalizedEquiv_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) (x : Coord3) :
    angularNormalizedEquiv A hA x=angularNormalizedLift A x := rfl

@[simp] lemma angularNormalizedEquiv_symm_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) (x : Coord3) :
    (angularNormalizedEquiv A hA).symm x=angularInverseLift A x := rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_UndoAngularWeakPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

namespace WeakFiniteTensorPair

def onEq {U V : Set Coord3} (w : WeakFiniteTensorPair U) (h : U=V) :
    WeakFiniteTensorPair V where
  v := w.v
  E := w.E
  symm := w.symm
  smooth := w.smooth
  measurable := w.measurable
  elliptic := w.elliptic
  regular := by simpa only [←h] using w.regular
  G := w.G
  flux_C1 := w.flux_C1
  constitution := w.constitution
  weak j ψ hc hs := w.weak j ψ hc (by simpa only [h] using hs)

end WeakFiniteTensorPair
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPairRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def centralBasisSlopes (j : Fin 2) : Fin 3 → ℝ :=
  ![![-1,1,0],![-1,0,1]] j

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WordGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

abbrev SourceWord := List (Fin 2)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FiniteEndPhysicalDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma AngularPeriodic.eq_of_angles {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) {x y : Coord3}
    (ht : x 0=y 0) (ha : torusAngles x=torusAngles y) : f x=f y := by
  have he (i : Fin 2) : ∃ n : ℤ, x i.succ=y i.succ+(2*Real.pi)*(n:ℝ) := by
    have hi := congrFun ha i
    have heq : ((x i.succ/(2*Real.pi):ℝ) : UnitAddCircle)=
        ((y i.succ/(2*Real.pi):ℝ) : UnitAddCircle) := by
      fin_cases i <;> exact hi
    have hz : (((x i.succ/(2*Real.pi)-y i.succ/(2*Real.pi)):ℝ) : UnitAddCircle)=0 := by
      simpa only [AddCircle.coe_sub,sub_eq_zero] using heq
    obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp hz
    refine ⟨n,?_⟩
    simp only [zsmul_eq_mul,mul_one] at hn
    have hπ : 2*Real.pi≠0 := by positivity
    field_simp at hn
    nlinarith
  choose n hn using he
  have hxy : x=y+angularShift (2*Real.pi) n := by
    ext i
    fin_cases i
    · simpa [angularShift] using ht
    · simpa [angularShift] using hn 0
    · simpa [angularShift] using hn 1
  rw [hxy]
  exact hp n y

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalSmoothTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

def piSmoothH1 {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) : H1 :=
  smoothH1 (φ ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)))
    (hφ.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)

lemma piSmoothH1_jet {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (piSmoothH1 hφ).val=ᵐ[ballMeasure] (fun x => piSmoothJet φ (WithLp.ofLp x)) := by
  filter_upwards [(smoothJet_memLp
    (hφ.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)).coeFn_toLp]
    with x hx
  change (piSmoothH1 hφ).val x=_ at hx
  rw [hx]
  ext i
  refine Fin.cases rfl (fun j => ?_) i
  change gradient (φ ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))) x j=
    fderiv ℝ φ (WithLp.ofLp x) (Pi.single j 1)
  rw [gradient_apply_single,fderiv_comp x (hφ.differentiable (by simp) _)
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).differentiableAt]
  rw [ContinuousLinearEquiv.fderiv]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

def physicalRestrictedJetCLM (D : Set (Fin 3 → ℝ)) :
    H1 →L[ℝ] Lp JetFiber 2 (volume.restrict D) :=
  ((lpRestrictionCLM D).comp ballWholePiJetCLM).comp H1Space.subtypeL

lemma physicalRestrictedJet_smooth_ae {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) {D : Set (Fin 3 → ℝ)}
    (hD : MeasurableSet D) (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    physicalRestrictedJetCLM D (piSmoothH1 hφ)=ᵐ[volume.restrict D] piSmoothJet φ := by
  filter_upwards [lpRestrictionCLM_ae D (ballWholePiJetCLM (piSmoothH1 hφ).val),
    ae_restrict_of_ae (ballWholePiJetCLM_ae_of_ae (piSmoothH1 hφ).val _ (piSmoothH1_jet hφ)),
    ae_restrict_mem hD] with y hr he hy
  exact hr.trans (he.trans (ite_eq_left (hb y hy)))

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

theorem dense_linear_observable_extension
    {E H V : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (J : E →ₗ[ℝ] H) (T : E →ₗ[ℝ] V) (hJ : DenseRange J)
    (hB : ∃ C : ℝ, ∀ f, ‖T f‖ ≤ C*‖J f‖) :
    ∃ L : H →L[ℝ] V, ∀ f, L (J f)=T f := by
  obtain ⟨C,hC⟩ := hB
  have hk : J.ker ≤ T.ker := by
    intro f hf
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [LinearMap.mem_ker.mp hf,norm_zero,mul_zero] using hC f
  let Q : J.range →ₗ[ℝ] V := (J.ker.liftQ T hk).comp J.quotKerEquivRange.symm.toLinearMap
  have hQ (f : E) : Q (J.rangeRestrict f)=T f := by
    have hh : J.quotKerEquivRange (Submodule.Quotient.mk f)=J.rangeRestrict f := rfl
    rw [←hh]
    change (J.ker.liftQ T hk) (J.quotKerEquivRange.symm
      (J.quotKerEquivRange (Submodule.Quotient.mk f)))=_
    rw [LinearEquiv.symm_apply_apply,Submodule.liftQ_apply]
  have hQB (x : J.range) : ‖Q x‖≤C*‖x‖ := by
    obtain ⟨f,hf⟩ := x.property
    have hx : x=J.rangeRestrict f := Subtype.ext hf.symm
    rw [hx,hQ]
    exact hC f
  let Qc := Q.mkContinuous C hQB
  have hd : DenseRange J.range.subtypeL := by
    intro x
    apply closure_mono (s := Set.range J) ?_ (hJ x)
    rintro _ ⟨f,rfl⟩
    exact ⟨J.rangeRestrict f,rfl⟩
  refine ⟨Qc.extend J.range.subtypeL,fun f => ?_⟩
  have hi : Isometry J.range.subtypeL := fun _ _ => rfl
  exact (Qc.extend_eq hd hi.isUniformInducing (J.rangeRestrict f)).trans (hQ f)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def physicalOuterBoundary (i : Fin 3) (θ : UnitAddTorus (Fin 2)) : Fin 3 → ℝ :=
  Fin.cases (sourceAngularCollar 0 θ)
    (fun k => sourceChildCoordinates (actualChildSign k) (sourceAngularCollar 0 θ)) i

lemma physicalOuterBoundary_continuous (i : Fin 3) : Continuous (physicalOuterBoundary i) := by
  refine Fin.cases (continuous_sourceAngularCollar 0) (fun k => ?_) i
  exact (sourceChildCoordinates_contDiff _).continuous.comp (continuous_sourceAngularCollar 0)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOuterTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance instMeasureSpaceUnitAddCircle_solutions_9 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_9 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def smoothOuterContinuousL (i : Fin 3) :
    SmoothScalar (Fin 3 → ℝ) →ₗ[ℝ] C(UnitAddTorus (Fin 2),ℂ) where
  toFun φ := ⟨fun θ => (φ.val (physicalOuterBoundary i θ):ℂ),
    Complex.continuous_ofReal.comp ((smoothScalar_contDiff φ).continuous.comp (physicalOuterBoundary_continuous i))⟩
  map_add' f g := by ext θ; simp
  map_smul' c f := by ext θ; simp

def smoothOuterFourierL (i : Fin 3) :
    SmoothScalar (Fin 3 → ℝ) →ₗ[ℝ] SpectralL2 TorusModes :=
  ((mFourierBasis (d:=Fin 2)).repr.toLinearEquiv.toLinearMap.restrictScalars ℝ).comp
    ((ContinuousMap.toLp 2 volume ℝ).toLinearMap.comp (smoothOuterContinuousL i))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RankProjectionFirst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

namespace WeakFiniteTensorPair

def output {U : Set Coord3} (w : WeakFiniteTensorPair U)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (b : Fin 2 → ℝ) : WeakFiniteTensorPair U :=
  ((w.linear (ContinuousLinearEquiv.refl ℝ Coord3) Q).translate 0 b).onEq (by ext x; simp)

@[simp] lemma output_v {U : Set Coord3} (w : WeakFiniteTensorPair U)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (b : Fin 2 → ℝ) (x : Coord3) :
    (w.output Q b).v x=Q (w.v x)+b := by
  change Q (w.v (x-0))+b=_
  rw [sub_zero]

end WeakFiniteTensorPair

end ScalarConductivity

end

end OAI
end


