-- Prove2me | Definitions.Def_Q227CKS000
-- name    : Q227CKS000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:45:28.933791+00:00
-- url     : https://prove2.me/theorems/89e6a3de-b409-4d0e-a09b-9847d2c3191d
-- title:
--   Definitions bundle Q227CKS000 of the split of OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CKSMain.schwarzschild_equality_examples`, carved from OpenAI's openai/math development (OpenAI, *Area-controlled end replacement and the Bondi Penrose inequality in the CKS class*, OpenAI Math Release, September 27, 2026, result family 260, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 359 declarations of OpenAI's Lean: 114 definitions, 5 inductive types or structures, 4 instances and 236 theorems. The definitions and types are `OAI.CKSAmbientCalculus.A`, `OAI.CKSAmbientCalculus.P`, `OAI.CKSAmbientCalculus.Symbols`, `OAI.CKSAmbientCalculus.Vect`, `OAI.CKSAmbientCalculus.bracket`, `OAI.CKSAmbientCalculus.coordCurvature`, `OAI.CKSAmbientCalculus.curvature`, `OAI.CKSAmbientCalculus.delta`, `OAI.CKSAmbientCalculus.nabla`, `OAI.CKSAmbientCalculus.pair`, `OAI.CKSAngularGeometry.ActualAdaptedAt`, `OAI.CKSAngularGeometry.ContinuousMetricJetAt`, `OAI.CKSAngularGeometry.ContinuousTensorJetAt`, `OAI.CKSAngularGeometry.FrameChartAt`, `OAI.CKSAngularGeometry.LocalFrame`, `OAI.CKSAngularGeometry.Mat`, `OAI.CKSAngularGeometry.SmoothOrthonormalAt`, `OAI.CKSAngularGeometry.actualFrameBracket`, `OAI.CKSAngularGeometry.actualFrameCurvature`, `OAI.CKSAngularGeometry.actualFrameEnergy`, `OAI.CKSAngularGeometry.actualFrameMomentum`, `OAI.CKSAngularGeometry.actualFrameScalar`, `OAI.CKSAngularGeometry.actualFrameTensorCovariant`, `OAI.CKSAngularGeometry.actualMetricFirstJet`, `OAI.CKSAngularGeometry.adaptedFrame`, `OAI.CKSAngularGeometry.coordinateChristoffel`, `OAI.CKSAngularGeometry.coordinateConnectionVector`, `OAI.CKSAngularGeometry.coordinateMomentum`, `OAI.CKSAngularGeometry.coordinateMomentumLinear`, `OAI.CKSAngularGeometry.coordinatePullback`, `OAI.CKSAngularGeometry.coordinatePullbackFrame`, `OAI.CKSAngularGeometry.coordinateTensorCovariant`, `OAI.CKSAngularGeometry.coordinateTensorCovariantLast`, `OAI.CKSAngularGeometry.covariantDirectionLinear`, `OAI.CKSAngularGeometry.covariantVector`, `OAI.CKSAngularGeometry.curvatureVector`, `OAI.CKSAngularGeometry.foliationMetric`, `OAI.CKSAngularGeometry.foliationNormal`, `OAI.CKSAngularGeometry.frameBracketCoefficient`, `OAI.CKSAngularGeometry.frameCoefficient` and 79 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Relativity_CKS_AdaptedKoszul`, `Relativity_CKS_AngularGeometry`, `Relativity_CKS_AngularSlice`, `Relativity_CKS_BondiBalance`, `Relativity_CKS_BoostTransport`, `Relativity_CKS_BoundaryBridge`, `Relativity_CKS_BoundaryCharts`, `Relativity_CKS_BoundaryFinite`, `Relativity_CKS_BoundaryPartial`, `Relativity_CKS_BoundarySmooth`, `Relativity_CKS_CKSMetricPositivity`, `Relativity_CKS_ConstructedOuterMetric`, `Relativity_CKS_CoordinateLeviCivita`, `Relativity_CKS_CutSurface`, `Relativity_CKS_FoliationKoszul`, `Relativity_CKS_FoliationOrthonormalFrame`, `Relativity_CKS_FoliationPhysicalLeaf`, `Relativity_CKS_FoliationReconstruction`, `Relativity_CKS_HeatBase`, `Relativity_CKS_InducedMetric`, `Relativity_CKS_InducedSphereAlgebra`, `Relativity_CKS_InducedSphereCalculus`, `Relativity_CKS_LogRadiusJets`, `Relativity_CKS_MainProof`, `Relativity_CKS_NonroundFrame`, `Relativity_CKS_PhysicalCovariantTensor`, `Relativity_CKS_PhysicalCurvatureOperator`, `Relativity_CKS_PhysicalFrameCalculus`, `Relativity_CKS_PhysicalFrameConnection`, `Relativity_CKS_PhysicalFrameCurvature`, `Relativity_CKS_PhysicalFrameTensor`, `Relativity_CKS_PhysicalMomentumCoordinate`, `Relativity_CKS_PhysicalMomentumCovector`, `Relativity_CKS_ScaledPullback`, `Relativity_CKS_SchwarzschildCKS`, `Relativity_CKS_SchwarzschildCKSAlgebra`, `Relativity_CKS_SchwarzschildCKSDecay`, `Relativity_CKS_SchwarzschildCoordinates`, `Relativity_CKS_SchwarzschildEnd`, `Relativity_CKS_SchwarzschildIntrinsicHorizonDefinitions`, `Relativity_CKS_SchwarzschildMetric`, `Relativity_CKS_SchwarzschildModel`, `Relativity_CKS_SchwarzschildPosition`, `Relativity_CKS_SchwarzschildProfile`, `Relativity_CKS_SmoothOuterDEC`, `Relativity_CKS_SphereConeAlgebra`, `Relativity_CKS_SphericalCharts`, `Relativity_CKS_SphericalFrame`, `Relativity_CKS_SphericalTensor`, `Relativity_CKS_TailEnergy`, `Relativity_CKS_TransferDefinitions`.
--
--   **Imports.** It imports the published bundles `Def_CKSBondiPenrose` and `Def_CKSBondiPenrose_002`.
--
--   **Imported by** (directly, in this split): the bundles `Q227CKS002`, `Q227CKS003` and `Q227CKS004`; the statements `OAI_CKSAngularGeometry_local_coordinate_DEC_pushforward`, `OAI_CKSSchwarzschild_metricInner_quad`, `OAI.CKSSchwarzschild.source_minimum_area` and `OAI_CKSSchwarzschild_spherical_vacuum_regular`; the proofs of `OAI_CKSAngularGeometry_local_coordinate_DEC_pushforward` and `OAI_CKSSchwarzschild_sphereConeChartFinrank`.
-- source:
--   OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 260; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSBondiPenrose_002

section
-- module Solutions.Q227_CKS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_AngularGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
abbrev Mat := Matrix I I ℝ

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SmoothOuterDEC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_congr {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (e : E) : D e f x = D e g x := by
  unfold D
  rw [h.fderiv_eq]

lemma D_const (e x : E) (c : ℝ) : D e (fun _ => c) x = 0 := by simp [D]
lemma D_mul (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y * g y) x = f x * D e g x + g x * D e f x := by
  simp [D, fderiv_fun_mul hf hg]
lemma D_const_mul (e : E) {f : E → ℝ} {x : E} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) : D e (fun y => c * f y) x = c * D e f x := by
  rw [D_mul e (differentiableAt_const c) hf, D_const]
  ring
lemma D_clm (e x : E) (A : E →L[ℝ] ℝ) : D e A x = A e := by simp [D]

lemma contDiffAt_D {f : E → ℝ} {x : E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f x)
    {m : ℕ∞ω} (hmn : m + 1 ≤ n) (e : E) : ContDiffAt ℝ m (D e f) x :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

lemma D_sin (e : E) {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    D e (fun y => Real.sin (f y)) x = Real.cos (f x) * D e f x := by
  unfold D
  change fderiv ℝ (Real.sin ∘ f) x e = _
  rw [((Real.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  simp

lemma D_cos (e : E) {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    D e (fun y => Real.cos (f y)) x = -Real.sin (f x) * D e f x := by
  unfold D
  change fderiv ℝ (Real.cos ∘ f) x e = _
  rw [((Real.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  simp

lemma D_comp_real (e : E) {f : ℝ → ℝ} {g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f (g y)) x = deriv f (g x) * D e g x := by
  unfold D
  change fderiv ℝ (f ∘ g) x e = _
  rw [(hf.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt).fderiv]
  simp

end
end CKSCalculus

end

noncomputable section
namespace CKSRound.MetricJet
@[ext] lemma ext_data {j k : MetricJet} (hi : j.inv = k.inv)
    (hd : j.d = k.d) (hdd : j.dd = k.dd) : j = k := by
  cases j
  cases k
  congr
end CKSRound.MetricJet

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound
open scoped Topology ContDiff
def coord (a : Idx) : Point →L[ℝ] ℝ := ContinuousLinearMap.proj a

lemma D_coord (a b : Idx) (x : Point) :
    D (basis a) (coord b) x = if b = a then 1 else 0 := by
  rw [D_clm]
  simp [coord, basis, Pi.single_apply]

end
end CKSRealizedRound

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_NonroundFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open scoped BigOperators Matrix
abbrev I := Fin 3

end
end CKSFrame

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_AdaptedKoszul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open scoped BigOperators
abbrev Coefficients := I → I → I → ℝ

def koszul (b : Coefficients) (i j k : I) : ℝ :=
  (b i j k-b j k i+b k i j)/2

end
end CKSFrame

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_LogRadiusJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def radiusPower (n : ℝ) (x : Point) : ℝ :=
  letI := pointDimension_neZero
  Real.exp (n*x 0)

end
end CKSMixedGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_CKSMetricPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def metricBlock (a : ℝ) (b : Point) (q : Mat) : AmbientMat :=
  !![a,b 0,b 1;b 0,q 0 0,q 0 1;b 1,q 1 0,q 1 1]

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_ScaledPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal

def logRadiusChart (x : Point) : Point :=
  letI := pointDimension_neZero
  fun i => if i = 0 then Real.exp (x 0) else x i

end
end CKSMixedGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_FoliationReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

 def foliationMetric (U : ℝ) (γ : Mat) (s : Point) : AmbientMat :=
  metricBlock (1/U^2+∑ a, ∑ b, γ a b*s a*s b) (fun a => ∑ b, γ a b*s b) γ

 def foliationNormal (U : ℝ) (s : Point) : Fin 3 → ℝ := ![U,-U*s 0,-U*s 1]

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_FoliationKoszul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped BigOperators

 def lowerKoszul (dg : Fin 3 → AmbientMat) (i j k : Fin 3) : ℝ :=
  (dg i j k+dg j i k-dg k i j)/2

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_FoliationPhysicalLeaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSCalculus
open scoped BigOperators Topology

 def actualMetricFirstJet (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) :
    Fin 3 → AmbientMat := fun i j k => D (CKSRealizedRound.basis i) (fun y => G y j k) x

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_CoordinateLeviCivita
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

 def coordinateChristoffel (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint)
    (i j k : Fin 3) : ℝ :=
  ∑ l, lowerKoszul (actualMetricFirstJet G x) i j l * (G x)⁻¹ l k

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_PhysicalFrameCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

 def metricPair (g : AmbientMat) (v w : PhysicalPoint) : ℝ :=
  ∑ i, ∑ j, g i j*v i*w j

lemma direction_expansion (v : PhysicalPoint) :
    v = ∑ i, v i • CKSRealizedRound.basis i := by
  ext j
  simp [CKSRealizedRound.basis, Pi.single_apply]

 def covariantVector (G : PhysicalPoint → AmbientMat) (e : PhysicalPoint)
    (W : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) (k : Fin 3) : ℝ :=
  D e (fun y => W y k) x + ∑ i, ∑ j, e i * W x j * coordinateChristoffel G x i j k

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_PhysicalFrameConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

abbrev LocalFrame := Fin 3 → PhysicalPoint → PhysicalPoint

 def frameCoefficient (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : ℝ :=
  metricPair (G x) (covariantVector G (E i x) (E j) x) (E k x)

 def actualFrameBracket (E : LocalFrame) (x : PhysicalPoint) (i j : Fin 3) : PhysicalPoint :=
  fun k => D (E i x) (fun y => E j y k) x - D (E j x) (fun y => E i y k) x

 def frameBracketCoefficient (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : ℝ :=
  metricPair (G x) (actualFrameBracket E x i j) (E k x)

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_PhysicalFrameCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

 def ActualAdaptedAt (G : PhysicalPoint → AmbientMat) (E : LocalFrame) (x : PhysicalPoint) : Prop :=
  DifferentiableAt ℝ G x ∧ (∀ i, DifferentiableAt ℝ (E i) x) ∧ (G x).PosDef ∧
  (∀ᶠ y in 𝓝 x, (G y).IsHermitian) ∧
  (∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0) ∧
  (∀ a b : Fin 2, frameBracketCoefficient G E x a.succ b.succ 0=0)

 def actualFrameCurvature (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k l : Fin 3) : ℝ :=
  D (E i x) (fun y => frameCoefficient G E y j k l) x -
  D (E j x) (fun y => frameCoefficient G E y i k l) x +
  ∑ m, (frameCoefficient G E x j k m*frameCoefficient G E x i m l -
    frameCoefficient G E x i k m*frameCoefficient G E x j m l -
    frameBracketCoefficient G E x i j m*frameCoefficient G E x m k l)

 def actualFrameScalar (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : ℝ := ∑ i, ∑ j, actualFrameCurvature G E x i j j i

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_PhysicalFrameTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

def frameTensor (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : AmbientMat := fun i j => metricPair (K x) (E i x) (E j x)

def actualFrameTensorCovariant (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : ℝ :=
  D (E i x) (fun y => frameTensor K E y j k) x -
    ∑ a, (frameCoefficient G E x i j a*frameTensor K E x a k+
      frameCoefficient G E x i k a*frameTensor K E x j a)

def actualFrameMomentum (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (j : Fin 3) : ℝ :=
  (∑ i, actualFrameTensorCovariant G K E x i i j)-
    ∑ i, D (E j x) (fun y => frameTensor K E y i i) x

def actualFrameEnergy (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : ℝ :=
  (actualFrameScalar G E x+(∑ i, frameTensor K E x i i)^2-
    ∑ i, ∑ j, (frameTensor K E x i j)^2)/2

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_PhysicalCovariantTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma metricPair_add_right (g : AmbientMat) (v w z : PhysicalPoint) :
    metricPair g v (w+z)=metricPair g v w+metricPair g v z := by
  simp only [metricPair,Pi.add_apply,mul_add,Finset.sum_add_distrib]

def coordinateConnectionVector (G : PhysicalPoint → AmbientMat)
    (e v : PhysicalPoint) (x : PhysicalPoint) (k : Fin 3) : ℝ :=
  ∑ i, ∑ j, e i*v j*coordinateChristoffel G x i j k

def coordinateTensorCovariant (G K : PhysicalPoint → AmbientMat)
    (e v w : PhysicalPoint) (x : PhysicalPoint) : ℝ :=
  metricPair (fun i j => D e (fun y => K y i j) x) v w -
    metricPair (K x) (coordinateConnectionVector G e v x) w -
    metricPair (K x) v (coordinateConnectionVector G e w x)

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_PhysicalMomentumCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

def coordinateMomentum (G K : PhysicalPoint → AmbientMat) (x w : PhysicalPoint) : ℝ :=
  ((G x)⁻¹ * Matrix.of (fun i j => coordinateTensorCovariant G K
    (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x)).trace -
    D w (fun y => ((G y)⁻¹*K y).trace) x

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_FoliationOrthonormalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSCalculus
open scoped BigOperators Topology ContDiff

 def adaptedFrame (U : ℝ) (γ : Mat) (s : Point) : Fin 3 → PhysicalPoint :=
  ![foliationNormal U s,
    ![0,(Real.sqrt (γ 0 0))⁻¹,0],
    ![0,-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det),Real.sqrt (γ 0 0)/Real.sqrt γ.det]]

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_PhysicalMomentumCovector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma metricPair_smul_right (g : AmbientMat) (r : ℝ) (v w : PhysicalPoint) :
    metricPair g v (r • w)=r*metricPair g v w := by
  simp only [metricPair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coordinateConnectionVector_add_right (G : PhysicalPoint → AmbientMat)
    (x e v w : PhysicalPoint) :
    coordinateConnectionVector G e (v+w) x=
      coordinateConnectionVector G e v x+coordinateConnectionVector G e w x := by
  ext k
  simp only [coordinateConnectionVector,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

lemma coordinateConnectionVector_smul_right (G : PhysicalPoint → AmbientMat)
    (x e v : PhysicalPoint) (r : ℝ) :
    coordinateConnectionVector G e (r • v) x=r • coordinateConnectionVector G e v x := by
  ext k
  simp only [coordinateConnectionVector,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def coordinateTensorCovariantLast (G K : PhysicalPoint → AmbientMat)
    (x e v : PhysicalPoint) : PhysicalPoint →ₗ[ℝ] ℝ where
  toFun := fun w => coordinateTensorCovariant G K e v w x
  map_add' := by
    intro w z
    simp only [coordinateTensorCovariant,coordinateConnectionVector_add_right,
      metricPair_add_right]
    erw [metricPair_add_right]
    ring
  map_smul' := by
    intro r w
    simp only [coordinateTensorCovariant,coordinateConnectionVector_smul_right,
      metricPair_smul_right,smul_eq_mul,RingHom.id_apply]
    erw [metricPair_smul_right]
    ring

def coordinateMomentumLinear (G K : PhysicalPoint → AmbientMat)
    (x : PhysicalPoint) : PhysicalPoint →ₗ[ℝ] ℝ where
  toFun := coordinateMomentum G K x
  map_add' := by
    intro w z
    have hc (i j) : coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) (w+z) x=
        coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x+
        coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) z x :=
      (coordinateTensorCovariantLast G K x _ _).map_add w z
    simp only [coordinateMomentum,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.of_apply,hc,mul_add,Finset.sum_add_distrib,D,map_add]
    ring
  map_smul' := by
    intro r w
    have hc (i j) : coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) (r • w) x=
        r*coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x :=
      (coordinateTensorCovariantLast G K x _ _).map_smul r w
    simp only [coordinateMomentum,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.of_apply,hc,D,map_smul,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm _ r,← Finset.mul_sum]
    ring

def momentumCovector (G K : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : PhysicalPoint :=
  fun i => coordinateMomentum G K x (CKSRealizedRound.basis i)

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_PhysicalCurvatureOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def covariantDirectionLinear (G : PhysicalPoint → AmbientMat)
    (W : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) :
    PhysicalPoint →ₗ[ℝ] PhysicalPoint where
  toFun e := covariantVector G e W x
  map_add' e f := by
    ext k
    simp only [covariantVector,D,map_add,Pi.add_apply,
      add_mul,Finset.sum_add_distrib]
    ring
  map_smul' r e := by
    ext k
    simp only [covariantVector,D,map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

def curvatureVector (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : PhysicalPoint :=
  covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x -
  covariantVector G (E j x) (fun y => covariantVector G (E i y) (E k) y) x -
  covariantVector G (actualFrameBracket E x i j) (E k) x

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_AngularSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
abbrev AP := CKSAngularGeometry.Point
abbrev MP := CKSMixedGeometry.Point
abbrev A := Fin 2

 def injection : AP →L[ℝ] MP :=
  ContinuousLinearMap.pi (fun i => Fin.cases 0 (fun a => ContinuousLinearMap.proj a) i)
def slice (r : ℝ) (x : AP) : MP := Pi.single 0 r+injection x

@[simp] lemma injection_zero (x : AP) : injection x 0=0 := rfl
@[simp] lemma injection_succ (x : AP) (a : A) : injection x a.succ=x a := rfl
@[simp] lemma slice_zero (r : ℝ) (x : AP) : slice r x 0=r := by simp [slice]
@[simp] lemma slice_succ (r : ℝ) (x : AP) (a : A) : slice r x a.succ=x a := by simp [slice]

end
end CKSAngularSlice

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_InducedSphereAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Finset
abbrev Mat := Matrix Ix Ix ℝ

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_InducedSphereCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

attribute [local instance] CKSLorentz.two_atLeastTwo

lemma unit_sum_sq {x : E} (hx : ‖x‖ = 1) : ∑ i, x i ^ 2 = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, hx]
  norm_num

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_HeatBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

open MeasureTheory

open scoped Pointwise

open scoped Manifold ContDiff Topology
open Set
instance ambient_finrank : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

def puncturedSpace : TopologicalSpace.Opens Ambient :=
  ⟨{x | x ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩

lemma normalize_mem_sphere (x : Ambient) (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Ambient) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

def normalizeSphere (x : puncturedSpace) : Sphere :=
  ⟨‖(x : Ambient)‖⁻¹ • (x : Ambient), normalize_mem_sphere x x.2⟩

lemma normalizeSphere_smooth : ContMDiff 𝓘(ℝ, Ambient) (𝓡 2) ∞ normalizeSphere := by
  have _hfin := ambient_finrank
  have hcoe : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, Ambient) ∞
      (fun x : puncturedSpace => (x : Ambient)) := contMDiff_subtype_val
  have hn : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, ℝ) ∞
      (fun x : puncturedSpace => ‖(x : Ambient)‖) := by
    intro x
    exact (contDiffAt_norm ℝ (show (x : Ambient) ≠ 0 from x.2)).comp_contMDiffAt hcoe.contMDiffAt
  have h := (hn.inv₀ (fun x => norm_ne_zero_iff.mpr (show (x : Ambient) ≠ 0 from x.2))).smul hcoe
  exact h.codRestrict_sphere (fun x => normalize_mem_sphere x x.2)

end
end CKSSphericalHarmonics

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphericalCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e pd )
open scoped Topology ContDiff

def sphereParam (x : Point) : E := WithLp.toLp 2
  ![Real.sin (x 1)*Real.cos (x 2), Real.sin (x 1)*Real.sin (x 2), Real.cos (x 1)]
def thetaFrame (x : Point) : E := WithLp.toLp 2
  ![Real.cos (x 1)*Real.cos (x 2), Real.cos (x 1)*Real.sin (x 2), -Real.sin (x 1)]
def phiUnit (x : Point) : E := WithLp.toLp 2 ![-Real.sin (x 2), Real.cos (x 2), 0]
def phiFrame (x : Point) : E := Real.sin (x 1) • phiUnit x

def chartVector (i : Ix) (x : Point) : E := ![0,thetaFrame x,phiFrame x] i

lemma sphereParam_smooth : ContDiff ℝ ∞ sphereParam := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> dsimp [sphereParam] <;> fun_prop

lemma sphereParam_norm (x : Point) : ‖sphereParam x‖ = 1 := by
  have h := EuclideanSpace.norm_sq_eq (sphereParam x)
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three] at h
  change ‖sphereParam x‖^2 = (Real.sin (x 1)*Real.cos (x 2))^2 +
    (Real.sin (x 1)*Real.sin (x 2))^2 + Real.cos (x 1)^2 at h
  have h₂ := congrArg (fun z : ℝ => Real.sin (x 1)^2*z)
    (Real.sin_sq_add_cos_sq (x 2))
  nlinarith [Real.sin_sq_add_cos_sq (x 1), norm_nonneg (sphereParam x)]

lemma component_fderiv {f : Point → E} {x : Point} (hf : DifferentiableAt ℝ f x)
    (v : Point) (i : Ix) :
    (fderiv ℝ f x v) i = D v (fun y => f y i) x := by
  have h := ((EuclideanSpace.proj i).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  exact (congrArg (fun L : Point →L[ℝ] ℝ => L v) h).symm

lemma fderiv_sphereParam (x : Point) (i : Ix) :
    fderiv ℝ sphereParam x (basis i) = chartVector i x := by
  ext j
  rw [component_fderiv (sphereParam_smooth.differentiable (by simp) x)]
  have hd1 : DifferentiableAt ℝ (fun y : Point => y 1) x := (coord 1).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 :=
    D_coord a b x
  fin_cases i <;> fin_cases j <;>
    dsimp [sphereParam, chartVector, thetaFrame, phiFrame, phiUnit]
  all_goals
    simp only [D_mul _ hd1.sin hd2.cos, D_mul _ hd1.sin hd2.sin,
      D_sin _ hd1, D_sin _ hd2, D_cos _ hd1, D_cos _ hd2, dc, Fin.reduceEq, ite_false, if_false, ite_true, if_true]
    norm_num
    <;> ring

end
end CKSSphericalChart

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphericalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e pd )
open scoped Topology ContDiff

lemma theta_tangent (x : Point) : ∑ i : Ix, sphereParam x i * thetaFrame x i = 0 := by
  simp only [Fin.sum_univ_three]
  change (Real.sin (x 1)*Real.cos (x 2))*(Real.cos (x 1)*Real.cos (x 2)) +
    (Real.sin (x 1)*Real.sin (x 2))*(Real.cos (x 1)*Real.sin (x 2)) +
    Real.cos (x 1)*(-Real.sin (x 1)) = 0
  linear_combination Real.sin (x 1)*Real.cos (x 1)*(Real.sin_sq_add_cos_sq (x 2))

lemma unit_tangent (x : Point) : ∑ i : Ix, sphereParam x i * phiUnit x i = 0 := by
  simp only [Fin.sum_univ_three]
  change (Real.sin (x 1)*Real.cos (x 2))*(-Real.sin (x 2)) +
    (Real.sin (x 1)*Real.sin (x 2))*Real.cos (x 2) + Real.cos (x 1)*0 = 0
  ring

lemma theta_unit (x : Point) : (∑ i : Ix, thetaFrame x i ^ 2) = 1 := by
  simp only [Fin.sum_univ_three]
  change (Real.cos (x 1)*Real.cos (x 2))^2 + (Real.cos (x 1)*Real.sin (x 2))^2 + (-Real.sin (x 1))^2 = 1
  linear_combination (Real.cos (x 1)^2)*(Real.sin_sq_add_cos_sq (x 2)) + Real.sin_sq_add_cos_sq (x 1)

lemma unit_unit (x : Point) : (∑ i : Ix, phiUnit x i ^ 2) = 1 := by
  simp only [Fin.sum_univ_three]
  change (-Real.sin (x 2))^2 + Real.cos (x 2)^2 + (0:ℝ)^2 = 1
  nlinarith [Real.sin_sq_add_cos_sq (x 2)]

lemma theta_unit_orthogonal (x : Point) : (∑ i : Ix, thetaFrame x i * phiUnit x i) = 0 := by
  simp only [Fin.sum_univ_three]
  change (Real.cos (x 1)*Real.cos (x 2))*(-Real.sin (x 2)) +
    (Real.cos (x 1)*Real.sin (x 2))*Real.cos (x 2) + (-Real.sin (x 1))*0 = 0
  ring

end
end CKSSphericalChart

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphericalTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e pd )
open scoped Topology ContDiff

def pair (M : Mat) (v w : E) : ℝ := ∑ i : Ix, ∑ j : Ix, v i * w j * M i j

@[simp] lemma pair_zero_left (M : Mat) (v : E) : pair M 0 v = 0 := by simp [pair]
@[simp] lemma pair_zero_right (M : Mat) (v : E) : pair M v 0 = 0 := by simp [pair]
@[simp] lemma pair_smul_left (M : Mat) (c : ℝ) (v w : E) :
    pair M (c • v) w = c * pair M v w := by simp [pair, mul_assoc, mul_sum]
@[simp] lemma pair_smul_right (M : Mat) (c : ℝ) (v w : E) :
    pair M v (c • w) = c * pair M v w := by
  simp only [pair, PiLp.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring
@[simp] lemma pair_neg_left (M : Mat) (v w : E) : pair M (-v) w = -pair M v w := by
  simpa only [neg_one_smul, neg_one_mul] using pair_smul_left M (-1) v w
@[simp] lemma pair_neg_right (M : Mat) (v w : E) : pair M v (-w) = -pair M v w := by
  simpa only [neg_one_smul, neg_one_mul] using pair_smul_right M (-1) v w
@[simp] lemma pair_add_left (M : Mat) (u v w : E) :
    pair M (u+v) w = pair M u w + pair M v w := by
  simp [pair, add_mul, sum_add_distrib]
@[simp] lemma pair_add_right (M : Mat) (u v w : E) :
    pair M u (v+w) = pair M u v + pair M u w := by
  simp [pair, mul_add, add_mul, sum_add_distrib]

end
end CKSSphericalChart

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_ConstructedOuterMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

def boost (e m : ℝ) (p : E) (x : V) : V :=
  ((e*x.1 + inner ℝ p x.2)/m,
    x.2 + (x.1/m + inner ℝ p x.2/(m*(e+m))) • p)

lemma boost_smooth (e m : ℝ) (p : E) : ContDiff ℝ ∞ (boost e m p) := by
  have hi : ContDiff ℝ ∞ (fun x : V => inner ℝ p x.2) := ContDiff.inner ℝ contDiff_const contDiff_snd
  unfold boost
  exact (((contDiff_const.mul contDiff_fst).add hi).div_const m).prodMk
    (contDiff_snd.add (((contDiff_fst.div_const m).add
      (hi.div_const (m*(e+m)))).smul contDiff_const))

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

def boostCLM (e m : ℝ) (p : E) : V →L[ℝ] V where
  toFun := boost e m p
  map_add' := by
    intro x y
    apply Prod.ext
    · simp only [boost, Prod.fst_add, Prod.snd_add, inner_add_right] <;> ring
    · simp only [boost, Prod.fst_add, Prod.snd_add, inner_add_right]
      module
  map_smul' := by
    intro c x
    apply Prod.ext
    · change (e*(c*x.1) + inner ℝ p (c • x.2))/m = c*((e*x.1 + inner ℝ p x.2)/m)
      rw [inner_smul_right]
      ring
    · change c • x.2 + ((c*x.1)/m + inner ℝ p (c • x.2)/(m*(e+m))) • p =
        c • (x.2 + (x.1/m + inner ℝ p x.2/(m*(e+m))) • p)
      rw [inner_smul_right]
      module
  cont := (boost_smooth e m p).continuous

@[simp] lemma boostCLM_apply (e m : ℝ) (p : E) (x : V) :
    boostCLM e m p x = boost e m p x := rfl

instance instFactEqNatFinrankRealEHAddOfNat : Fact (Module.finrank ℝ E = 2+1) := ⟨by simp [E]⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def inverseLogRadiusChart (x : Point) : Point :=
  letI := pointDimension_neZero
  fun i => if i=0 then Real.exp (-x 0) else x i

def backwardFactor (a : I) (y : Point) : ℝ :=
  letI := pointDimension_neZero
  if a=0 then -y 0 else 1

def backwardScaledD (a : I) (f : Point → ℝ) (y : Point) : ℝ :=
  backwardFactor a y * D (basis a) f y

def backwardScaledIter (directions : List I) (function : Point → ℝ) : Point → ℝ :=
  directions.foldr backwardScaledD function

@[simp] lemma backwardScaledIter_nil (function : Point → ℝ) :
    backwardScaledIter [] function = function := by
  simp only [backwardScaledIter, List.foldr_nil]

@[simp] lemma backwardScaledIter_cons (direction : I) (directions : List I)
    (function : Point → ℝ) :
    backwardScaledIter (direction :: directions) function =
      backwardScaledD direction (backwardScaledIter directions function) := by
  simp only [backwardScaledIter, List.foldr_cons]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

@[simp] lemma angularProjection_inverseLogRadiusChart (x : Point) :
    angularProjection (inverseLogRadiusChart x) = angularProjection x := by
  ext a
  simp [angularProjection,inverseLogRadiusChart,Fin.succ_ne_zero]

@[simp] lemma angularProjection_logRadiusChart (x : Point) :
    angularProjection (logRadiusChart x) = angularProjection x := by
  ext a
  simp [angularProjection,logRadiusChart,Fin.succ_ne_zero]

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def radialEigenvalue (t : ℝ) (directions : List I) : ℝ :=
  letI := pointDimension_neZero
  directions.foldr (fun direction product => (t*basis direction 0)*product) 1

@[simp] lemma radialEigenvalue_nil (exponent : ℝ) :
    radialEigenvalue exponent [] = 1 := by
  simp only [radialEigenvalue, List.foldr_nil]

@[simp] lemma radialEigenvalue_cons (exponent : ℝ) (direction : I)
    (directions : List I) :
    radialEigenvalue exponent (direction :: directions) =
      (exponent*basis direction 0)*radialEigenvalue exponent directions := by
  simp only [radialEigenvalue, List.foldr_cons]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus CKSAngularSlice
open scoped ContDiff Topology

def radialLogChart (y : Point) : Point :=
  letI := pointDimension_neZero
  fun i => if i=0 then Real.log (y 0) else y i

@[simp] lemma radialLogChart_logRadiusChart (x : Point) :
    radialLogChart (logRadiusChart x) = x := by
  ext i
  by_cases hi : i=0 <;> simp [radialLogChart,logRadiusChart,hi]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem stereoDimension : Fact (Module.finrank ℝ E = 2+1) := ⟨by simp [E]⟩

attribute [local instance] stereoDimension

def stereoAngleEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] Angle :=
  EuclideanSpace.equiv (Fin 2) ℝ

def stereoOrthogonalEquiv (v : Sphere) : (ℝ ∙ (v:E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr

def stereoAngularChart (v : Sphere) : OpenPartialHomeomorph Sphere Angle :=
  (stereographic' 2 v).trans stereoAngleEquiv.toHomeomorph.toOpenPartialHomeomorph

def stereoAngularExtension (v : Sphere) (x : E) : Angle :=
  stereoAngleEquiv (stereoOrthogonalEquiv v (stereoToFun (v:E) x))

def stereoAmbientDomain (v : Sphere) : Set E :=
  letI := two_atLeastTwo
  letI : Inner ℝ E :=
    @InnerProductSpace.toInner ℝ E _
      (PiLp.seminormedAddCommGroup 2 (fun _ : Fin 3 => ℝ))
      (PiLp.innerProductSpace (fun _ : Fin 3 => ℝ))
  {x | inner ℝ (v:E) x ≠ 1}

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

attribute [local instance] stereoDimension

@[simp] lemma stereoAngularChart_source (v : Sphere) :
    (stereoAngularChart v).source = {v}ᶜ := by
  simp [stereoAngularChart]

@[simp] lemma stereoAngularChart_target (v : Sphere) :
    (stereoAngularChart v).target = univ := by
  simp [stereoAngularChart]

lemma stereoAngularChart_param (v : Sphere) (θ : Angle) :
    ((stereoAngularChart v).symm θ : E) = stereoInvFunAux (v:E)
      ((stereoOrthogonalEquiv v).symm (stereoAngleEquiv.symm θ) : E) := rfl

lemma stereoAngularChart_param_smooth (v : Sphere) :
    ContDiff ℝ ∞ (fun θ => ((stereoAngularChart v).symm θ : E)) := by
  simp_rw [stereoAngularChart_param]
  exact contDiff_stereoInvFunAux.comp
    ((ℝ ∙ (v:E))ᗮ.subtypeL.contDiff.comp
      ((stereoOrthogonalEquiv v).symm.toContinuousLinearEquiv.contDiff.comp
        stereoAngleEquiv.symm.contDiff))

lemma stereoAmbientDomain_open (v : Sphere) : IsOpen (stereoAmbientDomain v) :=
  isOpen_ne_fun (innerSL ℝ (v:E)).continuous continuous_const

lemma stereoAngularExtension_smooth (v : Sphere) :
    ContDiffOn ℝ ∞ (stereoAngularExtension v) (stereoAmbientDomain v) := by
  exact stereoAngleEquiv.contDiff.comp_contDiffOn
    ((stereoOrthogonalEquiv v).toContinuousLinearEquiv.contDiff.comp_contDiffOn
      contDiffOn_stereoToFun)

lemma stereoAngularChart_source_domain (v n : Sphere)
    (hn : n ∈ (stereoAngularChart v).source) : (n:E) ∈ stereoAmbientDomain v := by
  change inner ℝ (v:E) (n:E) ≠ 1
  intro h
  have he : v=n := (sphere_ext_iff v n).mpr h
  simp [stereoAngularChart_source,he] at hn

lemma stereoAngularExtension_eq (v n : Sphere) :
    stereoAngularExtension v n=stereoAngularChart v n := rfl

def stereoSmoothPatch (v : Sphere) : SmoothAngularPatch where
  chart := stereoAngularChart v
  param_smooth := (stereoAngularChart_param_smooth v).contDiffOn
  extension := stereoAngularExtension v
  domain := stereoAmbientDomain v
  isOpen_domain := stereoAmbientDomain_open v
  extension_smooth := stereoAngularExtension_smooth v
  source_domain := stereoAngularChart_source_domain v
  extension_eq := fun n _ => stereoAngularExtension_eq v n

namespace SmoothAngularPatch

lemma param_sphere (P : SmoothAngularPatch) (θ : Angle) :
    P.param θ ∈ Metric.sphere (0:E) 1 := (P.chart.symm θ).2

lemma param_norm (patch : SmoothAngularPatch) (angle : Angle) : ‖patch.param angle‖ = 1 :=
  (dist_zero_right (patch.param angle)).symm.trans (Metric.mem_sphere.mp (patch.param_sphere angle))

lemma param_contDiffAt (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target) :
    ContDiffAt ℝ ∞ P.param θ :=
  P.param_smooth.contDiffAt (P.chart.open_target.mem_nhds hθ)

end SmoothAngularPatch
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularSlice Set
open scoped ContDiff Topology

@[simp] lemma angularProjection_radialLogChart (y : Point) :
    angularProjection (radialLogChart y) = angularProjection y := by
  ext a
  simp [angularProjection,radialLogChart]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

namespace SmoothAngularPatch

lemma extension_param (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target) :
    P.extension (P.param θ)=θ := by
  rw [show P.param θ=(P.chart.symm θ:E) from rfl,
    P.extension_eq _ (P.chart.map_target hθ)]
  exact P.chart.right_inv hθ

lemma extension_contDiffAt_param (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : ContDiffAt ℝ ∞ P.extension (P.param θ) := by
  exact P.extension_smooth.contDiffAt (P.isOpen_domain.mem_nhds
    (P.source_domain _ (P.chart.map_target hθ)))

lemma param_tangent (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (v : Angle) : inner ℝ (P.param θ) (fderiv ℝ P.param θ v) = 0 := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hconst : (fun η => inner ℝ (P.param η) (P.param η)) = fun _ : Angle => (1:ℝ) := by
    funext η
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖P.param η‖=1 := P.param_norm η
    rw [hn,one_pow]
  have hd := fderiv_inner_apply (𝕜:=ℝ) hφ hφ v
  rw [hconst] at hd
  simp only [fderiv_fun_const] at hd
  change 0 = inner ℝ (P.param θ) (fderiv ℝ P.param θ v) +
    inner ℝ (fderiv ℝ P.param θ v) (P.param θ) at hd
  have hc := real_inner_comm (fderiv ℝ P.param θ v) (P.param θ)
  linarith

end SmoothAngularPatch

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped Topology ContDiff
lemma polarParam_contDiffAt (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) : ContDiffAt ℝ ∞ (polarParam P) y := by
  exact (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).contDiff.contDiffAt.smul
    ((P.param_contDiffAt hy).comp y angularProjection.contDiff.contDiffAt)
lemma polarParam_norm (P : SmoothAngularPatch) {y : Point} (hy : 0 ≤ y 0) :
    ‖polarParam P y‖ = y 0 := by
  have hn : ‖P.param (angularProjection y)‖=1 := P.param_norm (angularProjection y)
  simp only [polarParam,norm_smul,Real.norm_eq_abs,abs_of_nonneg hy,hn,mul_one]
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma angularRadialTail_open (R : ℝ) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (angularRadialTail R W) := by
  exact (isOpen_Ioi.preimage (continuous_apply 0)).inter
    (hW.preimage angularProjection.continuous)

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped ContDiff Topology
lemma scaledIter_congr_germ {f g : Point → ℝ} {y : Point} (h : f =ᶠ[𝓝 y] g)
    (l : List I) : scaledIter l f =ᶠ[𝓝 y] scaledIter l g := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    filter_upwards [ih.fderiv (𝕜:=ℝ)] with z hz
    exact congrArg (fun L : Point →L[ℝ] ℝ => radialFactor a z * L (basis a)) hz
lemma SourceRemainderOn.congrOn {j q : ℕ} {V : Set Point} {f g : Point → ℝ}
    (hf : SourceRemainderOn j q V f) (hV : IsOpen V) (he : EqOn f g V) :
    SourceRemainderOn j q V g := by
  have hg {y} (hy : y ∈ V) : f =ᶠ[𝓝 y] g := by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact he hz
  refine ⟨fun y hy => (hf.regular y hy).congr_of_eventuallyEq (hg hy).symm,?_⟩
  obtain ⟨B,hB,hb⟩ := hf.bound
  refine ⟨B,hB,?_⟩
  intro y hy l hl
  rw [← (scaledIter_congr_germ (hg hy) l).eq_of_nhds]
  exact hb y hy l hl
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalEnergy (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : ℝ :=
  (actualFrameScalar G E x + ((G x)⁻¹*K x).trace^2 -
    ((G x)⁻¹*K x*(G x)⁻¹*K x).trace)/2

def physicalDEC (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : Prop :=
  Real.sqrt (metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x)) ≤
    physicalEnergy G K E x

end
end CKSAngularGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BoostTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open Set

def normalizeAmbient (x : E) : E := ‖x‖⁻¹ • x

lemma normalizeAmbient_smooth {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ normalizeAmbient x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

@[simp] lemma normalizeAmbient_sphere (n : Sphere) : normalizeAmbient n = n := by
  simp [normalizeAmbient]

end
end CKSLorentz

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BondiBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def polarInverse (P : SmoothAngularPatch) (x : E) : Point :=
  slice ‖x‖ (P.extension (normalizeAmbient x))
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma normalizeAmbient_polarParam (P : SmoothAngularPatch) {y : Point} (hr : 0 < y 0) :
    normalizeAmbient (polarParam P y) = P.param (angularProjection y) := by
  rw [normalizeAmbient,polarParam_norm P hr.le,polarParam,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
lemma slice_projection (y : Point) : slice (y 0) (angularProjection y) = y := by
  funext i
  refine Fin.cases ?_ (fun a => ?_) i
  · exact slice_zero _ _
  · exact slice_succ _ _ a
lemma polarInverse_param (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    polarInverse P (polarParam P y)=y := by
  simp only [polarInverse,polarParam_norm P hr.le,normalizeAmbient_polarParam P hr,
    P.extension_param hy,slice_projection]
lemma polarInverse_smoothAt_param (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    ContDiffAt ℝ ∞ (polarInverse P) (polarParam P y) := by
  have hn : polarParam P y ≠ 0 := norm_ne_zero_iff.mp (by rw [polarParam_norm P hr.le]; exact hr.ne')
  have he : ContDiffAt ℝ ∞ P.extension (normalizeAmbient (polarParam P y)) := by
    rw [normalizeAmbient_polarParam P hr]
    exact P.extension_contDiffAt_param hy
  have hθ := he.comp (polarParam P y) (normalizeAmbient_smooth hn)
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [polarInverse,slice_zero] using contDiffAt_norm ℝ hn (n := ∞)
  · simpa only [polarInverse,slice_succ,Function.comp_apply] using contDiffAt_pi.mp hθ a
lemma polarInverse_fderiv_left (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (fderiv ℝ (polarInverse P) (polarParam P y)).comp (fderiv ℝ (polarParam P) y) =
      ContinuousLinearMap.id ℝ Point := by
  have hh : (polarInverse P ∘ polarParam P) =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hr,
      angularProjection.continuous.continuousAt.preimage_mem_nhds (P.chart.open_target.mem_nhds hy)] with z hz hzt
    exact polarInverse_param P hz hzt
  have hg := hh.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp y ((polarInverse_smoothAt_param P hr hy).differentiableAt (by simp))
    ((polarParam_contDiffAt P hy).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),fderiv_id] at hg
  exact hg
lemma polarParam_fderiv_injective (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    Function.Injective (fderiv ℝ (polarParam P) y) := by
  intro v w hvw
  have hleft z := congrArg (fun L : Point →L[ℝ] Point => L z) (polarInverse_fderiv_left P hr hy)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hleft
  rw [← hleft v,← hleft w,hvw]
lemma polarParam_fderiv_surjective (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    Function.Surjective (fderiv ℝ (polarParam P) y) := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [CKSMixedGeometry.Point,E])).mp (polarParam_fderiv_injective P hr hy)
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

@[simp] lemma logRadiusChart_slice (ρ : ℝ) (x : AP) :
    logRadiusChart (slice ρ x)=slice (Real.exp ρ) x := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma polarParam_fderiv (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (v : Point) :
    fderiv ℝ (polarParam P) y v = v 0 • P.param (angularProjection y) +
      y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) := by
  have hP := (P.param_contDiffAt hy).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hp := (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).hasFDerivAt (x := y)
  have ha := hP.hasFDerivAt.comp y angularProjection.hasFDerivAt
  have hh := hp.smul ha
  change HasFDerivAt (polarParam P) _ y at hh
  rw [hh.fderiv]
  change y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) + v 0 • P.param (angularProjection y) = _
  exact add_comm _ _
lemma polarParam_fderiv_radial (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) :
    fderiv ℝ (polarParam P) y (basis 0) = P.param (angularProjection y) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis 0) = 0 := by ext a; simp [angularProjection,basis,Fin.succ_ne_zero]
  rw [ha]
  simp [basis]
lemma polarParam_fderiv_angular (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (a : Fin 2) :
    fderiv ℝ (polarParam P) y (basis a.succ) = y 0 • fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis a.succ) = CKSAngularGeometry.basis a := by
    ext b
    simp [angularProjection,basis,CKSAngularGeometry.basis,Pi.single_apply,Fin.succ_inj]
  rw [ha]
  simp [basis,Fin.succ_ne_zero]

end
end CKSLorentz

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_TailEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSCalculus CKSAngularGeometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

abbrev A := Fin 3
abbrev P := PhysicalPoint
abbrev Vect := PhysicalPoint
abbrev Symbols := A → A → A → ℝ

def delta (v : Vect) (f : P → ℝ) (x : P) : ℝ := D v f x

def bracket (V W : P → Vect) (x : P) : Vect := fun k =>
  delta (V x) (fun y => W y k) x - delta (W x) (fun y => V y k) x

def nabla (Γ : P → Symbols) (v : Vect) (W : P → Vect) (x : P) : Vect := fun k =>
  delta v (fun y => W y k) x + ∑ i : A, ∑ j : A, v i * W x j * Γ x k i j

def curvature (Γ : P → Symbols) (V W Z : P → Vect) (x : P) : Vect :=
  nabla Γ (V x) (fun y => nabla Γ (W y) Z y) x -
    nabla Γ (W x) (fun y => nabla Γ (V y) Z y) x - nabla Γ (bracket V W x) Z x

def coordCurvature (Γ : P → Symbols) (x : P) (k l i j : A) : ℝ :=
  D (CKSRealizedRound.basis i) (fun y => Γ y k j l) x -
    D (CKSRealizedRound.basis j) (fun y => Γ y k i l) x +
    ∑ m : A, (Γ x m j l * Γ x k i m - Γ x m i l * Γ x k j m)

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSAngularGeometry
open scoped BigOperators

def pair (γ : AmbientMat) (v w : Vect) : ℝ := ∑ i : A, ∑ j : A, γ i j * v i * w j

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalSymbols (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) :
    CKSAmbientCalculus.Symbols := fun a i j => coordinateChristoffel G x i j a

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

structure SmoothOrthonormalAt (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : Prop where
  metric_smooth : ContDiffAt ℝ ∞ G x
  frame_smooth : ∀ i, ContDiffAt ℝ ∞ (E i) x
  positive : (G x).PosDef
  symmetric : ∀ᶠ y in 𝓝 x, (G y).IsHermitian
  orthonormal : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0

structure FrameChartAt (φ : PhysicalPoint → PhysicalPoint)
    (G H : PhysicalPoint → AmbientMat) (E F : LocalFrame) (x : PhysicalPoint) : Prop where
  chart_smooth : ContDiffAt ℝ ∞ φ x
  source : SmoothOrthonormalAt G E (φ x)
  target : SmoothOrthonormalAt H F x
  frame_related : ∀ᶠ y in 𝓝 x, ∀ i, fderiv ℝ φ y (F i y) = E i (φ y)
  metric_related : ∀ v w, metricPair (H x) v w =
    metricPair (G (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def coordinatePullback (φ : PhysicalPoint → PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : AmbientMat := fun i j =>
  metricPair (G (φ x)) (fderiv ℝ φ x (CKSRealizedRound.basis i))
    (fderiv ℝ φ x (CKSRealizedRound.basis j))
def coordinatePullbackFrame (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (E : LocalFrame) : LocalFrame := fun i x => fderiv ℝ e.symm (e x) (E i (e x))
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
def sphericalMap (x : PhysicalPoint) : PhysicalPoint := toPoint (x 0 • sphereParam x)
def sphericalBasis (x : PhysicalPoint) (i : Fin 3) : E :=
  ![sphereParam x,x 0 • thetaFrame x,x 0 • phiFrame x] i
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma sphericalMap_smooth : ContDiff ℝ ∞ sphericalMap :=
  toPoint.contDiff.comp ((coord 0).contDiff.smul sphereParam_smooth)
lemma sphericalMap_fderiv (x : PhysicalPoint) (i : Fin 3) :
    fderiv ℝ sphericalMap x (basis i) = toPoint (sphericalBasis x i) := by
  have hd : DifferentiableAt ℝ (fun y : PhysicalPoint => y 0 • sphereParam y) x :=
    (coord 0).differentiableAt.smul (sphereParam_smooth.differentiable (by simp) x)
  rw [show sphericalMap = toPoint ∘ (fun y : PhysicalPoint => y 0 • sphereParam y) from rfl,
    fderiv_comp x toPoint.differentiableAt hd,ContinuousLinearEquiv.fderiv,
    ContinuousLinearMap.comp_apply]
  change toPoint (fderiv ℝ (fun y : PhysicalPoint => y 0 • sphereParam y) x (basis i)) = toPoint (sphericalBasis x i)
  apply congrArg toPoint
  change fderiv ℝ (fun y : PhysicalPoint => (coord 0) y • sphereParam y) x (basis i) = _
  rw [fderiv_fun_smul (coord 0).differentiableAt (sphereParam_smooth.differentiable (by simp) x)]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, fderiv_sphereParam]
  have hc : fderiv ℝ (coord 0) x (basis i) = if 0=i then 1 else 0 := D_coord i 0 x
  rw [hc]
  fin_cases i <;> simp [sphericalBasis,chartVector] <;> rfl
lemma pair_one (v w : E) : pair (1 : AmbientMat) v w=∑ i, v i*w i := by
  simp [pair,Matrix.one_apply]
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma pair_one_symm (v w : E) : pair (1 : AmbientMat) v w=pair (1 : AmbientMat) w v := by
  rw [pair_one,pair_one]
  apply Finset.sum_congr rfl
  intro i _
  ring
def unitBasis (x : PhysicalPoint) (i : Fin 3) : E := ![sphereParam x,thetaFrame x,phiUnit x] i
def sphericalScale (x : PhysicalPoint) (i : Fin 3) : ℝ := ![1,x 0,x 0*Real.sin (x 1)] i
lemma sphericalBasis_scaled (x : PhysicalPoint) (i : Fin 3) :
    sphericalBasis x i=sphericalScale x i • unitBasis x i := by
  fin_cases i <;> simp [sphericalBasis,sphericalScale,unitBasis,phiFrame,smul_smul]
lemma pair_one_unitBasis (x : PhysicalPoint) (i j : Fin 3) :
    pair (1 : AmbientMat) (unitBasis x i) (unitBasis x j)=if i=j then 1 else 0 := by
  have hnn : pair (1 : AmbientMat) (sphereParam x) (sphereParam x)=1 := by
    rw [pair_one]
    simpa only [sq] using unit_sum_sq (sphereParam_norm x)
  have hnθ : pair (1 : AmbientMat) (sphereParam x) (thetaFrame x)=0 := by
    rw [pair_one]; exact theta_tangent x
  have hnu : pair (1 : AmbientMat) (sphereParam x) (phiUnit x)=0 := by
    rw [pair_one]; exact unit_tangent x
  have hθθ : pair (1 : AmbientMat) (thetaFrame x) (thetaFrame x)=1 := by
    rw [pair_one]; simpa only [sq] using theta_unit x
  have huu : pair (1 : AmbientMat) (phiUnit x) (phiUnit x)=1 := by
    rw [pair_one]; simpa only [sq] using unit_unit x
  have hθu : pair (1 : AmbientMat) (thetaFrame x) (phiUnit x)=0 := by
    rw [pair_one]; exact theta_unit_orthogonal x
  have hθn := (pair_one_symm (thetaFrame x) (sphereParam x)).trans hnθ
  have hun := (pair_one_symm (phiUnit x) (sphereParam x)).trans hnu
  have huθ := (pair_one_symm (phiUnit x) (thetaFrame x)).trans hθu
  fin_cases i <;> fin_cases j <;>
    simp [unitBasis,hnn,hnθ,hnu,hθθ,huu,hθu,hθn,hun,huθ]
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma pair_sum_right (M : AmbientMat) (v : E) (w : Fin 3 → E) :
    pair M v (∑ i,w i)=∑ i,pair M v (w i) := by
  simp [Fin.sum_univ_three,pair_add_right]
lemma sphericalMap_fderiv_component (x v : PhysicalPoint) (j : Fin 3) :
    pair (1 : AmbientMat) (unitBasis x j) (toPoint.symm (fderiv ℝ sphericalMap x v))=
      sphericalScale x j*v j := by
  conv_lhs => pattern v; rw [direction_expansion v]
  simp only [map_sum,map_smul,sphericalMap_fderiv,toPoint.symm_apply_apply,
    pair_sum_right,pair_smul_right,sphericalBasis_scaled,pair_one_unitBasis]
  simp [mul_ite,Finset.sum_ite_eq,mul_comm]
lemma sphericalMap_fderiv_injective {x : PhysicalPoint} (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : Function.Injective (fderiv ℝ sphericalMap x) := by
  intro v w h
  funext j
  have hh := congrArg (fun z => pair (1 : AmbientMat) (unitBasis x j) (toPoint.symm z)) h
  rw [sphericalMap_fderiv_component,sphericalMap_fderiv_component] at hh
  have hscale : sphericalScale x j≠0 := by
    fin_cases j <;> simp [sphericalScale,hx,hs]
  exact mul_left_cancel₀ hscale hh
noncomputable def sphericalDerivativeEquiv (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : PhysicalPoint ≃L[ℝ] PhysicalPoint :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ sphericalMap x)
    (LinearMap.ker_eq_bot.mpr (sphericalMap_fderiv_injective hx hs))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp (sphericalMap_fderiv_injective hx hs)))
lemma sphericalDerivative_hasFDerivAt (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : HasFDerivAt sphericalMap (sphericalDerivativeEquiv x hx hs : PhysicalPoint →L[ℝ] PhysicalPoint) x :=
  (sphericalMap_smooth.differentiable (by simp) x).hasFDerivAt
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable def sphericalChart (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : OpenPartialHomeomorph PhysicalPoint PhysicalPoint :=
  sphericalMap_smooth.contDiffAt.toOpenPartialHomeomorph sphericalMap
    (sphericalDerivative_hasFDerivAt x hx hs) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
@[simp] lemma sphericalChart_coe (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : (sphericalChart x hx hs : PhysicalPoint → PhysicalPoint) = sphericalMap := rfl
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
structure ContinuousMetricJetAt (g : PhysicalPoint → CKSRound.MetricJet) (x : PhysicalPoint) : Prop where
  inv : ∀ i j, ContinuousAt (fun y => (g y).inv i j) x
  d : ∀ a i j, ContinuousAt (fun y => (g y).d a i j) x
  dd : ∀ a b i j, ContinuousAt (fun y => (g y).dd a b i j) x
structure ContinuousTensorJetAt (k : PhysicalPoint → CKSRound.TensorJet) (x : PhysicalPoint) : Prop where
  val : ∀ i j, ContinuousAt (fun y => (k y).val i j) x
  d : ∀ a i j, ContinuousAt (fun y => (k y).d a i j) x
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
abbrev cartesianPolar (P : SmoothAngularPatch) (y : Point) : Point :=
  CKSCartesianOuter.toPoint (polarParam P y)
lemma cartesianPolar_smoothAt (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) :
    ContDiffAt ℝ ∞ (cartesianPolar P) y :=
  CKSCartesianOuter.toPoint.contDiff.contDiffAt.comp y (polarParam_contDiffAt P hy)
lemma cartesianPolar_fderiv (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) :
    fderiv ℝ (cartesianPolar P) y =
      CKSCartesianOuter.toPoint.toContinuousLinearMap.comp (fderiv ℝ (polarParam P) y) := by
  change fderiv ℝ (CKSCartesianOuter.toPoint ∘ polarParam P) y = _
  rw [fderiv_comp y CKSCartesianOuter.toPoint.differentiableAt
    ((polarParam_contDiffAt P hy).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),ContinuousLinearEquiv.fderiv]
noncomputable def polarDerivative (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) : Point ≃L[ℝ] Point :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (cartesianPolar P) y)
    (LinearMap.ker_eq_bot.mpr (by
      rw [cartesianPolar_fderiv P hy]
      exact CKSCartesianOuter.toPoint.injective.comp (polarParam_fderiv_injective P hr hy)))
    (LinearMap.range_eq_top.mpr (by
      rw [cartesianPolar_fderiv P hy]
      exact CKSCartesianOuter.toPoint.surjective.comp (polarParam_fderiv_surjective P hr hy)))
lemma polarDerivative_hasFDerivAt (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    HasFDerivAt (cartesianPolar P) (polarDerivative P hr hy).toContinuousLinearMap y :=
  (cartesianPolar_smoothAt P hy).differentiableAt (by simp) |>.hasFDerivAt
noncomputable def polarCartesianChart (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    OpenPartialHomeomorph Point Point :=
  (cartesianPolar_smoothAt P hy).toOpenPartialHomeomorph (cartesianPolar P)
    (polarDerivative_hasFDerivAt P hr hy) (by simp)
@[simp] lemma polarCartesianChart_coe (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (polarCartesianChart P hr hy : Point → Point) = cartesianPolar P := rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
local instance sgpNorm : NormedAddCommGroup SpatialBilinear :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance sgpSpace : NormedSpace ℝ SpatialBilinear := ContinuousLinearMap.toNormedSpace
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] CKSSpatialManifold.real_id_isometric real_smulCommClass
  spatialDual_smulCommClass
attribute [local instance] OAI.CKSLorentz.hsgNorm

attribute [local instance] OAI.CKSLorentz.hsgSpace

theorem spatialBilinear_isScalarTower : IsScalarTower ℝ ℝ SpatialBilinear where
  smul_assoc scalar factor form := by
    ext first second
    change (scalar * factor) * form first second = scalar * (factor * form first second)
    exact mul_assoc scalar factor (form first second)

attribute [local instance] spatialBilinear_isScalarTower

lemma hyperbolicField_smooth : ContDiff ℝ ∞ hyperbolicField := by
  unfold hyperbolicField
  exact contDiff_const.sub ((contDiff_const.div (contDiff_const.add (contDiff_norm_sq ℝ))
    (fun x => by positivity)).smul ((innerSL ℝ).contDiff.smulRight (innerSL ℝ).contDiff))
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
lemma angularMetricTrace_add (σ A B : AngularMatrix) :
    angularMetricTrace σ (A+B)=angularMetricTrace σ A+angularMetricTrace σ B := by
  simp only [angularMetricTrace,Matrix.mul_add,Matrix.trace_add]
lemma angularMetricTrace_smul (σ A : AngularMatrix) (c : ℝ) :
    angularMetricTrace σ (c • A)=c*angularMetricTrace σ A := by
  simp only [angularMetricTrace,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
lemma cksChartMassAspect_split (φ : Angle → E) (mr : Angle → ℝ)
    (mg mK : I → I → Angle → ℝ) (θ : Angle) :
    cksChartMassAspect φ mr mg mK θ =
      angularMetricTrace (angularRoundMetric φ θ) (fun a b => mg a.succ b.succ θ) +
      2*angularMetricTrace (angularRoundMetric φ θ) (fun a b => mK a.succ b.succ θ) + 2*mr θ := by
  let σ := angularRoundMetric φ θ
  let A : AngularMatrix := fun a b => mg a.succ b.succ θ
  let B : AngularMatrix := fun a b => mK a.succ b.succ θ
  change angularMetricTrace σ (A + (2:ℝ) • B) + 2*mr θ =
    angularMetricTrace σ A + 2*angularMetricTrace σ B + 2*mr θ
  rw [angularMetricTrace_add,angularMetricTrace_smul]

end
end CKSLorentz

end

noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set Manifold MeasureTheory CKSReplacementCompleteness
open scoped ContDiff ENNReal NNReal
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H3 M]
  [IsManifold I3 1 M] [T3Space M]

def identityOuterDomain [IsManifold I3 ∞ M] [ConnectedSpace M]
    (hS : IsCompact (I3.boundary M)) : OuterDomain M where
  Carrier := M
  topology := inferInstance
  charts := inferInstance
  smooth := inferInstance
  inclusion := id
  embedding := IsSmoothEmbedding.id
  closed := by simpa only [range_id] using (isClosed_univ : IsClosed (univ : Set M))
  connected := by simpa only [range_id] using (isConnected_univ : IsConnected (univ : Set M))
  contains_distant_end := ⟨∅,isCompact_empty,by simp⟩
  interior_into := by simp
  compact_boundary := by simpa using hS

end
end CKSGeometricCuts

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] real_id_isometric CKSMetricGluing.real_continuousAdd
  CKSMetricGluing.real_continuousConstSMul CKSMetricGluing.real_smulCommClass

theorem covector_smulCommClass {Space : Type*} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] :
    letI := CKSLorentz.real_smulCommClass
    SMulCommClass ℝ ℝ (Space →L[ℝ] ℝ) := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

attribute [local instance] covector_smulCommClass

abbrev SpatialTangentTriv := Trivialization E (π E (fun x : M => TangentSpace I x))
local instance spatialScalarAtlas : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℝ) := ⟨rfl⟩
def spatialBilinearTriv (e : SpatialTangentTriv I (M := M)) [MemTrivializationAtlas e] :
    Trivialization SpatialBilinear (π SpatialBilinear (fun x : M =>
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  letI := CKSLorentz.real_smulCommClass
  e.continuousLinearMap (RingHom.id ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Bundle.Trivial.trivialization M ℝ))
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] spatialScalarAtlas real_id_isometric CKSMetricGluing.real_continuousAdd
  CKSMetricGluing.real_continuousConstSMul CKSMetricGluing.real_smulCommClass
  covector_smulCommClass
local instance bilNorm : NormedAddCommGroup SpatialBilinear :=
  letI := CKSLorentz.real_smulCommClass
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance bilSpace : NormedSpace ℝ SpatialBilinear :=
  letI := CKSLorentz.real_smulCommClass
  letI := covector_smulCommClass (Space := E)
  ContinuousLinearMap.toNormedSpace
instance spatialBilinearTriv_atlas (e : SpatialTangentTriv I (M := M)) [MemTrivializationAtlas e] :
    MemTrivializationAtlas (spatialBilinearTriv I e) := by unfold spatialBilinearTriv; infer_instance
@[simp] lemma spatialBilinearTriv_baseSet (e : SpatialTangentTriv I (M := M)) [MemTrivializationAtlas e] :
    (spatialBilinearTriv I e).baseSet = e.baseSet := by simp [spatialBilinearTriv]
lemma spatialBilinearTriv_pair (e : SpatialTangentTriv I (M := M)) [MemTrivializationAtlas e]
    {x : M} (hx : x ∈ e.baseSet)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
    ((spatialBilinearTriv I e) ⟨x,B⟩).2 v w = B (e.symmL ℝ x v) (e.symmL ℝ x w) := by
  let := CKSLorentz.real_smulCommClass
  unfold spatialBilinearTriv
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ))
    (show x ∈ (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ)).baseSet by simpa using hx)]
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (Trivial.trivialization M ℝ) (show x ∈ (Trivial.trivialization M ℝ).baseSet from mem_univ x)]
  rfl
lemma mfderiv_gauge_smooth {f : M → E} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, E) ∞ f x) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun y => ((NormedSpace.fromTangentSpace (f y)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, E) f y)).comp
        ((trivializationAt E (TangentSpace I) x).symmL ℝ y)) x := by
  have h := hf.mfderiv_const (show (∞ : ℕ∞ω) + 1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space, NormedSpace.fromTangentSpace]
  rfl

omit [IsManifold I ∞ M] in
lemma bilinearComp_smoothAt [IsManifold I ∞ M]
    {B : M → SpatialBilinear} {A : M → E →L[ℝ] E} {x : M}
    (hB : ContMDiffAt I 𝓘(ℝ, SpatialBilinear) ∞ B x)
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ A x) :
    ContMDiffAt I 𝓘(ℝ, SpatialBilinear) ∞ (fun y => (B y).bilinearComp (A y) (A y)) x := by
  have flipSmooth : ContDiff ℝ ∞ (fun B : SpatialBilinear => B.flip) :=
    by
      let L : SpatialBilinear →L[ℝ] SpatialBilinear := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      exact L.contDiff
  exact flipSmooth.comp_contMDiffAt
    ((flipSmooth.comp_contMDiffAt (hB.clm_comp hA)).clm_comp hA)
lemma endInner_smoothAt {f : M → E} {A : SpatialTensor} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x)
    (hA : ContDiffAt ℝ ∞ A (f x)) :
    ContMDiffAt I (I.prod 𝓘(ℝ,SpatialBilinear)) ∞
      (innerSection I (endInner I f A)) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  apply ((spatialBilinearTriv I e).contMDiffAt_section_iff (IB := I) (n := ∞)
    (F := SpatialBilinear) (s := endInner I f A)
    (show x ∈ (spatialBilinearTriv I e).baseSet by simpa using hx)).mpr
  have hB := hA.contMDiffAt.comp x hf
  apply (bilinearComp_smoothAt hB (mfderiv_gauge_smooth hf)).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  ext v w
  rw [spatialBilinearTriv_pair e hy]
  rfl
lemma positive_bilinear_bounded (B : SpatialBilinear) (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    IsVonNBounded ℝ {v : E | B v v < 1} := by
  have hc : Continuous (fun v : E => B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨a,ha,hm⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.continuousOn
  have haNorm : ‖a‖ = 1 := by simpa [Metric.mem_sphere] using ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at haNorm
  have hp : 0 < B a a := hB a ha0
  have hlow : ∀ v : E, B a a * ‖v‖ ^ 2 ≤ B v v := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hy : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have h := hm (show (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : E) 1 by
      simpa [Metric.mem_sphere] using hy)
    have he : B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) = B v v / ‖v‖^2 := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      field_simp
    change B a a ≤ B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) at h
    rw [he] at h
    exact (le_div_iff₀ (sq_pos_of_pos hn)).mp h
  apply (NormedSpace.isVonNBounded_iff ℝ).mpr
  apply (Metric.isBounded_iff_subset_ball (0 : E)).mpr
  refine ⟨1 + (B a a)⁻¹, ?_⟩
  intro v hv
  change dist v 0 < 1 + (B a a)⁻¹
  rw [dist_zero_right]
  have hbv : B v v < 1 := hv
  have hl := hlow v
  have hinv : 0 < (B a a)⁻¹ := inv_pos.mpr hp
  have he : B a a * (B a a)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  by_contra hh
  have hn : 1 + (B a a)⁻¹ ≤ ‖v‖ := le_of_not_gt hh
  have hn1 : 1 ≤ ‖v‖ := by linarith
  have hn2 : ‖v‖ ≤ ‖v‖^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hn hp.le
  have hmul2 := mul_le_mul_of_nonneg_left hn2 hp.le
  nlinarith
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
lemma endInner_fullRank (g : SmoothMetric I (M := M)) (f : M → E)
    (A : SpatialTensor) {x : M} (heq : g.inner x = endInner I f A x) :
    Function.Bijective (mfderiv I 𝓘(ℝ,E) f x) := by
  let : FiniteDimensional ℝ (TangentSpace I x) := by exact (inferInstance : FiniteDimensional ℝ E)
  have hi : Function.Injective (mfderiv I 𝓘(ℝ,E) f x) := by
    intro v w hvw
    by_contra hne
    have hp := g.pos x (v-w) (sub_ne_zero.mpr hne)
    rw [heq] at hp
    have hz : (mfderiv I 𝓘(ℝ,E) f x) (v-w) = 0 := by rw [map_sub,hvw,sub_self]
    change 0 < A (f x) ((mfderiv I 𝓘(ℝ,E) f x) (v-w))
      ((mfderiv I 𝓘(ℝ,E) f x) (v-w)) at hp
    rw [hz] at hp
    have ha : A (f x) (0:E) (0:E) = 0 := by simp
    exact (lt_irrefl 0) (ha ▸ hp)
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
end
end CKSSpatialManifold

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BoundaryFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal
namespace CKSIntrinsicGeometry
attribute [local instance] halfSpaceDimension_neZero

section Charts
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 1 M]

lemma boundary_chart_zero (x y : M) (hy : y ∈ (extChartAt I3 x).source)
    (hS : y ∈ I3.boundary M) : (extChartAt I3 x y) 0 = 0 := by
  have hychart : y ∈ (chartAt H3 x).source := by simpa using hy
  have hyrange : extChartAt I3 x y ∈ range I3 :=
    (extChartAt_target_subset_range x) ((extChartAt I3 x).map_source hy)
  have hnonneg : 0 ≤ (extChartAt I3 x y) 0 := by
    simpa only [I3, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hyrange
  have hnot : ¬I3.IsInteriorPoint y :=
    (I3.isBoundaryPoint_iff_not_isInteriorPoint y).mp hS
  have hle : (extChartAt I3 x y) 0 ≤ 0 := by
    by_contra h
    have hpos : 0 < (extChartAt I3 x y) 0 := lt_of_not_ge h
    have hint : extChartAt I3 x y ∈ interior (range I3) := by
      simpa only [I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hpos
    apply hnot
    apply (I3.isInteriorPoint_iff_of_mem_atlas one_ne_zero (chart_mem_atlas H3 x) hychart).mpr
    exact (chartAt H3 x).mem_interior_extend_target ((chartAt H3 x).map_source hychart) hint
  exact le_antisymm hle hnonneg
end Charts

end CKSIntrinsicGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BoundaryCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSBoundarySurface

@[simp] lemma liftPlane_zero (z : E2) : liftPlane z 0 = 0 := rfl
@[simp] lemma liftPlane_succ (z : E2) (i : Fin 2) : liftPlane z i.succ = z i := rfl
@[simp] lemma dropPlane_apply (z : E3) (i : Fin 2) : dropPlane z i = z i.succ := rfl
@[simp] lemma drop_lift (z : E2) : dropPlane (liftPlane z) = z := by ext i; rfl
@[simp] lemma I3_liftHalf (z : E2) : I3 (liftHalf z) = liftPlane z := rfl

attribute [local instance] halfSpaceDimension_neZero

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M]

lemma boundary_iff_zero (x y : M) (hy : y ∈ (chartAt H3 x).source) :
    y ∈ I3.boundary M ↔ (I3 (chartAt H3 x y)) 0 = 0 := by
  constructor
  · exact CKSIntrinsicGeometry.boundary_chart_zero x y (by simpa using hy)
  · intro hz
    apply (I3.isBoundaryPoint_iff_not_isInteriorPoint y).mpr
    intro hi
    have hin := (I3.isInteriorPoint_iff_of_mem_atlas
      (by simp : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas H3 x) hy).mp hi
    have hr := (chartAt H3 x).interior_extend_target_subset_interior_range hin
    have hp : 0 < (I3 (chartAt H3 x y)) 0 := by
      simpa only [I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
        OpenPartialHomeomorph.extend_coe, Function.comp_apply] using hr
    rw [hz] at hp
    exact (lt_irrefl 0) hp

end CKSBoundarySurface

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BoundaryPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSBoundarySurface
attribute [local instance] Classical.propDecidable
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 halfSpaceDimension_neZero) I3 ∞ M _ _]

lemma boundaryInverse_val (x : Boundary M) {z : E2}
    (hz : liftHalf z ∈ (chartAt H3 x.val).target) :
    (boundaryInverse x z).val = (chartAt H3 x.val).symm (liftHalf z) := by
  simp only [boundaryInverse,dite_eq_left hz]

@[simp] lemma boundaryChart_source (x : Boundary M) :
    (boundaryChart x).source = Subtype.val ⁻¹' (chartAt H3 x.val).source := rfl
@[simp] lemma boundaryChart_target (x : Boundary M) :
    (boundaryChart x).target = liftHalf ⁻¹' (chartAt H3 x.val).target := rfl
@[simp] lemma boundaryChart_apply (x y : Boundary M) :
    boundaryChart x y = dropPlane (I3 (chartAt H3 x.val y.val)) := rfl
lemma boundaryChart_symm_val (x : Boundary M) {z : E2} (hz : z ∈ (boundaryChart x).target) :
    ((boundaryChart x).symm z).val = (chartAt H3 x.val).symm (liftHalf z) :=
  boundaryInverse_val x hz

end CKSBoundarySurface

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildModel
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface
attribute [local instance] Classical.propDecidable

@[simp] lemma join_zero (z : ℝ × E2) : join z 0 = z.1 := rfl
@[simp] lemma join_succ (z : ℝ × E2) (i : Fin 2) : join z i.succ = z.2 i := rfl
@[simp] lemma drop_join (z : ℝ × E2) : dropPlane (join z) = z.2 := by ext i; rfl
@[simp] lemma join_drop (z : E3) : join (z 0,dropPlane z) = z := by
  ext i; cases i using Fin.cases <;> rfl

@[simp] lemma halfProduct_val (z : Radial × E2) : (halfProduct z).val = join (z.1.val,z.2) := rfl
@[simp] lemma halfProduct_symm_fst (z : H3) : (halfProduct.symm z).1.val = z.val 0 := rfl
@[simp] lemma halfProduct_symm_snd (z : H3) : (halfProduct.symm z).2 = dropPlane z.val := rfl

@[simp] lemma productChart_source (s : Sphere) :
    (productChart s).source = Prod.snd ⁻¹' (chartAt E2 s).source := by
  ext p; simp [productChart]
attribute [local instance] halfSpaceDimension_neZero

@[simp] lemma productChart_target (s : Sphere) :
    (productChart s).target = (fun z : H3 => dropPlane z.val) ⁻¹' (chartAt E2 s).target := by
  ext p; simp [productChart]
@[simp] lemma productChart_apply (s : Sphere) (p : Exterior) :
    (productChart s p).val = join (p.1.val,chartAt E2 s p.2) := rfl
@[simp] lemma productChart_symm (s : Sphere) (z : H3) :
    (productChart s).symm z = (⟨z.val 0,z.property⟩,(chartAt E2 s).symm (dropPlane z.val)) := rfl

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BoundarySmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle Filter Function
open scoped ContDiff Topology
namespace CKSBoundarySurface
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M]

lemma inclusion_chart_formula (x : Boundary M) {z : E2}
    (hz : z ∈ (boundaryChart x).target) :
    writtenInExtChartAt I2 I3 x (Subtype.val : Boundary M → M) z = liftPlane z := by
  change I3 (chartAt H3 x.val (((boundaryChart x).symm z).val)) = _
  rw [boundaryChart_symm_val x hz, (chartAt H3 x.val).right_inv hz]
  rfl

lemma inclusion_chart_eventually (x : Boundary M) :
    writtenInExtChartAt I2 I3 x (Subtype.val : Boundary M → M) =ᶠ[𝓝 (extChartAt I2 x x)] liftPlane := by
  have ht : (boundaryChart x).target ∈ 𝓝 (extChartAt I2 x x) :=
    (boundaryChart x).open_target.mem_nhds ((boundaryChart x).map_source (mem_chart_source E2 x))
  filter_upwards [ht] with z hz
  exact inclusion_chart_formula x hz

lemma inclusion_smooth : ContMDiff I2 I3 ∞ (Subtype.val : Boundary M → M) := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  exact ((liftPlane.contDiff.contDiffAt).congr_of_eventuallyEq (inclusion_chart_eventually x)).contDiffWithinAt

lemma inclusion_hasMFDeriv (x : Boundary M) :
    HasMFDerivAt I2 I3 (Subtype.val : Boundary M → M) x liftPlane := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  exact (liftPlane.hasFDerivAt.congr_of_eventuallyEq (inclusion_chart_eventually x)).hasFDerivWithinAt

end CKSBoundarySurface

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_InducedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
namespace CKSInducedArea
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass
  real_id_isometric

section Trivializations
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one

attribute [local instance] tangent_vectorBundle

omit [IsManifold I ∞ M] in
attribute [local instance] scalar_smulCommClass

attribute [local instance] scalar_vectorBundle

attribute [local instance] scalar_continuousSMul

attribute [local instance] covector_vectorBundle

omit [IsManifold I ∞ M] in
attribute [local instance] covector_topologicalAddGroup

omit [IsManifold I ∞ M] in
attribute [local instance] covector_continuousSMul

attribute [local instance] OAI.CKSInducedArea.scalarAtlas

attribute [local instance] covector_atlas

@[simp] lemma bilinearTriv_baseSet (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] : (bilinearTriv I e).baseSet = e.baseSet := by
  simp [bilinearTriv]
end Trivializations

attribute [local instance] OAI.CKSInducedArea.bilNorm2

attribute [local instance] OAI.CKSInducedArea.bilSpace2

attribute [local instance] OAI.CKSInducedArea.bilNorm3

attribute [local instance] OAI.CKSInducedArea.bilSpace3

attribute [local instance] OAI.CKSInducedArea.mixNorm23

attribute [local instance] OAI.CKSInducedArea.mixSpace23

attribute [local instance] OAI.CKSInducedArea.mixNorm32

attribute [local instance] OAI.CKSInducedArea.mixSpace32

lemma positive_bilinear_bounded (B : Bil2) (hB : ∀ v : E2, v ≠ 0 → 0 < B v v) :
    IsVonNBounded ℝ {v : E2 | B v v < 1} := by
  have hc : Continuous (fun v : E2 => B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨a,ha,hm⟩ := (isCompact_sphere (0 : E2) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.continuousOn
  have haNorm : ‖a‖ = 1 := by simpa [Metric.mem_sphere] using ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at haNorm
  have hp : 0 < B a a := hB a ha0
  have hlow : ∀ v : E2, B a a * ‖v‖ ^ 2 ≤ B v v := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hy : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have h := hm (show (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : E2) 1 by
      simpa [Metric.mem_sphere] using hy)
    have he : B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) = B v v / ‖v‖^2 := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      field_simp
    change B a a ≤ B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) at h
    rw [he] at h
    exact (le_div_iff₀ (sq_pos_of_pos hn)).mp h
  apply (NormedSpace.isVonNBounded_iff ℝ).mpr
  apply (Metric.isBounded_iff_subset_ball (0 : E2)).mpr
  refine ⟨1 + (B a a)⁻¹, ?_⟩
  intro v hv
  change dist v 0 < 1 + (B a a)⁻¹
  rw [dist_zero_right]
  have hbv : B v v < 1 := hv
  have hl := hlow v
  have hinv : 0 < (B a a)⁻¹ := inv_pos.mpr hp
  have he : B a a * (B a a)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  by_contra hh
  have hn : 1 + (B a a)⁻¹ ≤ ‖v‖ := le_of_not_gt hh
  have hn1 : 1 ≤ ‖v‖ := by linarith
  have hn2 : ‖v‖ ≤ ‖v‖^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hn hp.le
  have hmul2 := mul_le_mul_of_nonneg_left hn2 hp.le
  nlinarith

end CKSInducedArea

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

def angular (p : Exterior) : Sphere := p.2

def firstCoordinate : E3 →L[ℝ] ℝ := EuclideanSpace.proj ⟨0, Nat.zero_lt_succ 2⟩

lemma extChart_formula (p y : Exterior) : extChartAt I3 p y = join (height y,chartAt E2 p.2 y.2) := rfl
lemma inverseChart_height (p : Exterior) {z : E3} (hz : z ∈ range I3) :
    height ((extChartAt I3 p).symm z) = z 0 := by
  change (I3.symm z).val 0 = z 0
  exact congrArg (fun w : E3 => w 0) (I3.right_inv hz)
lemma inverseChart_angular (p : Exterior) {z : E3} (hz : z ∈ range I3) :
    angular ((extChartAt I3 p).symm z) = (chartAt E2 p.2).symm (dropPlane z) := by
  change (chartAt E2 p.2).symm (dropPlane (I3.symm z).val) = _
  rw [show (I3.symm z).val = z from I3.right_inv hz]

lemma angular_chart_eq (p : Exterior) :
    writtenInExtChartAt I3 I2 p angular =ᶠ[𝓝[range I3] extChartAt I3 p p] dropPlane := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I3) p] with z hz
  have hzr := extChartAt_target_subset_range (I := I3) p hz
  have hz' : dropPlane z ∈ (chartAt E2 p.2).target := by
    have h := (extChartAt I3 p).map_target hz
    have hi := (extChartAt I3 p).right_inv hz
    rw [extChart_formula] at hi
    have hh := congrArg dropPlane hi
    simp only [drop_join] at hh
    rw [← hh]
    apply (chartAt E2 p.2).map_source
    rw [extChartAt_source] at h
    change (extChartAt I3 p).symm z ∈ (productChart p.2).source at h
    simpa only [productChart_source, mem_preimage] using h
  change chartAt E2 p.2 (angular ((extChartAt I3 p).symm z)) = _
  rw [inverseChart_angular p hzr,(chartAt E2 p.2).right_inv hz']

lemma height_chart_eq (p : Exterior) :
    writtenInExtChartAt I3 𝓘(ℝ,ℝ) p height =ᶠ[𝓝[range I3] extChartAt I3 p p] firstCoordinate := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact inverseChart_height p hz

lemma angular_chart_self (p : Exterior) :
    writtenInExtChartAt I3 I2 p angular (extChartAt I3 p p) = dropPlane (extChartAt I3 p p) := by
  change chartAt E2 p.2 (angular ((extChartAt I3 p).symm (extChartAt I3 p p))) = _
  rw [extChartAt_to_inv,extChart_formula,drop_join]
  rfl
lemma height_chart_self (p : Exterior) :
    writtenInExtChartAt I3 𝓘(ℝ,ℝ) p height (extChartAt I3 p p) = firstCoordinate (extChartAt I3 p p) := by
  exact inverseChart_height p (extChartAt_target_subset_range (I := I3) p (mem_extChartAt_target p))

lemma angular_smooth : ContMDiff I3 I2 ∞ angular := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuous_snd.continuousAt,?_⟩
  exact dropPlane.contDiff.contDiffWithinAt.congr_of_eventuallyEq (angular_chart_eq p) (angular_chart_self p)
lemma height_smooth : ContMDiff I3 𝓘(ℝ,ℝ) ∞ height := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(continuous_subtype_val.comp continuous_fst).continuousAt,?_⟩
  exact firstCoordinate.contDiff.contDiffWithinAt.congr_of_eventuallyEq (height_chart_eq p) (height_chart_self p)
lemma mfderiv_angular (p : Exterior) : mfderiv I3 I2 angular p = dropPlane := by
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_snd.continuousAt,?_⟩
  exact dropPlane.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq (angular_chart_eq p) (angular_chart_self p)
lemma mfderiv_height (p : Exterior) : mfderiv I3 𝓘(ℝ,ℝ) height p = firstCoordinate := by
  apply HasMFDerivAt.mfderiv
  refine ⟨(continuous_subtype_val.comp continuous_fst).continuousAt,?_⟩
  exact firstCoordinate.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq (height_chart_eq p) (height_chart_self p)

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildPosition
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Function
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩

lemma radius_pos {m : ℝ} (hm : 0 < m) (p : Exterior) : 0 < radius m p := by
  have hp := p.1.property
  unfold radius height
  linarith
lemma radius_ge (m : ℝ) (p : Exterior) : 2*m ≤ radius m p := by
  have hp := p.1.property
  unfold radius height
  linarith
lemma radius_smooth (m : ℝ) : ContMDiff I3 𝓘(ℝ,ℝ) ∞ (radius m) :=
  contMDiff_const.add height_smooth
lemma directionAmbient_smooth : ContMDiff I3 𝓘(ℝ,E3) ∞ directionAmbient :=
  (contMDiff_coe_sphere (n := 2) (E := E3)).comp angular_smooth
lemma position_smooth (m : ℝ) : ContMDiff I3 𝓘(ℝ,E3) ∞ (position m) :=
  (radius_smooth m).smul directionAmbient_smooth
lemma norm_direction (p : Exterior) : ‖directionAmbient p‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right,directionAmbient] using p.2.property
lemma norm_position {m : ℝ} (hm : 0 < m) (p : Exterior) : ‖position m p‖ = radius m p := by
  rw [position,norm_smul,norm_direction,mul_one,Real.norm_eq_abs,abs_of_pos (radius_pos hm p)]

lemma mfderiv_radius (m : ℝ) (p : Exterior) : mfderiv I3 𝓘(ℝ,ℝ) (radius m) p = firstCoordinate := by
  have h := (hasMFDerivAt_const (I := I3) (I' := 𝓘(ℝ,ℝ)) (2*m) p).add
    ((height_smooth p).mdifferentiableAt (by simp)).hasMFDerivAt
  have he := h.mfderiv
  rw [mfderiv_height] at he
  change mfderiv I3 𝓘(ℝ,ℝ) (radius m) p = (0 : E3 →L[ℝ] ℝ) + firstCoordinate at he
  simpa only [zero_add] using he

lemma mfderiv_directionAmbient (p : Exterior) :
    mfderiv I3 𝓘(ℝ,E3) directionAmbient p =
      (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) p.2).comp dropPlane := by
  have h := mfderiv_comp (I := I3) (I' := I2) (I'' := 𝓘(ℝ,E3))
    (f := angular) (g := (Subtype.val : Sphere → E3)) p
    ((contMDiff_coe_sphere (n := 2) (m := ∞) p.2).mdifferentiableAt (by simp))
    ((angular_smooth p).mdifferentiableAt (by simp))
  rw [mfderiv_angular] at h
  exact h

lemma directionAmbient_orthogonal (p : Exterior) (v : E3) :
    ⟪directionAmbient p, mfderiv I3 𝓘(ℝ,E3) directionAmbient p v⟫_ℝ = 0 := by
  rw [mfderiv_directionAmbient]
  have h : (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) p.2).range =
      (ℝ ∙ (p.2.val : E3))ᗮ := by
    convert! range_mvfderiv_subtypeVal (n := 2) p.2
  have hv : (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) p.2) (dropPlane v) ∈
      (ℝ ∙ (p.2.val : E3))ᗮ := by
    rw [← h]
    exact ⟨dropPlane v,rfl⟩
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv)

def ambientDerivative (f : Exterior → E3) (p : Exterior) : E3 →L[ℝ] E3 := by
  exact mfderiv I3 𝓘(ℝ,E3) f p

lemma mfderiv_position (m : ℝ) (p : Exterior) (v : E3) :
    ambientDerivative (position m) p v =
      (radius m p) • ambientDerivative directionAmbient p v +
        (v 0) • directionAmbient p := by
  have hr := ((radius_smooth m p).mdifferentiableAt (by simp)).hasMFDerivAt
  have hn := ((directionAmbient_smooth p).mdifferentiableAt (by simp)).hasMFDerivAt
  let D : E3 →L[ℝ] E3 :=
    (radius m p) • ambientDerivative directionAmbient p +
      firstCoordinate.smulRight (directionAmbient p)
  have hd : HasMFDerivAt I3 𝓘(ℝ,E3) (position m) p D := by
    refine ⟨(position_smooth m).continuous.continuousAt,?_⟩
    have h := hr.2.smul hn.2
    simp only [writtenInExtChartAt,Function.comp_apply,mfld_simps,
      mfderiv_radius,chartAt_self_eq] at h
    change HasFDerivWithinAt (writtenInExtChartAt I3 𝓘(ℝ,E3) p (position m)) D
      (range I3) (extChartAt I3 p p) at h
    exact h

  exact congrArg (fun L => L v) hd.mfderiv

lemma position_derivative_injective {m : ℝ} (hm : 0 < m) (p : Exterior) :
    Injective (ambientDerivative (position m) p) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hv' := hv
  change ambientDerivative (position m) p v = 0 at hv'
  rw [mfderiv_position] at hv'
  change radius m p • ambientDerivative directionAmbient p v + (v 0) • directionAmbient p = 0 at hv'
  have hinner := congrArg (fun w : E3 => ⟪directionAmbient p,w⟫_ℝ) hv'
  have hn : ⟪directionAmbient p,directionAmbient p⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq,norm_direction]; norm_num
  have ho : ⟪directionAmbient p,ambientDerivative directionAmbient p v⟫_ℝ = 0 :=
    directionAmbient_orthogonal p v
  simp only [inner_add_right,inner_smul_right,ho,hn,mul_zero,mul_one,
    zero_add,inner_zero_right] at hinner
  have hdir : mfderiv I3 𝓘(ℝ,E3) directionAmbient p v = 0 := by
    rw [hinner,zero_smul,add_zero] at hv'
    exact (smul_eq_zero.mp hv').resolve_left (ne_of_gt (radius_pos hm p))
  have hdrop : dropPlane v = 0 := by
    rw [mfderiv_directionAmbient] at hdir
    have injectiveSphere : Injective (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) p.2) := by
      convert! injective_mvfderiv_subtypeVal_sphere (n := 2) p.2
    exact injectiveSphere (hdir.trans (map_zero _).symm)
  rw [← join_drop v,hinner,hdrop]
  exact map_zero _

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma velocity_smooth (m : ℝ) : ContDiff ℝ ∞ (velocity m) := by
  unfold velocity
  exact contDiff_const.add ((contDiff_id.add contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).sub contDiff_const)))
lemma velocity_near (m r : ℝ) (hr : r ≤ 2*m+1) : velocity m r = -1 := by
  simp [velocity,Real.smoothTransition.zero_of_nonpos (by linarith : r-2*m-1 ≤ 0)]
lemma lapseSquared_pos {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) : 0 < lapseSquared m r := by
  have hrp : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) hm) hr
  rcases eq_or_lt_of_le hr with he|he
  · have hv := velocity_near m r (by linarith)
    have hm0 : m ≠ 0 := ne_of_gt hm
    subst r
    simp [lapseSquared,hv,hm0]
  · have hh : 2*m/r < 1 := (div_lt_one hrp).mpr he
    have hsq := sq_nonneg (velocity m r)
    unfold lapseSquared
    linarith
lemma lapseSquared_smoothAt {m r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ∞ (lapseSquared m) r := by
  exact (contDiffAt_const.sub (contDiffAt_const.div contDiffAt_id (ne_of_gt hr))).add
    ((velocity_smooth m).contDiffAt.pow 2)

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildMetric
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Manifold Bundle Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
attribute [local instance] CKSSpatialManifold.real_id_isometric
local instance instIsBoundedSMulRealSpatialBilinear : IsBoundedSMul ℝ SpatialBilinear :=
  @NormedSpace.toIsBoundedSMul ℝ SpatialBilinear _ _ _
local instance instTopologicalSpaceTotalSpaceExteriorContinuousLinearMapRealIdE3TangentSpaceEuclideanSpaceFinOfNatNatEuclideanHalfSpaceI3 : TopologicalSpace (TotalSpace (E3 →L[ℝ] ℝ)
    (fun x : Exterior => TangentSpace I3 x →L[ℝ] ℝ)) := inferInstance

lemma radialUnit_smoothAt {x : E3} (hx : x ≠ 0) : ContDiffAt ℝ ∞ radialUnit x := by
  exact ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
lemma radialForm_smoothAt {x : E3} (hx : x ≠ 0) : ContDiffAt ℝ ∞ radialForm x := by
  have h := (innerSL ℝ).contDiff.contDiffAt.comp x (radialUnit_smoothAt hx)
  convert h.smulRight h using 1
  all_goals try with_reducible_and_instances rfl
  ext y v w
  rfl
lemma cartMetric_smoothAt {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) :
    ContDiffAt ℝ ∞ (cartMetric m) x := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (mul_pos (by norm_num) hm) hr
  have hx : x ≠ 0 := norm_pos_iff.mp hn
  exact contDiffAt_const.add (((lapseSquared_smoothAt hn).comp x
    (contDiffAt_norm ℝ hx)).inv (ne_of_gt (lapseSquared_pos hm hr)) |>.sub contDiffAt_const |>.smul
      (radialForm_smoothAt hx))
lemma velocity_deriv_smooth (m : ℝ) : ContDiff ℝ ∞ (deriv (velocity m)) := by
  exact ((contDiff_infty_iff_deriv).mp (velocity_smooth m)).2
lemma cartTensor_smoothAt {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) :
    ContDiffAt ℝ ∞ (cartTensor m) x := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (mul_pos (by norm_num) hm) hr
  have hx : x ≠ 0 := norm_pos_iff.mp hn
  have hnorm := contDiffAt_norm ℝ hx (n := ∞)
  have hv := ((velocity_smooth m).contDiffAt.comp x hnorm).div hnorm (ne_of_gt hn)
  have hd := ((velocity_deriv_smooth m).contDiffAt.comp x hnorm).div
    ((lapseSquared_smoothAt hn).comp x hnorm) (ne_of_gt (lapseSquared_pos hm hr))
  exact (hv.smul contDiffAt_const).add ((hd.sub hv).smul (radialForm_smoothAt hx))

lemma euclideanForm_apply (v w : E3) : euclideanForm v w = ⟪v,w⟫_ℝ := rfl
lemma radialForm_apply (x v w : E3) :
    radialForm x v w = ⟪radialUnit x,v⟫_ℝ * ⟪radialUnit x,w⟫_ℝ := rfl
lemma cartMetric_apply (m : ℝ) (x v w : E3) :
    cartMetric m x v w = ⟪v,w⟫_ℝ + ((lapseSquared m ‖x‖)⁻¹-1) *
      (⟪radialUnit x,v⟫_ℝ * ⟪radialUnit x,w⟫_ℝ) := rfl
lemma cartMetric_symm (m : ℝ) (x v w : E3) : cartMetric m x v w = cartMetric m x w v := by
  rw [cartMetric_apply,cartMetric_apply,real_inner_comm v w,mul_comm (⟪radialUnit x,v⟫_ℝ)]
lemma cartTensor_symm (m : ℝ) (x v w : E3) : cartTensor m x v w = cartTensor m x w v := by
  change velocity m ‖x‖ / ‖x‖ * ⟪v,w⟫_ℝ +
      (deriv (velocity m) ‖x‖ / lapseSquared m ‖x‖ - velocity m ‖x‖ / ‖x‖) *
      (⟪radialUnit x,v⟫_ℝ * ⟪radialUnit x,w⟫_ℝ) = _
  simp only [cartTensor,add_apply,smul_apply,
    smul_eq_mul,euclideanForm_apply,radialForm_apply,real_inner_comm v w,
    mul_comm (⟪radialUnit x,v⟫_ℝ)]
lemma norm_radialUnit {x : E3} (hx : x ≠ 0) : ‖radialUnit x‖ = 1 := by
  rw [radialUnit,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
lemma cartMetric_pos {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖)
    (v : E3) (hv : v ≠ 0) : 0 < cartMetric m x v v := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (mul_pos (by norm_num) hm) hr
  have hbound := real_inner_mul_inner_self_le (radialUnit x) v
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,norm_radialUnit (norm_pos_iff.mp hn)] at hbound
  have hnorm : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hl : 0 < (lapseSquared m ‖x‖)⁻¹ := inv_pos.mpr (lapseSquared_pos hm hr)
  rw [cartMetric_apply,real_inner_self_eq_norm_sq]
  by_cases hh : ⟪radialUnit x,v⟫_ℝ = 0
  · simp [hh,hnorm]
  · have hp : 0 < (lapseSquared m ‖x‖)⁻¹ * (⟪radialUnit x,v⟫_ℝ)^2 :=
      mul_pos hl (sq_pos_of_ne_zero hh)
    nlinarith

lemma metricInner_smooth {m : ℝ} (hm : 0 < m) :
    ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 (metricInner m)) := by
  intro p
  apply endInner_smoothAt (position_smooth m p)
  apply cartMetric_smoothAt hm
  rw [norm_position hm]
  exact radius_ge m p
lemma metricInner_symm (m : ℝ) (p : Exterior) (v w : TangentSpace I3 p) :
    metricInner m p v w = metricInner m p w v := by
  exact cartMetric_symm m _ _ _
lemma metricInner_pos {m : ℝ} (hm : 0 < m) (p : Exterior) (v : TangentSpace I3 p) (hv : v ≠ 0) :
    0 < metricInner m p v v := by
  change 0 < cartMetric m (position m p) (ambientDerivative (position m) p v)
    (ambientDerivative (position m) p v)
  apply cartMetric_pos hm
  · rw [norm_position hm]; exact radius_ge m p
  · intro h
    apply hv
    exact (position_derivative_injective hm p) (h.trans (map_zero _).symm)

def smoothMetric {m : ℝ} (hm : 0 < m) : SmoothMetric I3 (M := Exterior) where
  inner := metricInner m
  symm := metricInner_symm m
  pos := metricInner_pos hm
  isVonNBounded p := positive_bilinear_bounded (metricInner m p) (metricInner_pos hm p)
  contMDiff := metricInner_smooth hm

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_CutSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle Function
open scoped ContDiff Topology
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N]

variable [@IsManifold ℝ _ E3 _ _ H3
  (@instTopologicalSpaceEuclideanHalfSpace 3 CKSBoundarySurface.halfSpaceDimension_neZero) I3 ∞ N _ _]

instance surfaceCompact (D : OuterDomain N) : CompactSpace (Surface D) := by
  apply isCompact_iff_compactSpace.mp
  exact D.embedding.isEmbedding.isCompact_iff.mpr D.compact_boundary

end CKSFullCutArea

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_TransferDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
namespace CKSMain
universe u v
attribute [local instance] manifold_regular

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

attribute [local instance] CKSBoundarySurface.halfSpaceDimension_neZero
  CKSBoundarySurface.two_atLeastTwo CKSLorentz.hsgNorm CKSLorentz.hsgSpace
  CKSMetricGluing.real_continuousAdd CKSMetricGluing.real_continuousConstSMul
  CKSMetricGluing.real_smulCommClass CKSSpatialManifold.real_id_isometric
  CKSSpatialManifold.covector_smulCommClass CKSLorentz.real_isTopologicalAddGroup
  CKSInducedArea.scalar_smulCommClass CKSInducedArea.scalar_vectorBundle
  CKSInducedArea.scalar_continuousSMul CKSSourceExterior.source_manifold_one
  CKSSchwarzschild.frameCovectorModule

theorem af_tangent_vectorBundle :
    VectorBundle ℝ E3 (fun x : N => TangentSpace I3 x) := inferInstance

attribute [local instance] af_tangent_vectorBundle

theorem af_covector_vectorBundle :
    VectorBundle ℝ (E3 →L[ℝ] ℝ) (fun x : N => TangentSpace I3 x →L[ℝ] ℝ) :=
  inferInstance

attribute [local instance] af_covector_vectorBundle

omit [IsManifold I3 ∞ N] in
theorem af_covector_topologicalAddGroup (point : N) :
    IsTopologicalAddGroup (TangentSpace I3 point →L[ℝ] ℝ) := inferInstance

omit [IsManifold I3 ∞ N] in
theorem af_covector_continuousSMul (point : N) :
    ContinuousSMul ℝ (TangentSpace I3 point →L[ℝ] ℝ) := inferInstance

attribute [local instance] af_covector_topologicalAddGroup af_covector_continuousSMul

attribute [local instance] sixteen_atLeastTwo

end CKSMain

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BoundaryBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology InnerProductSpace
namespace CKSMain
open CKSSchwarzschild
attribute [local instance] manifold_regular
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
attribute [local instance] CKSSpatialManifold.real_id_isometric
  CKSLorentz.real_smulCommClass CKSLorentz.spatialDual_smulCommClass

def schwarzschildAtlas {m : ℝ} (hm : 0 < m) :
    CoefficientAtlas (smoothMetric hm) (tensorInner m) :=
  let atlas : ∀ p, ConstraintChart (metricInner m) (tensorInner m) p := fun p => {
    domain := univ
    coordinate := position m
    metric := cartMetric m
    tensor := cartTensor m
    isOpen := isOpen_univ
    mem := mem_univ p
    smooth := by
      beta_reduce
      exact (position_smooth m).contMDiffOn
    fullRank := by
      beta_reduce
      exact fun _ _ =>
        endInner_fullRank (smoothMetric hm) (position m) (cartMetric m) rfl
    coefficientSmooth := by
      beta_reduce
      exact fun y _ =>
        ⟨cartMetric_smoothAt hm
          (by rw [norm_position hm]; exact radius_ge m y),
         cartTensor_smoothAt hm
          (by rw [norm_position hm]; exact radius_ge m y)⟩
    positiveSymmetric := by
      beta_reduce
      exact fun y _ => ⟨cartMetric_symm m _,
        cartMetric_pos hm
          (by rw [norm_position hm]; exact radius_ge m y),
        cartTensor_symm m _⟩
    represents := by
      exact fun _ _ => ⟨rfl,rfl⟩ }
  atlas

end CKSMain

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCKSAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMixedGeometry CKSAngularSlice
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

def metricPerturbation (m : ℝ) : SpatialTensor := fun x => cartMetric m x - hyperbolicField x
def tensorPerturbation (m : ℝ) : SpatialTensor := fun x => cartTensor m x - hyperbolicField x
def radialCoefficient (m r : ℝ) : ℝ :=
  letI := CKSBoundarySurface.two_atLeastTwo
  (1+r^2-2*m/r)⁻¹-(1+r^2)⁻¹

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCKSDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSMixedGeometry CKSAngularSlice
open scoped ContDiff Topology
namespace CKSSchwarzschild

def compactDenominator (m s : ℝ) : ℝ :=
  letI := CKSBoundarySurface.two_atLeastTwo
  (1+s^2-2*m*s^3)*(1+s^2)
def compactCoefficient (m s : ℝ) : ℝ :=
  letI := CKSBoundarySurface.two_atLeastTwo
  2*m / compactDenominator m s
def compactRemainder (m s : ℝ) : ℝ :=
  letI := CKSBoundarySurface.two_atLeastTwo
  2*m*s*(-2+2*m*s-s^2+2*m*s^3)/compactDenominator m s
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildEnd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSSourceExterior
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
attribute [local instance] CKSMixedGeometry.pointDimension_neZero CKSBoundarySurface.two_atLeastTwo

local instance instFactEqNatFinrankRealE3HAddOfNat_1_r309c4c_1 : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩
def sphereDefault : Sphere := ⟨EuclideanSpace.single 0 1,by simp⟩
def sphereDirection (x : E3) : Sphere :=
  if h : x ≠ 0 then ⟨‖x‖⁻¹ • x, CKSSphericalHarmonics.normalize_mem_sphere x h⟩ else sphereDefault
lemma sphereDirection_val {x : E3} (hx : x ≠ 0) :
    (sphereDirection x).val = ‖x‖⁻¹ • x := by simp [sphereDirection,hx]
lemma sphereDirection_smoothAt {x : E3} (hx : x ≠ 0) :
    ContMDiffAt 𝓘(ℝ,E3) I2 ∞ sphereDirection x := by
  have he : (fun y : CKSSphericalHarmonics.puncturedSpace => sphereDirection y) =
      CKSSphericalHarmonics.normalizeSphere := by
    funext y; apply Subtype.ext; exact sphereDirection_val y.property
  have h := CKSSphericalHarmonics.normalizeSphere_smooth
  rw [← he] at h
  exact contMDiffAt_subtype_iff.mp (h ⟨x,hx⟩)

def positionInverse (m : ℝ) (x : E3) : Exterior :=
  (⟨max 0 (‖x‖-2*m),le_max_left _ _⟩,sphereDirection x)
lemma positionInverse_radius {m : ℝ} {x : E3} (hx : 2*m ≤ ‖x‖) :
    radius m (positionInverse m x) = ‖x‖ := by
  simp only [radius,height,positionInverse,max_eq_right (sub_nonneg.mpr hx)]
  ring
lemma position_left_inverse {m : ℝ} (hm : 0 < m) (p : Exterior) :
    positionInverse m (position m p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [positionInverse,norm_position hm,radius,height,add_sub_cancel_left,
      max_eq_right p.1.property]
  · apply Subtype.ext
    rw [show (positionInverse m (position m p)).2 = sphereDirection (position m p) from rfl,
      sphereDirection_val (norm_ne_zero_iff.mp (ne_of_gt (by rw [norm_position hm]; exact radius_pos hm p))),
      norm_position hm,position,smul_smul,inv_mul_cancel₀ (ne_of_gt (radius_pos hm p)),one_smul]
    rfl
lemma position_right_inverse {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖) :
    position m (positionInverse m x) = x := by
  have hp : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx
  unfold position directionAmbient
  rw [positionInverse_radius hx]
  change ‖x‖ • (sphereDirection x).val = x
  rw [sphereDirection_val (norm_ne_zero_iff.mp hp.ne'),smul_smul,
    mul_inv_cancel₀ hp.ne',one_smul]

lemma pair_smoothAt {f : E3 → Exterior} {x : E3}
    (ht : ContDiffAt ℝ ∞ (fun y => height (f y)) x)
    (hs : ContMDiffAt 𝓘(ℝ,E3) I2 ∞ (fun y => angular (f y)) x) :
    ContMDiffAt 𝓘(ℝ,E3) I3 ∞ f x := by
  rw [contMDiffAt_iff] at hs ⊢
  constructor
  · exact (ht.continuousAt.codRestrict (fun y => (f y).1.property)).prodMk hs.1
  · have hs' : ContDiffAt ℝ ∞ (fun y => chartAt E2 (f x).2 (f y).2) x := by
      simpa only [mfld_simps,chartAt_self_eq,OpenPartialHomeomorph.refl_apply,
        Function.comp_def,contDiffWithinAt_univ,angular] using hs.2
    have h := join.contDiff.contDiffAt.comp x (ht.prodMk hs')
    simp only [mfld_simps,chartAt_self_eq,
      Function.comp_def,contDiffWithinAt_univ]
    change ContDiffAt ℝ ∞ (fun y => join (height (f y),chartAt E2 (f x).2 (f y).2)) x
    exact h

lemma positionInverse_smoothAt {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m < ‖x‖) :
    ContMDiffAt 𝓘(ℝ,E3) I3 ∞ (positionInverse m) x := by
  have hp : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by positivity) hx))
  apply pair_smoothAt
  · have he : (fun y => height (positionInverse m y)) =ᶠ[𝓝 x] (fun y => ‖y‖-2*m) := by
      filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx] with y hy
      exact max_eq_right (sub_nonneg.mpr hy.le)
    exact ((contDiffAt_norm ℝ hp).sub contDiffAt_const).congr_of_eventuallyEq he
  · exact sphereDirection_smoothAt hp

lemma radius_sublevel_compact (m r : ℝ) : IsCompact {p : Exterior | radius m p ≤ r} := by
  have ht : IsCompact {t : Radial | t.val ≤ r-2*m} := by
    rw [Subtype.isCompact_iff]
    convert (isCompact_Icc : IsCompact (Icc 0 (r-2*m))) using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp only [mem_image,mem_ofPred_eq,mem_Icc]
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ⟨a.property,ha⟩
    · rintro ⟨h0,h1⟩; exact ⟨⟨t,h0⟩,h1,rfl⟩
  convert ht.prod (isCompact_univ : IsCompact (univ : Set Sphere)) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [mem_ofPred_eq,mem_prod,mem_univ,and_true,radius,height]
  constructor <;> intro h <;> linarith

def coordinateEnd {m : ℝ} (hm : 0 < m) : CoordinateEnd (N := Exterior) where
  radius := 2*m+1
  radius_pos := by positivity
  domain := {p | 2*m+1 < radius m p}
  isOpen := isOpen_lt continuous_const (radius_smooth m).continuous
  coordinate := position m
  inverse := positionInverse m
  smooth := (position_smooth m).contMDiffOn
  inverse_smooth := fun x hx => (positionInverse_smoothAt hm (by change 2*m+1 < ‖x‖ at hx; linarith)).contMDiffWithinAt
  mapsTo := fun p hp => by rwa [norm_position hm]
  left_inverse := fun p _ => position_left_inverse hm p
  right_inverse := fun x hx => by
    have h := position_right_inverse hm (le_of_lt (by linarith : 2*m < ‖x‖))
    exact ⟨by dsimp; rw [positionInverse_radius (by linarith)]; exact hx,h⟩
  closed_far_side := fun r hr => by
    have he : {p : Exterior | p ∈ {p | 2*m+1 < radius m p} ∧ r ≤ ‖position m p‖} =
        {p | r ≤ radius m p} := by
      ext p; simp only [mem_ofPred_eq,norm_position hm]; constructor
      · exact And.right
      · intro hp; exact ⟨lt_of_lt_of_le hr hp,hp⟩
    rw [he]
    exact isClosed_le continuous_const (radius_smooth m).continuous
  compact_inner_side := fun r hr => by
    have he : {p : Exterior | p ∉ {p | 2*m+1 < radius m p} ∨ ‖position m p‖ ≤ r} =
        {p | radius m p ≤ r} := by
      ext p; simp only [mem_ofPred_eq,norm_position hm,not_lt]
      constructor
      · rintro (h|h); exact h.trans hr.le; exact h
      · exact Or.inr
    rw [he]
    exact radius_sublevel_compact m r
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCKS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMixedGeometry CKSAngularSlice
open CKSSourceExterior
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

theorem four_atLeastTwo : Nat.AtLeastTwo 4 := inferInstance

attribute [local instance] four_atLeastTwo
attribute [local instance] CKSMixedGeometry.pointDimension_neZero CKSBoundarySurface.two_atLeastTwo

lemma cksData_metric_smooth {m : ℝ} (hm : 0 < m) :
    ∀ y, (coordinateEnd hm).radius < ‖y‖ → ContDiffAt ℝ ∞ (metricPerturbation m) y :=
  fun y hy => (cartMetric_smoothAt hm (by change 2*m+1 < ‖y‖ at hy; linarith)).sub
    hyperbolicField_smooth.contDiffAt

lemma cksData_tensor_smooth {m : ℝ} (hm : 0 < m) :
    ∀ y, (coordinateEnd hm).radius < ‖y‖ → ContDiffAt ℝ ∞ (tensorPerturbation m) y :=
  fun y hy => (cartTensor_smoothAt hm (by change 2*m+1 < ‖y‖ at hy; linarith)).sub
    hyperbolicField_smooth.contDiffAt

lemma cksData_represents {m : ℝ} (hm : 0 < m) :
    ∀ p ∈ (coordinateEnd hm).domain,
      (smoothMetric hm).inner p = CKSSpatialManifold.endInner I3 (position m)
        (sourceSpatial (metricPerturbation m)) p ∧
      tensorInner m p = CKSSpatialManifold.endInner I3 (position m)
        (sourceSpatial (tensorPerturbation m)) p := by
  have hM : sourceSpatial (metricPerturbation m) = cartMetric m := by
    funext x
    change hyperbolicField x + (cartMetric m x - hyperbolicField x) = cartMetric m x
    abel
  have hK : sourceSpatial (tensorPerturbation m) = cartTensor m := by
    funext x
    change hyperbolicField x + (cartTensor m x - hyperbolicField x) = cartTensor m x
    abel
  intro p hp
  constructor
  · change metricInner m p = CKSSpatialManifold.endInner I3 (position m)
      (sourceSpatial (metricPerturbation m)) p
    rw [hM]
    rfl
  · rw [hK]
    rfl

lemma cksData_aspect_smooth (m : ℝ) :
    CKSSphericalHarmonics.SmoothSphere (fun _ => 4*m) := contMDiff_const

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphereConeAlgebra
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

def coneLinear (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3) : E3 →L[ℝ] E3 :=
  firstCoordinate.smulRight n + r • A.comp dropPlane
@[simp] lemma coneLinear_apply (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3) (v : E3) :
    coneLinear r n A v = (v 0) • n + r • A (dropPlane v) := rfl

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildIntrinsicHorizonDefinitions
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff
namespace CKSSchwarzschild
open CKSBoundarySurface
universe u
structure IntrinsicInteriorImmersion (m : ℝ) (T : Type u)
    [TopologicalSpace T] [ChartedSpace E2 T] where
  map : T → Exterior
  smooth : ContMDiff I2 I3 ∞ map
  immersion : ∀ p, Function.Injective (mfderiv I2 I3 map p)
  interior : ∀ p, map p ∈ I3.interior Exterior
  normal : ∀ p, TangentSpace I3 (map p)
  normal_unit : ∀ p, metricInner m (map p) (normal p) (normal p) = 1
  normal_orthogonal : ∀ p a, metricInner m (map p) (normal p) (mfderiv I2 I3 map p a) = 0

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_MainProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
namespace CKSMain
universe u v
attribute [local instance] manifold_regular
open CKSSchwarzschild

def InteriorSurface.schwarzschildImmersion {m : ℝ} (hm : 0 < m)
    {T : Type v} [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]
    (D : InteriorSurface (smoothMetric hm) (tensorInner m) (schwarzschildAtlas hm) T) :
    IntrinsicInteriorImmersion m T where
  map := D.map
  smooth := D.smooth
  immersion := D.immersion
  interior := D.interior
  normal := D.normal
  normal_unit := D.normal_unit
  normal_orthogonal := D.normal_orthogonal

end CKSMain

end

end OAI
end


