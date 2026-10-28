-- Prove2me | Definitions.Def_OAIQ079A001
-- name    : OAIQ079A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:36:18.469156+00:00
-- url     : https://prove2.me/theorems/6e6730c1-cc75-4cbb-91ae-cf55669ddbab
-- title:
--   Definitions bundle OAIQ079A001 of the split of OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2501 declarations of OpenAI's Lean: 2498 definitions, 1 inductive type or structure, 1 instance and 1 theorem. The definitions and types are `OAI.CubicTorus.radialFaceNormal`, `OAI.CubicTorus.radialPatchInequalities`, `OAI.CubicTorus.scalarMollification`, `OAI.CubicTorus.scalarMollifier`, `OAI.CubicTorus.scaledTestField`, `OAI.CubicTorus.strictPatchClosed`, `OAI.CubicTorus.strictPatchCutoff`, `OAI.CubicTorus.strictPatchOpen`, `OAI.CubicTorus.stripe`, `OAI.CubicTorus.stripeUpper`, `OAI.CubicTorus.supportedMeasure`, `OAI.CubicTorus.weightedPerimeter`, `OAI.ReusedScalar205.CubicTorus.Arithmetic.Encl`, `OAI.ReusedScalar205.CubicTorus.Arithmetic.asinQuarterArg`, `OAI.ReusedScalar205.CubicTorus.Arithmetic.atanHalf`, `OAI.ReusedScalar205.CubicTorus.Arithmetic.atanPoly`, `OAI.ReusedScalar205.CubicTorus.Nesting.cutoff`, `OAI.ReusedScalar205.CubicTorus.Nesting.ell`, `OAI.ReusedScalar205.CubicTorus.Nesting.lambda`, `OAI.ReusedScalar205.CubicTorus.Nesting.rawWeight`, `OAI.ReusedScalar205.CubicTorus.Nesting.weight`, `OAI.ReusedScalar205.CubicTorus.Reduction.UpperSupport`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e0`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e10`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e100`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1000`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1001`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1002`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1003`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1004`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1005`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1006`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1007`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1008`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1009`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e101`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1010`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1011`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e1012` and 2459 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `CubicTorus_Compactness_BVLocalTranslation`, `CubicTorus_Estimates_CirclePeriodize`, `CubicTorus_Estimates_CoordinatePlaneRays`, `CubicTorus_Profiles_AtanPoly`, `CubicTorus_Profiles_GainBounds`, `CubicTorus_Profiles_ProfileBounds`, `CubicTorus_Profiles_ValueEnclosures1165To1383`, `CubicTorus_Profiles_ValueEnclosures1384To1602`, `CubicTorus_Profiles_ValueEnclosures1603To1821`, `CubicTorus_Profiles_ValueEnclosures1822To2041`, `CubicTorus_Profiles_ValueEnclosures2042To2262`, `CubicTorus_Profiles_ValueEnclosures2263To2479`, `CubicTorus_Profiles_ValueEnclosures2480To2700`, `CubicTorus_Profiles_ValueEnclosures2701To2920`, `CubicTorus_Profiles_ValueEnclosures289To507`, `CubicTorus_Profiles_ValueEnclosures2921To3142`, `CubicTorus_Profiles_ValueEnclosures726To944`, `CubicTorus_Profiles_ValueEnclosures72To288`, `CubicTorus_Profiles_ValueEnclosures945To1164`, `CubicTorus_Reflection_BVScaledFlux`, `CubicTorus_Regularity_BVPlaneAreaCoordinates`, `CubicTorus_Regularity_SmoothApproxLip`, `CubicTorus_Regularity_WeightedPerimeter`.
--
--   **Imports.** It imports the published bundle `Def_CubicTorus`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ079A003`; the proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab`, `OAI.CubicTorus.SmallStandardRegion.bv_data`, `OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small`, `OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous`, `OAI.CubicTorus.planar_radial_both_extents`, `OAI.CubicTorus.planar_radial_isoperimetric`, `OAI.CubicTorus.planar_radial_strip_gain_first` and `OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_sectionLength_corrected`.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_CubicTorus

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

def stripe (V : ℝ) : Set Torus :=
  {x | ((AddCircle.equivIco (1 : ℝ) 0) (x 0) : ℝ) < V}

def stripeUpper (V : ℝ) : Fin 3 → ℝ := Function.update 1 0 V

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_WeightedPerimeter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus
open scoped RealInnerProductSpace

def weightedPerimeter (E : Set Torus) (w : Cover → ℝ) : ℝ≥0∞ :=
  ⨆ (F : Cover → Cover) (_ : AdmissibleField F),
    ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      divergence (fun y ↦ w y • F y) x)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

def supportedMeasure (σ : FiniteMeasure Torus) : Measure (σ : Measure Torus).support :=
  Measure.comap Subtype.val (σ : Measure Torus)

instance supportedMeasure_finite (σ : FiniteMeasure Torus) : IsFiniteMeasure (supportedMeasure σ) :=
  inferInstanceAs (IsFiniteMeasure (Measure.comap _ (σ : Measure Torus)))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def scaledTestField (a : Cover) (r : ℝ) (F : Cover → Cover) (x : Cover) : Cover :=
  r • F (r⁻¹ • (x - a))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlaneAreaCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def radialFaceNormal (u : ℝ) : Cover :=
  WithLp.toLp 2 ![0,1/Real.sqrt (1+u^2),-u/Real.sqrt (1+u^2)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {ι : Type*} [Fintype ι]

def strictPatchOpen (g : ι → Cover → ℝ) : Set Cover := {x | ∀ i, 0 < g i x}
def strictPatchClosed (g : ι → Cover → ℝ) : Set Cover := {x | ∀ i, 0 ≤ g i x}
def strictPatchCutoff (g : ι → Cover → ℝ) (ε : ℝ) (x : Cover) : ℝ :=
  ∏ i, Real.smoothTransition (g i x/ε-1)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def radialPatchInequalities (a c b l u : ℝ) : Fin 6 → Cover → ℝ :=
  ![fun x ↦ x 0-a,fun x ↦ c-x 0,fun x ↦ x 2,fun x ↦ b-x 2,
    fun x ↦ x 1-l*x 2,fun x ↦ u*x 2-x 1]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CirclePeriodize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma real_periodic_deriv {f : ℝ → ℝ} (hp : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro x
  rw [← deriv_comp_add_const]
  exact congrArg (fun g : ℝ → ℝ ↦ deriv g x) (funext hp)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CoordinatePlaneRays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

def scalarMollifier (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1/((n : ℝ)+1)
  rOut := 2/((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

def scalarMollification (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (scalarMollifier n).normed volume ⋆ f

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_AtanPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace ReusedScalar205

noncomputable section

namespace CubicTorus.Arithmetic
open Set Filter
open scoped Topology

def atanPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ↑(2 * i + 1)

def atanHalf (x : ℝ) : ℝ := x / (1 + Real.sqrt (1 + x ^ 2))

def asinQuarterArg (z : ℝ) : ℝ :=
  atanHalf (z / (1 + Real.sqrt (1 - z ^ 2)))

end CubicTorus.Arithmetic

namespace CubicTorus.Arithmetic

def Encl (x l u : ℝ) : Prop := l ≤ x ∧ x ≤ u

end CubicTorus.Arithmetic

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubicTorus.Nesting

def lambda : ℝ := 49 / 50
def ell : ℝ := 7 / 25
def cutoff : ℝ := Real.sqrt 48 / 7
def rawWeight (X : ℝ) : ℝ := (1 - lambda * X ^ 2) / Real.sqrt (1 - X ^ 2)
def weight (X : ℝ) : ℝ := rawWeight (min X cutoff)

end CubicTorus.Nesting

end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

structure UpperSupport (I C : ℝ → ℝ) (x : ℝ) : Prop where
  smooth : ContDiffAt ℝ 2 C x
  contact : C x = I x
  above : ∀ᶠ y in 𝓝 x, I y ≤ C y

end CubicTorus.Reduction

end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_GainBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e0 : ℝ := Real.pi

def e1 : ℝ := (48 : ℝ)

def e2 : ℝ := Real.sqrt e1

def e3 : ℝ := (7 : ℝ)

def e4 : ℝ := e2 / e3

def e5 : ℝ := (1 : ℝ)

def e6 : ℝ := e5 / e0

def e7 : ℝ := e5 - e6

def e8 : ℝ := (49 / 50 : ℝ)

def e9 : ℝ := (7 / 25 : ℝ)

def e10 : ℝ := (21 / 100 : ℝ)

def e11 : ℝ := (16 / 25 : ℝ)

def e12 : ℝ := e11 / e0

def e13 : ℝ := e11 * e7

def e14 : ℝ := e8 * e11

def e15 : ℝ := e14 / e0

def e16 : ℝ := e11 ^ 2

def e17 : ℝ := (4 : ℝ)

def e18 : ℝ := e17 * e16

def e19 : ℝ := e18 / e0

def e20 : ℝ := e5 + e19

def e21 : ℝ := Real.sqrt e20

def e22 : ℝ := e5 + e21

def e23 : ℝ := (2 : ℝ)

def e24 : ℝ := e23 / e22

def e25 : ℝ := e9 * e24

def e26 : ℝ := e15 + e25

def e27 : ℝ := e26 - e5

def e28 : ℝ := e0 / e16

def e29 : ℝ := (2 / 3 : ℝ)

def e30 : ℝ := e12 ^ 2

def e31 : ℝ := e5 - e30

def e32 : ℝ := Real.sqrt e31

def e33 : ℝ := e29 - e32

def e34 : ℝ := e32 ^ 3

def e35 : ℝ := (3 : ℝ)

def e36 : ℝ := e34 / e35

def e37 : ℝ := e33 + e36

def e38 : ℝ := e8 * e37

def e39 : ℝ := e30 / e32

def e40 : ℝ := e39 - e23

def e41 : ℝ := e23 * e32

def e42 : ℝ := e40 + e41

def e43 : ℝ := (50 : ℝ)

def e44 : ℝ := e42 / e43

def e45 : ℝ := e38 - e44

def e46 : ℝ := e28 * e45

def e47 : ℝ := e27 + e46

def e48 : ℝ := e13 ^ 2

def e49 : ℝ := e5 - e48

def e50 : ℝ := Real.sqrt e49

def e58 : ℝ := Real.arcsin e13

def e59 : ℝ := (51 / 100 : ℝ)

def e60 : ℝ := e59 * e58

def e61 : ℝ := (49 / 100 : ℝ)

def e62 : ℝ := e61 * e13

def e63 : ℝ := e62 * e50

def e64 : ℝ := e60 - e63

def e65 : ℝ := e43 * e50

def e66 : ℝ := e13 / e65

def e67 : ℝ := e64 - e66

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures72To288
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e75 : ℝ := Real.arcsin e12

def e76 : ℝ := e59 * e75

def e77 : ℝ := e61 * e12

def e78 : ℝ := e77 * e32

def e79 : ℝ := e76 - e78

def e80 : ℝ := e43 * e32

def e81 : ℝ := e12 / e80

def e82 : ℝ := e79 - e81

def e83 : ℝ := e67 - e82

def e84 : ℝ := e83 / e11

def e85 : ℝ := e47 + e84

def e86 : ℝ := e13 + e4

def e87 : ℝ := e86 / e23

def e88 : ℝ := e13 / e11

def e89 : ℝ := Real.sqrt e0

def e90 : ℝ := e89 * e88

def e91 : ℝ := e0 / e17

def e92 : ℝ := e88 ^ 2

def e93 : ℝ := e91 * e92

def e94 : ℝ := e5 + e93

def e95 : ℝ := Real.sqrt e94

def e96 : ℝ := e90 * e95

def e97 : ℝ := e0 / e23

def e98 : ℝ := e97 * e92

def e99 : ℝ := e96 - e98

def e100 : ℝ := e87 * e99

def e101 : ℝ := e87 / e11

def e102 : ℝ := e89 * e101

def e103 : ℝ := e101 ^ 2

def e104 : ℝ := e91 * e103

def e105 : ℝ := e5 + e104

def e106 : ℝ := Real.sqrt e105

def e107 : ℝ := e102 * e106

def e108 : ℝ := e97 * e103

def e109 : ℝ := e107 - e108

def e110 : ℝ := e13 * e109

def e111 : ℝ := e100 - e110

def e112 : ℝ := e87 ^ 2

def e113 : ℝ := e8 * e112

def e114 : ℝ := e5 - e113

def e115 : ℝ := e5 - e112

def e116 : ℝ := Real.sqrt e115

def e117 : ℝ := e114 / e116

def e118 : ℝ := e5 - e117

def e119 : ℝ := e8 * e48

def e120 : ℝ := e5 - e119

def e121 : ℝ := e120 / e50

def e122 : ℝ := e5 - e121

def e123 : ℝ := e118 - e122

def e124 : ℝ := e111 * e123

def e125 : ℝ := e109 - e99

def e126 : ℝ := e5 + e116

def e127 : ℝ := e87 / e126

def e128 : ℝ := e127 ^ 2

def e129 : ℝ := e5 + e128

def e130 : ℝ := Real.sqrt e129

def e131 : ℝ := e5 + e130

def e132 : ℝ := e127 / e131

def e133 : ℝ := Real.arcsin e87

def e134 : ℝ := e59 * e133

def e135 : ℝ := e61 * e87

def e136 : ℝ := e135 * e116

def e137 : ℝ := e134 - e136

def e138 : ℝ := e43 * e116

def e139 : ℝ := e87 / e138

def e140 : ℝ := e137 - e139

def e141 : ℝ := e140 - e67

def e142 : ℝ := e125 * e141

def e143 : ℝ := e124 + e142

def e144 : ℝ := e87 - e13

def e145 : ℝ := e143 / e144

def e146 : ℝ := e85 + e145

def e147 : ℝ := e4 * e109

def e148 : ℝ := e4 / e11

def e149 : ℝ := e89 * e148

def e150 : ℝ := e148 ^ 2

def e151 : ℝ := e91 * e150

def e152 : ℝ := e5 + e151

def e153 : ℝ := Real.sqrt e152

def e154 : ℝ := e149 * e153

def e155 : ℝ := e97 * e150

def e156 : ℝ := e154 - e155

def e157 : ℝ := e87 * e156

def e158 : ℝ := e147 - e157

def e159 : ℝ := e4 ^ 2

def e160 : ℝ := e8 * e159

def e161 : ℝ := e5 - e160

def e162 : ℝ := e5 - e159

def e163 : ℝ := Real.sqrt e162

def e164 : ℝ := e161 / e163

def e165 : ℝ := e5 - e164

def e166 : ℝ := e165 - e118

def e167 : ℝ := e158 * e166

def e168 : ℝ := e156 - e109

def e169 : ℝ := e5 + e163

def e170 : ℝ := e4 / e169

def e171 : ℝ := e170 ^ 2

def e172 : ℝ := e5 + e171

def e173 : ℝ := Real.sqrt e172

def e174 : ℝ := e5 + e173

def e175 : ℝ := e170 / e174

def e176 : ℝ := Real.arcsin e4

def e177 : ℝ := e59 * e176

def e178 : ℝ := e61 * e4

def e179 : ℝ := e178 * e163

def e180 : ℝ := e177 - e179

def e181 : ℝ := e43 * e163

def e182 : ℝ := e4 / e181

def e183 : ℝ := e180 - e182

def e184 : ℝ := e183 - e140

def e185 : ℝ := e168 * e184

def e186 : ℝ := e167 + e185

def e187 : ℝ := e4 - e87

def e188 : ℝ := e186 / e187

def e189 : ℝ := e146 + e188

def e190 : ℝ := (37 / 50 : ℝ)

def e191 : ℝ := e190 / e0

def e192 : ℝ := e190 * e7

def e193 : ℝ := e8 * e190

def e194 : ℝ := e193 / e0

def e195 : ℝ := e190 ^ 2

def e196 : ℝ := e17 * e195

def e197 : ℝ := e196 / e0

def e198 : ℝ := e5 + e197

def e199 : ℝ := Real.sqrt e198

def e200 : ℝ := e5 + e199

def e201 : ℝ := e23 / e200

def e202 : ℝ := e9 * e201

def e203 : ℝ := e194 + e202

def e204 : ℝ := e203 - e5

def e205 : ℝ := e0 / e195

def e206 : ℝ := e191 ^ 2

def e207 : ℝ := e5 - e206

def e208 : ℝ := Real.sqrt e207

def e209 : ℝ := e29 - e208

def e210 : ℝ := e208 ^ 3

def e211 : ℝ := e210 / e35

def e212 : ℝ := e209 + e211

def e213 : ℝ := e8 * e212

def e214 : ℝ := e206 / e208

def e215 : ℝ := e214 - e23

def e216 : ℝ := e23 * e208

def e217 : ℝ := e215 + e216

def e218 : ℝ := e217 / e43

def e219 : ℝ := e213 - e218

def e220 : ℝ := e205 * e219

def e221 : ℝ := e204 + e220

def e222 : ℝ := e192 ^ 2

def e223 : ℝ := e5 - e222

def e224 : ℝ := Real.sqrt e223

def e225 : ℝ := e5 + e224

def e226 : ℝ := e192 / e225

def e227 : ℝ := e226 ^ 2

def e228 : ℝ := e5 + e227

def e229 : ℝ := Real.sqrt e228

def e230 : ℝ := e5 + e229

def e231 : ℝ := e226 / e230

def e232 : ℝ := Real.arcsin e192

def e233 : ℝ := e59 * e232

def e234 : ℝ := e61 * e192

def e235 : ℝ := e234 * e224

def e236 : ℝ := e233 - e235

def e237 : ℝ := e43 * e224

def e238 : ℝ := e192 / e237

def e239 : ℝ := e236 - e238

def e240 : ℝ := e5 + e208

def e241 : ℝ := e191 / e240

def e242 : ℝ := e241 ^ 2

def e243 : ℝ := e5 + e242

def e244 : ℝ := Real.sqrt e243

def e245 : ℝ := e5 + e244

def e246 : ℝ := e241 / e245

def e247 : ℝ := Real.arcsin e191

def e248 : ℝ := e59 * e247

def e249 : ℝ := e61 * e191

def e250 : ℝ := e249 * e208

def e251 : ℝ := e248 - e250

def e252 : ℝ := e43 * e208

def e253 : ℝ := e191 / e252

def e254 : ℝ := e251 - e253

def e255 : ℝ := e239 - e254

def e256 : ℝ := e255 / e190

def e257 : ℝ := e221 + e256

def e258 : ℝ := e192 + e4

def e259 : ℝ := e258 / e23

def e260 : ℝ := e192 / e190

def e261 : ℝ := e89 * e260

def e262 : ℝ := e260 ^ 2

def e263 : ℝ := e91 * e262

def e264 : ℝ := e5 + e263

def e265 : ℝ := Real.sqrt e264

def e266 : ℝ := e261 * e265

def e267 : ℝ := e97 * e262

def e268 : ℝ := e266 - e267

def e269 : ℝ := e259 * e268

def e270 : ℝ := e259 / e190

def e271 : ℝ := e89 * e270

def e272 : ℝ := e270 ^ 2

def e273 : ℝ := e91 * e272

def e274 : ℝ := e5 + e273

def e275 : ℝ := Real.sqrt e274

def e276 : ℝ := e271 * e275

def e277 : ℝ := e97 * e272

def e278 : ℝ := e276 - e277

def e279 : ℝ := e192 * e278

def e280 : ℝ := e269 - e279

def e281 : ℝ := e259 ^ 2

def e282 : ℝ := e8 * e281

def e283 : ℝ := e5 - e282

def e284 : ℝ := e5 - e281

def e285 : ℝ := Real.sqrt e284

def e286 : ℝ := e283 / e285

def e287 : ℝ := e5 - e286

def e288 : ℝ := e8 * e222

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures289To507
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e289 : ℝ := e5 - e288

def e290 : ℝ := e289 / e224

def e291 : ℝ := e5 - e290

def e292 : ℝ := e287 - e291

def e293 : ℝ := e280 * e292

def e294 : ℝ := e278 - e268

def e295 : ℝ := e5 + e285

def e296 : ℝ := e259 / e295

def e297 : ℝ := e296 ^ 2

def e298 : ℝ := e5 + e297

def e299 : ℝ := Real.sqrt e298

def e300 : ℝ := e5 + e299

def e301 : ℝ := e296 / e300

def e302 : ℝ := Real.arcsin e259

def e303 : ℝ := e59 * e302

def e304 : ℝ := e61 * e259

def e305 : ℝ := e304 * e285

def e306 : ℝ := e303 - e305

def e307 : ℝ := e43 * e285

def e308 : ℝ := e259 / e307

def e309 : ℝ := e306 - e308

def e310 : ℝ := e309 - e239

def e311 : ℝ := e294 * e310

def e312 : ℝ := e293 + e311

def e313 : ℝ := e259 - e192

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures726To944
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e757 : ℝ := e4 / e8

def e924 : ℝ := (24 / 25 : ℝ)

def e932 : ℝ := e23 / e0

def e939 : ℝ := (67 / 500 : ℝ)

def e941 : ℝ := (9 / 25 : ℝ)

def e944 : ℝ := (6 : ℝ)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures945To1164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e954 : ℝ := e10 ^ 3

def e964 : ℝ := (53 / 50 : ℝ)

def e965 : ℝ := e964 / e0

def e966 : ℝ := e964 * e7

def e967 : ℝ := e8 * e964

def e968 : ℝ := e967 / e0

def e969 : ℝ := e964 ^ 2

def e970 : ℝ := e17 * e969

def e971 : ℝ := e970 / e0

def e972 : ℝ := e5 + e971

def e973 : ℝ := Real.sqrt e972

def e974 : ℝ := e5 + e973

def e975 : ℝ := e23 / e974

def e976 : ℝ := e9 * e975

def e977 : ℝ := e968 + e976

def e978 : ℝ := e977 - e5

def e979 : ℝ := e0 / e969

def e980 : ℝ := e965 ^ 2

def e981 : ℝ := e5 - e980

def e982 : ℝ := Real.sqrt e981

def e983 : ℝ := e29 - e982

def e984 : ℝ := e982 ^ 3

def e985 : ℝ := e984 / e35

def e986 : ℝ := e983 + e985

def e987 : ℝ := e8 * e986

def e988 : ℝ := e980 / e982

def e989 : ℝ := e988 - e23

def e990 : ℝ := e23 * e982

def e991 : ℝ := e989 + e990

def e992 : ℝ := e991 / e43

def e993 : ℝ := e987 - e992

def e994 : ℝ := e979 * e993

def e995 : ℝ := e978 + e994

def e996 : ℝ := e966 ^ 2

def e997 : ℝ := e5 - e996

def e998 : ℝ := Real.sqrt e997

def e999 : ℝ := e5 + e998

def e1000 : ℝ := e966 / e999

def e1001 : ℝ := e1000 ^ 2

def e1002 : ℝ := e5 + e1001

def e1003 : ℝ := Real.sqrt e1002

def e1004 : ℝ := e5 + e1003

def e1005 : ℝ := e1000 / e1004

def e1006 : ℝ := Real.arcsin e966

def e1007 : ℝ := e59 * e1006

def e1008 : ℝ := e61 * e966

def e1009 : ℝ := e1008 * e998

def e1010 : ℝ := e1007 - e1009

def e1011 : ℝ := e43 * e998

def e1012 : ℝ := e966 / e1011

def e1013 : ℝ := e1010 - e1012

def e1014 : ℝ := e5 + e982

def e1015 : ℝ := e965 / e1014

def e1016 : ℝ := e1015 ^ 2

def e1017 : ℝ := e5 + e1016

def e1018 : ℝ := Real.sqrt e1017

def e1019 : ℝ := e5 + e1018

def e1020 : ℝ := e1015 / e1019

def e1021 : ℝ := Real.arcsin e965

def e1022 : ℝ := e59 * e1021

def e1023 : ℝ := e61 * e965

def e1024 : ℝ := e1023 * e982

def e1025 : ℝ := e1022 - e1024

def e1026 : ℝ := e43 * e982

def e1027 : ℝ := e965 / e1026

def e1028 : ℝ := e1025 - e1027

def e1029 : ℝ := e1013 - e1028

def e1030 : ℝ := e1029 / e964

def e1031 : ℝ := e995 + e1030

def e1032 : ℝ := e966 + e4

def e1033 : ℝ := e1032 / e23

def e1034 : ℝ := e966 / e964

def e1035 : ℝ := e89 * e1034

def e1036 : ℝ := e1034 ^ 2

def e1037 : ℝ := e91 * e1036

def e1038 : ℝ := e5 + e1037

def e1039 : ℝ := Real.sqrt e1038

def e1040 : ℝ := e1035 * e1039

def e1041 : ℝ := e97 * e1036

def e1042 : ℝ := e1040 - e1041

def e1043 : ℝ := e1033 * e1042

def e1044 : ℝ := e1033 / e964

def e1045 : ℝ := e89 * e1044

def e1046 : ℝ := e1044 ^ 2

def e1047 : ℝ := e91 * e1046

def e1048 : ℝ := e5 + e1047

def e1049 : ℝ := Real.sqrt e1048

def e1050 : ℝ := e1045 * e1049

def e1051 : ℝ := e97 * e1046

def e1052 : ℝ := e1050 - e1051

def e1053 : ℝ := e966 * e1052

def e1054 : ℝ := e1043 - e1053

def e1055 : ℝ := e1033 ^ 2

def e1056 : ℝ := e8 * e1055

def e1057 : ℝ := e5 - e1056

def e1058 : ℝ := e5 - e1055

def e1059 : ℝ := Real.sqrt e1058

def e1060 : ℝ := e1057 / e1059

def e1061 : ℝ := e5 - e1060

def e1062 : ℝ := e8 * e996

def e1063 : ℝ := e5 - e1062

def e1064 : ℝ := e1063 / e998

def e1065 : ℝ := e5 - e1064

def e1066 : ℝ := e1061 - e1065

def e1067 : ℝ := e1054 * e1066

def e1068 : ℝ := e1052 - e1042

def e1069 : ℝ := e5 + e1059

def e1070 : ℝ := e1033 / e1069

def e1071 : ℝ := e1070 ^ 2

def e1072 : ℝ := e5 + e1071

def e1073 : ℝ := Real.sqrt e1072

def e1074 : ℝ := e5 + e1073

def e1075 : ℝ := e1070 / e1074

def e1076 : ℝ := Real.arcsin e1033

def e1077 : ℝ := e59 * e1076

def e1078 : ℝ := e61 * e1033

def e1079 : ℝ := e1078 * e1059

def e1080 : ℝ := e1077 - e1079

def e1081 : ℝ := e43 * e1059

def e1082 : ℝ := e1033 / e1081

def e1083 : ℝ := e1080 - e1082

def e1084 : ℝ := e1083 - e1013

def e1085 : ℝ := e1068 * e1084

def e1086 : ℝ := e1067 + e1085

def e1087 : ℝ := e1033 - e966

def e1088 : ℝ := e1086 / e1087

def e1089 : ℝ := e1031 + e1088

def e1090 : ℝ := e4 * e1052

def e1091 : ℝ := e4 / e964

def e1092 : ℝ := e89 * e1091

def e1093 : ℝ := e1091 ^ 2

def e1094 : ℝ := e91 * e1093

def e1095 : ℝ := e5 + e1094

def e1096 : ℝ := Real.sqrt e1095

def e1097 : ℝ := e1092 * e1096

def e1098 : ℝ := e97 * e1093

def e1099 : ℝ := e1097 - e1098

def e1100 : ℝ := e1033 * e1099

def e1101 : ℝ := e1090 - e1100

def e1102 : ℝ := e165 - e1061

def e1103 : ℝ := e1101 * e1102

def e1104 : ℝ := e1099 - e1052

def e1105 : ℝ := e183 - e1083

def e1106 : ℝ := e1104 * e1105

def e1107 : ℝ := e1103 + e1106

def e1108 : ℝ := e4 - e1033

def e1109 : ℝ := e1107 / e1108

def e1110 : ℝ := e1089 + e1109

def e1111 : ℝ := e924 / e964

def e1112 : ℝ := min e7 e1111

def e1113 : ℝ := e1112 - e5

def e1114 : ℝ := e23 * e964

def e1115 : ℝ := e1114 * e975

def e1116 : ℝ := e1115 / e0

def e1117 : ℝ := e1113 + e1116

def e1118 : ℝ := e23 * e969

def e1119 : ℝ := e1118 * e975

def e1120 : ℝ := e0 + e1119

def e1121 : ℝ := Real.sqrt e1120

def e1122 : ℝ := e932 * e1121

def e1123 : ℝ := e964 ^ 3

def e1124 : ℝ := e939 * e1123

def e1125 : ℝ := min e1124 e941

def e1126 : ℝ := e23 * e1117

def e1127 : ℝ := e944 * e1125

def e1128 : ℝ := e1122 ^ 2

def e1129 : ℝ := e1127 * e1128

def e1130 : ℝ := e1129 * e1117

def e1131 : ℝ := e1130 / e9

def e1132 : ℝ := e5 + e1131

def e1133 : ℝ := Real.sqrt e1132

def e1134 : ℝ := e5 + e1133

def e1135 : ℝ := e1126 / e1134

def e1136 : ℝ := e1125 * e954

def e1137 : ℝ := e1117 - e1135

def e1138 : ℝ := e1137 / e1122

def e1139 : ℝ := e1138 ^ 2

def e1140 : ℝ := e9 * e1139

def e1141 : ℝ := e1135 ^ 3

def e1142 : ℝ := e1125 * e1141

def e1143 : ℝ := e1140 + e1142

def e1144 : ℝ := min e1136 e1143

def e1145 : ℝ := (11 / 10 : ℝ)

def e1146 : ℝ := e1145 / e0

def e1147 : ℝ := e1145 * e7

def e1148 : ℝ := e8 * e1145

def e1149 : ℝ := e1148 / e0

def e1150 : ℝ := e1145 ^ 2

def e1151 : ℝ := e17 * e1150

def e1152 : ℝ := e1151 / e0

def e1153 : ℝ := e5 + e1152

def e1154 : ℝ := Real.sqrt e1153

def e1155 : ℝ := e5 + e1154

def e1156 : ℝ := e23 / e1155

def e1157 : ℝ := e9 * e1156

def e1158 : ℝ := e1149 + e1157

def e1159 : ℝ := e1158 - e5

def e1160 : ℝ := e0 / e1150

def e1161 : ℝ := e1146 ^ 2

def e1162 : ℝ := e5 - e1161

def e1163 : ℝ := Real.sqrt e1162

def e1164 : ℝ := e29 - e1163

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures1165To1383
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e1165 : ℝ := e1163 ^ 3

def e1166 : ℝ := e1165 / e35

def e1167 : ℝ := e1164 + e1166

def e1168 : ℝ := e8 * e1167

def e1169 : ℝ := e1161 / e1163

def e1170 : ℝ := e1169 - e23

def e1171 : ℝ := e23 * e1163

def e1172 : ℝ := e1170 + e1171

def e1173 : ℝ := e1172 / e43

def e1174 : ℝ := e1168 - e1173

def e1175 : ℝ := e1160 * e1174

def e1176 : ℝ := e1159 + e1175

def e1177 : ℝ := e1147 ^ 2

def e1178 : ℝ := e5 - e1177

def e1179 : ℝ := Real.sqrt e1178

def e1180 : ℝ := e5 + e1179

def e1181 : ℝ := e1147 / e1180

def e1182 : ℝ := e1181 ^ 2

def e1183 : ℝ := e5 + e1182

def e1184 : ℝ := Real.sqrt e1183

def e1185 : ℝ := e5 + e1184

def e1186 : ℝ := e1181 / e1185

def e1187 : ℝ := Real.arcsin e1147

def e1188 : ℝ := e59 * e1187

def e1189 : ℝ := e61 * e1147

def e1190 : ℝ := e1189 * e1179

def e1191 : ℝ := e1188 - e1190

def e1192 : ℝ := e43 * e1179

def e1193 : ℝ := e1147 / e1192

def e1194 : ℝ := e1191 - e1193

def e1195 : ℝ := e5 + e1163

def e1196 : ℝ := e1146 / e1195

def e1197 : ℝ := e1196 ^ 2

def e1198 : ℝ := e5 + e1197

def e1199 : ℝ := Real.sqrt e1198

def e1200 : ℝ := e5 + e1199

def e1201 : ℝ := e1196 / e1200

def e1202 : ℝ := Real.arcsin e1146

def e1203 : ℝ := e59 * e1202

def e1204 : ℝ := e61 * e1146

def e1205 : ℝ := e1204 * e1163

def e1206 : ℝ := e1203 - e1205

def e1207 : ℝ := e43 * e1163

def e1208 : ℝ := e1146 / e1207

def e1209 : ℝ := e1206 - e1208

def e1210 : ℝ := e1194 - e1209

def e1211 : ℝ := e1210 / e1145

def e1212 : ℝ := e1176 + e1211

def e1213 : ℝ := e1147 + e4

def e1214 : ℝ := e1213 / e23

def e1215 : ℝ := e1147 / e1145

def e1216 : ℝ := e89 * e1215

def e1217 : ℝ := e1215 ^ 2

def e1218 : ℝ := e91 * e1217

def e1219 : ℝ := e5 + e1218

def e1220 : ℝ := Real.sqrt e1219

def e1221 : ℝ := e1216 * e1220

def e1222 : ℝ := e97 * e1217

def e1223 : ℝ := e1221 - e1222

def e1224 : ℝ := e1214 * e1223

def e1225 : ℝ := e1214 / e1145

def e1226 : ℝ := e89 * e1225

def e1227 : ℝ := e1225 ^ 2

def e1228 : ℝ := e91 * e1227

def e1229 : ℝ := e5 + e1228

def e1230 : ℝ := Real.sqrt e1229

def e1231 : ℝ := e1226 * e1230

def e1232 : ℝ := e97 * e1227

def e1233 : ℝ := e1231 - e1232

def e1234 : ℝ := e1147 * e1233

def e1235 : ℝ := e1224 - e1234

def e1236 : ℝ := e1214 ^ 2

def e1237 : ℝ := e8 * e1236

def e1238 : ℝ := e5 - e1237

def e1239 : ℝ := e5 - e1236

def e1240 : ℝ := Real.sqrt e1239

def e1241 : ℝ := e1238 / e1240

def e1242 : ℝ := e5 - e1241

def e1243 : ℝ := e8 * e1177

def e1244 : ℝ := e5 - e1243

def e1245 : ℝ := e1244 / e1179

def e1246 : ℝ := e5 - e1245

def e1247 : ℝ := e1242 - e1246

def e1248 : ℝ := e1235 * e1247

def e1249 : ℝ := e1233 - e1223

def e1250 : ℝ := e5 + e1240

def e1251 : ℝ := e1214 / e1250

def e1252 : ℝ := e1251 ^ 2

def e1253 : ℝ := e5 + e1252

def e1254 : ℝ := Real.sqrt e1253

def e1255 : ℝ := e5 + e1254

def e1256 : ℝ := e1251 / e1255

def e1257 : ℝ := Real.arcsin e1214

def e1258 : ℝ := e59 * e1257

def e1259 : ℝ := e61 * e1214

def e1260 : ℝ := e1259 * e1240

def e1261 : ℝ := e1258 - e1260

def e1262 : ℝ := e43 * e1240

def e1263 : ℝ := e1214 / e1262

def e1264 : ℝ := e1261 - e1263

def e1265 : ℝ := e1264 - e1194

def e1266 : ℝ := e1249 * e1265

def e1267 : ℝ := e1248 + e1266

def e1268 : ℝ := e1214 - e1147

def e1269 : ℝ := e1267 / e1268

def e1270 : ℝ := e1212 + e1269

def e1271 : ℝ := e4 * e1233

def e1272 : ℝ := e4 / e1145

def e1273 : ℝ := e89 * e1272

def e1274 : ℝ := e1272 ^ 2

def e1275 : ℝ := e91 * e1274

def e1276 : ℝ := e5 + e1275

def e1277 : ℝ := Real.sqrt e1276

def e1278 : ℝ := e1273 * e1277

def e1279 : ℝ := e97 * e1274

def e1280 : ℝ := e1278 - e1279

def e1281 : ℝ := e1214 * e1280

def e1282 : ℝ := e1271 - e1281

def e1283 : ℝ := e165 - e1242

def e1284 : ℝ := e1282 * e1283

def e1285 : ℝ := e1280 - e1233

def e1286 : ℝ := e183 - e1264

def e1287 : ℝ := e1285 * e1286

def e1288 : ℝ := e1284 + e1287

def e1289 : ℝ := e4 - e1214

def e1290 : ℝ := e1288 / e1289

def e1291 : ℝ := e1270 + e1290

def e1292 : ℝ := e924 / e1145

def e1293 : ℝ := min e7 e1292

def e1294 : ℝ := e1293 - e5

def e1295 : ℝ := e23 * e1145

def e1296 : ℝ := e1295 * e1156

def e1297 : ℝ := e1296 / e0

def e1298 : ℝ := e1294 + e1297

def e1299 : ℝ := e23 * e1150

def e1300 : ℝ := e1299 * e1156

def e1301 : ℝ := e0 + e1300

def e1302 : ℝ := Real.sqrt e1301

def e1303 : ℝ := e932 * e1302

def e1304 : ℝ := e1145 ^ 3

def e1305 : ℝ := e939 * e1304

def e1306 : ℝ := min e1305 e941

def e1307 : ℝ := e23 * e1298

def e1308 : ℝ := e944 * e1306

def e1309 : ℝ := e1303 ^ 2

def e1310 : ℝ := e1308 * e1309

def e1311 : ℝ := e1310 * e1298

def e1312 : ℝ := e1311 / e9

def e1313 : ℝ := e5 + e1312

def e1314 : ℝ := Real.sqrt e1313

def e1315 : ℝ := e5 + e1314

def e1316 : ℝ := e1307 / e1315

def e1317 : ℝ := e1306 * e954

def e1318 : ℝ := e1298 - e1316

def e1319 : ℝ := e1318 / e1303

def e1320 : ℝ := e1319 ^ 2

def e1321 : ℝ := e9 * e1320

def e1322 : ℝ := e1316 ^ 3

def e1323 : ℝ := e1306 * e1322

def e1324 : ℝ := e1321 + e1323

def e1325 : ℝ := min e1317 e1324

def e1326 : ℝ := (57 / 50 : ℝ)

def e1327 : ℝ := e1326 / e0

def e1328 : ℝ := e1326 * e7

def e1329 : ℝ := e8 * e1326

def e1330 : ℝ := e1329 / e0

def e1331 : ℝ := e1326 ^ 2

def e1332 : ℝ := e17 * e1331

def e1333 : ℝ := e1332 / e0

def e1334 : ℝ := e5 + e1333

def e1335 : ℝ := Real.sqrt e1334

def e1336 : ℝ := e5 + e1335

def e1337 : ℝ := e23 / e1336

def e1338 : ℝ := e9 * e1337

def e1339 : ℝ := e1330 + e1338

def e1340 : ℝ := e1339 - e5

def e1341 : ℝ := e0 / e1331

def e1342 : ℝ := e1327 ^ 2

def e1343 : ℝ := e5 - e1342

def e1344 : ℝ := Real.sqrt e1343

def e1345 : ℝ := e29 - e1344

def e1346 : ℝ := e1344 ^ 3

def e1347 : ℝ := e1346 / e35

def e1348 : ℝ := e1345 + e1347

def e1349 : ℝ := e8 * e1348

def e1350 : ℝ := e1342 / e1344

def e1351 : ℝ := e1350 - e23

def e1352 : ℝ := e23 * e1344

def e1353 : ℝ := e1351 + e1352

def e1354 : ℝ := e1353 / e43

def e1355 : ℝ := e1349 - e1354

def e1356 : ℝ := e1341 * e1355

def e1357 : ℝ := e1340 + e1356

def e1358 : ℝ := e1328 ^ 2

def e1359 : ℝ := e5 - e1358

def e1360 : ℝ := Real.sqrt e1359

def e1361 : ℝ := e5 + e1360

def e1362 : ℝ := e1328 / e1361

def e1363 : ℝ := e1362 ^ 2

def e1364 : ℝ := e5 + e1363

def e1365 : ℝ := Real.sqrt e1364

def e1366 : ℝ := e5 + e1365

def e1367 : ℝ := e1362 / e1366

def e1368 : ℝ := Real.arcsin e1328

def e1369 : ℝ := e59 * e1368

def e1370 : ℝ := e61 * e1328

def e1371 : ℝ := e1370 * e1360

def e1372 : ℝ := e1369 - e1371

def e1373 : ℝ := e43 * e1360

def e1374 : ℝ := e1328 / e1373

def e1375 : ℝ := e1372 - e1374

def e1376 : ℝ := e5 + e1344

def e1377 : ℝ := e1327 / e1376

def e1378 : ℝ := e1377 ^ 2

def e1379 : ℝ := e5 + e1378

def e1380 : ℝ := Real.sqrt e1379

def e1381 : ℝ := e5 + e1380

def e1382 : ℝ := e1377 / e1381

def e1383 : ℝ := Real.arcsin e1327

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures1384To1602
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e1384 : ℝ := e59 * e1383

def e1385 : ℝ := e61 * e1327

def e1386 : ℝ := e1385 * e1344

def e1387 : ℝ := e1384 - e1386

def e1388 : ℝ := e43 * e1344

def e1389 : ℝ := e1327 / e1388

def e1390 : ℝ := e1387 - e1389

def e1391 : ℝ := e1375 - e1390

def e1392 : ℝ := e1391 / e1326

def e1393 : ℝ := e1357 + e1392

def e1394 : ℝ := e1328 + e4

def e1395 : ℝ := e1394 / e23

def e1396 : ℝ := e1328 / e1326

def e1397 : ℝ := e89 * e1396

def e1398 : ℝ := e1396 ^ 2

def e1399 : ℝ := e91 * e1398

def e1400 : ℝ := e5 + e1399

def e1401 : ℝ := Real.sqrt e1400

def e1402 : ℝ := e1397 * e1401

def e1403 : ℝ := e97 * e1398

def e1404 : ℝ := e1402 - e1403

def e1405 : ℝ := e1395 * e1404

def e1406 : ℝ := e1395 / e1326

def e1407 : ℝ := e89 * e1406

def e1408 : ℝ := e1406 ^ 2

def e1409 : ℝ := e91 * e1408

def e1410 : ℝ := e5 + e1409

def e1411 : ℝ := Real.sqrt e1410

def e1412 : ℝ := e1407 * e1411

def e1413 : ℝ := e97 * e1408

def e1414 : ℝ := e1412 - e1413

def e1415 : ℝ := e1328 * e1414

def e1416 : ℝ := e1405 - e1415

def e1417 : ℝ := e1395 ^ 2

def e1418 : ℝ := e8 * e1417

def e1419 : ℝ := e5 - e1418

def e1420 : ℝ := e5 - e1417

def e1421 : ℝ := Real.sqrt e1420

def e1422 : ℝ := e1419 / e1421

def e1423 : ℝ := e5 - e1422

def e1424 : ℝ := e8 * e1358

def e1425 : ℝ := e5 - e1424

def e1426 : ℝ := e1425 / e1360

def e1427 : ℝ := e5 - e1426

def e1428 : ℝ := e1423 - e1427

def e1429 : ℝ := e1416 * e1428

def e1430 : ℝ := e1414 - e1404

def e1431 : ℝ := e5 + e1421

def e1432 : ℝ := e1395 / e1431

def e1433 : ℝ := e1432 ^ 2

def e1434 : ℝ := e5 + e1433

def e1435 : ℝ := Real.sqrt e1434

def e1436 : ℝ := e5 + e1435

def e1437 : ℝ := e1432 / e1436

def e1438 : ℝ := Real.arcsin e1395

def e1439 : ℝ := e59 * e1438

def e1440 : ℝ := e61 * e1395

def e1441 : ℝ := e1440 * e1421

def e1442 : ℝ := e1439 - e1441

def e1443 : ℝ := e43 * e1421

def e1444 : ℝ := e1395 / e1443

def e1445 : ℝ := e1442 - e1444

def e1446 : ℝ := e1445 - e1375

def e1447 : ℝ := e1430 * e1446

def e1448 : ℝ := e1429 + e1447

def e1449 : ℝ := e1395 - e1328

def e1450 : ℝ := e1448 / e1449

def e1451 : ℝ := e1393 + e1450

def e1452 : ℝ := e4 * e1414

def e1453 : ℝ := e4 / e1326

def e1454 : ℝ := e89 * e1453

def e1455 : ℝ := e1453 ^ 2

def e1456 : ℝ := e91 * e1455

def e1457 : ℝ := e5 + e1456

def e1458 : ℝ := Real.sqrt e1457

def e1459 : ℝ := e1454 * e1458

def e1460 : ℝ := e97 * e1455

def e1461 : ℝ := e1459 - e1460

def e1462 : ℝ := e1395 * e1461

def e1463 : ℝ := e1452 - e1462

def e1464 : ℝ := e165 - e1423

def e1465 : ℝ := e1463 * e1464

def e1466 : ℝ := e1461 - e1414

def e1467 : ℝ := e183 - e1445

def e1468 : ℝ := e1466 * e1467

def e1469 : ℝ := e1465 + e1468

def e1470 : ℝ := e4 - e1395

def e1471 : ℝ := e1469 / e1470

def e1472 : ℝ := e1451 + e1471

def e1473 : ℝ := e924 / e1326

def e1474 : ℝ := min e7 e1473

def e1475 : ℝ := e1474 - e5

def e1476 : ℝ := e23 * e1326

def e1477 : ℝ := e1476 * e1337

def e1478 : ℝ := e1477 / e0

def e1479 : ℝ := e1475 + e1478

def e1480 : ℝ := e23 * e1331

def e1481 : ℝ := e1480 * e1337

def e1482 : ℝ := e0 + e1481

def e1483 : ℝ := Real.sqrt e1482

def e1484 : ℝ := e932 * e1483

def e1485 : ℝ := e1326 ^ 3

def e1486 : ℝ := e939 * e1485

def e1487 : ℝ := min e1486 e941

def e1488 : ℝ := e23 * e1479

def e1489 : ℝ := e944 * e1487

def e1490 : ℝ := e1484 ^ 2

def e1491 : ℝ := e1489 * e1490

def e1492 : ℝ := e1491 * e1479

def e1493 : ℝ := e1492 / e9

def e1494 : ℝ := e5 + e1493

def e1495 : ℝ := Real.sqrt e1494

def e1496 : ℝ := e5 + e1495

def e1497 : ℝ := e1488 / e1496

def e1498 : ℝ := e1487 * e954

def e1499 : ℝ := e1479 - e1497

def e1500 : ℝ := e1499 / e1484

def e1501 : ℝ := e1500 ^ 2

def e1502 : ℝ := e9 * e1501

def e1503 : ℝ := e1497 ^ 3

def e1504 : ℝ := e1487 * e1503

def e1505 : ℝ := e1502 + e1504

def e1506 : ℝ := min e1498 e1505

def e1507 : ℝ := (59 / 50 : ℝ)

def e1508 : ℝ := e1507 / e0

def e1509 : ℝ := e1507 * e7

def e1510 : ℝ := e8 * e1507

def e1511 : ℝ := e1510 / e0

def e1512 : ℝ := e1507 ^ 2

def e1513 : ℝ := e17 * e1512

def e1514 : ℝ := e1513 / e0

def e1515 : ℝ := e5 + e1514

def e1516 : ℝ := Real.sqrt e1515

def e1517 : ℝ := e5 + e1516

def e1518 : ℝ := e23 / e1517

def e1519 : ℝ := e9 * e1518

def e1520 : ℝ := e1511 + e1519

def e1521 : ℝ := e1520 - e5

def e1522 : ℝ := e0 / e1512

def e1523 : ℝ := e1508 ^ 2

def e1524 : ℝ := e5 - e1523

def e1525 : ℝ := Real.sqrt e1524

def e1526 : ℝ := e29 - e1525

def e1527 : ℝ := e1525 ^ 3

def e1528 : ℝ := e1527 / e35

def e1529 : ℝ := e1526 + e1528

def e1530 : ℝ := e8 * e1529

def e1531 : ℝ := e1523 / e1525

def e1532 : ℝ := e1531 - e23

def e1533 : ℝ := e23 * e1525

def e1534 : ℝ := e1532 + e1533

def e1535 : ℝ := e1534 / e43

def e1536 : ℝ := e1530 - e1535

def e1537 : ℝ := e1522 * e1536

def e1538 : ℝ := e1521 + e1537

def e1539 : ℝ := e1509 ^ 2

def e1540 : ℝ := e5 - e1539

def e1541 : ℝ := Real.sqrt e1540

def e1542 : ℝ := e5 + e1541

def e1543 : ℝ := e1509 / e1542

def e1544 : ℝ := e1543 ^ 2

def e1545 : ℝ := e5 + e1544

def e1546 : ℝ := Real.sqrt e1545

def e1547 : ℝ := e5 + e1546

def e1548 : ℝ := e1543 / e1547

def e1549 : ℝ := Real.arcsin e1509

def e1550 : ℝ := e59 * e1549

def e1551 : ℝ := e61 * e1509

def e1552 : ℝ := e1551 * e1541

def e1553 : ℝ := e1550 - e1552

def e1554 : ℝ := e43 * e1541

def e1555 : ℝ := e1509 / e1554

def e1556 : ℝ := e1553 - e1555

def e1557 : ℝ := e5 + e1525

def e1558 : ℝ := e1508 / e1557

def e1559 : ℝ := e1558 ^ 2

def e1560 : ℝ := e5 + e1559

def e1561 : ℝ := Real.sqrt e1560

def e1562 : ℝ := e5 + e1561

def e1563 : ℝ := e1558 / e1562

def e1564 : ℝ := Real.arcsin e1508

def e1565 : ℝ := e59 * e1564

def e1566 : ℝ := e61 * e1508

def e1567 : ℝ := e1566 * e1525

def e1568 : ℝ := e1565 - e1567

def e1569 : ℝ := e43 * e1525

def e1570 : ℝ := e1508 / e1569

def e1571 : ℝ := e1568 - e1570

def e1572 : ℝ := e1556 - e1571

def e1573 : ℝ := e1572 / e1507

def e1574 : ℝ := e1538 + e1573

def e1575 : ℝ := e1509 + e4

def e1576 : ℝ := e1575 / e23

def e1577 : ℝ := e1509 / e1507

def e1578 : ℝ := e89 * e1577

def e1579 : ℝ := e1577 ^ 2

def e1580 : ℝ := e91 * e1579

def e1581 : ℝ := e5 + e1580

def e1582 : ℝ := Real.sqrt e1581

def e1583 : ℝ := e1578 * e1582

def e1584 : ℝ := e97 * e1579

def e1585 : ℝ := e1583 - e1584

def e1586 : ℝ := e1576 * e1585

def e1587 : ℝ := e1576 / e1507

def e1588 : ℝ := e89 * e1587

def e1589 : ℝ := e1587 ^ 2

def e1590 : ℝ := e91 * e1589

def e1591 : ℝ := e5 + e1590

def e1592 : ℝ := Real.sqrt e1591

def e1593 : ℝ := e1588 * e1592

def e1594 : ℝ := e97 * e1589

def e1595 : ℝ := e1593 - e1594

def e1596 : ℝ := e1509 * e1595

def e1597 : ℝ := e1586 - e1596

def e1598 : ℝ := e1576 ^ 2

def e1599 : ℝ := e8 * e1598

def e1600 : ℝ := e5 - e1599

def e1601 : ℝ := e5 - e1598

def e1602 : ℝ := Real.sqrt e1601

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures1603To1821
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e1603 : ℝ := e1600 / e1602

def e1604 : ℝ := e5 - e1603

def e1605 : ℝ := e8 * e1539

def e1606 : ℝ := e5 - e1605

def e1607 : ℝ := e1606 / e1541

def e1608 : ℝ := e5 - e1607

def e1609 : ℝ := e1604 - e1608

def e1610 : ℝ := e1597 * e1609

def e1611 : ℝ := e1595 - e1585

def e1612 : ℝ := e5 + e1602

def e1613 : ℝ := e1576 / e1612

def e1614 : ℝ := e1613 ^ 2

def e1615 : ℝ := e5 + e1614

def e1616 : ℝ := Real.sqrt e1615

def e1617 : ℝ := e5 + e1616

def e1618 : ℝ := e1613 / e1617

def e1619 : ℝ := Real.arcsin e1576

def e1620 : ℝ := e59 * e1619

def e1621 : ℝ := e61 * e1576

def e1622 : ℝ := e1621 * e1602

def e1623 : ℝ := e1620 - e1622

def e1624 : ℝ := e43 * e1602

def e1625 : ℝ := e1576 / e1624

def e1626 : ℝ := e1623 - e1625

def e1627 : ℝ := e1626 - e1556

def e1628 : ℝ := e1611 * e1627

def e1629 : ℝ := e1610 + e1628

def e1630 : ℝ := e1576 - e1509

def e1631 : ℝ := e1629 / e1630

def e1632 : ℝ := e1574 + e1631

def e1633 : ℝ := e4 * e1595

def e1634 : ℝ := e4 / e1507

def e1635 : ℝ := e89 * e1634

def e1636 : ℝ := e1634 ^ 2

def e1637 : ℝ := e91 * e1636

def e1638 : ℝ := e5 + e1637

def e1639 : ℝ := Real.sqrt e1638

def e1640 : ℝ := e1635 * e1639

def e1641 : ℝ := e97 * e1636

def e1642 : ℝ := e1640 - e1641

def e1643 : ℝ := e1576 * e1642

def e1644 : ℝ := e1633 - e1643

def e1645 : ℝ := e165 - e1604

def e1646 : ℝ := e1644 * e1645

def e1647 : ℝ := e1642 - e1595

def e1648 : ℝ := e183 - e1626

def e1649 : ℝ := e1647 * e1648

def e1650 : ℝ := e1646 + e1649

def e1651 : ℝ := e4 - e1576

def e1652 : ℝ := e1650 / e1651

def e1653 : ℝ := e1632 + e1652

def e1654 : ℝ := e924 / e1507

def e1655 : ℝ := min e7 e1654

def e1656 : ℝ := e1655 - e5

def e1657 : ℝ := e23 * e1507

def e1658 : ℝ := e1657 * e1518

def e1659 : ℝ := e1658 / e0

def e1660 : ℝ := e1656 + e1659

def e1661 : ℝ := e23 * e1512

def e1662 : ℝ := e1661 * e1518

def e1663 : ℝ := e0 + e1662

def e1664 : ℝ := Real.sqrt e1663

def e1665 : ℝ := e932 * e1664

def e1666 : ℝ := e1507 ^ 3

def e1667 : ℝ := e939 * e1666

def e1668 : ℝ := min e1667 e941

def e1669 : ℝ := e23 * e1660

def e1670 : ℝ := e944 * e1668

def e1671 : ℝ := e1665 ^ 2

def e1672 : ℝ := e1670 * e1671

def e1673 : ℝ := e1672 * e1660

def e1674 : ℝ := e1673 / e9

def e1675 : ℝ := e5 + e1674

def e1676 : ℝ := Real.sqrt e1675

def e1677 : ℝ := e5 + e1676

def e1678 : ℝ := e1669 / e1677

def e1679 : ℝ := e1668 * e954

def e1680 : ℝ := e1660 - e1678

def e1681 : ℝ := e1680 / e1665

def e1682 : ℝ := e1681 ^ 2

def e1683 : ℝ := e9 * e1682

def e1684 : ℝ := e1678 ^ 3

def e1685 : ℝ := e1668 * e1684

def e1686 : ℝ := e1683 + e1685

def e1687 : ℝ := min e1679 e1686

def e1688 : ℝ := (61 / 50 : ℝ)

def e1689 : ℝ := e1688 / e0

def e1690 : ℝ := e1688 * e7

def e1691 : ℝ := e8 * e1688

def e1692 : ℝ := e1691 / e0

def e1693 : ℝ := e1688 ^ 2

def e1694 : ℝ := e17 * e1693

def e1695 : ℝ := e1694 / e0

def e1696 : ℝ := e5 + e1695

def e1697 : ℝ := Real.sqrt e1696

def e1698 : ℝ := e5 + e1697

def e1699 : ℝ := e23 / e1698

def e1700 : ℝ := e9 * e1699

def e1701 : ℝ := e1692 + e1700

def e1702 : ℝ := e1701 - e5

def e1703 : ℝ := e0 / e1693

def e1704 : ℝ := e1689 ^ 2

def e1705 : ℝ := e5 - e1704

def e1706 : ℝ := Real.sqrt e1705

def e1707 : ℝ := e29 - e1706

def e1708 : ℝ := e1706 ^ 3

def e1709 : ℝ := e1708 / e35

def e1710 : ℝ := e1707 + e1709

def e1711 : ℝ := e8 * e1710

def e1712 : ℝ := e1704 / e1706

def e1713 : ℝ := e1712 - e23

def e1714 : ℝ := e23 * e1706

def e1715 : ℝ := e1713 + e1714

def e1716 : ℝ := e1715 / e43

def e1717 : ℝ := e1711 - e1716

def e1718 : ℝ := e1703 * e1717

def e1719 : ℝ := e1702 + e1718

def e1720 : ℝ := e1690 ^ 2

def e1721 : ℝ := e5 - e1720

def e1722 : ℝ := Real.sqrt e1721

def e1723 : ℝ := e5 + e1722

def e1724 : ℝ := e1690 / e1723

def e1725 : ℝ := e1724 ^ 2

def e1726 : ℝ := e5 + e1725

def e1727 : ℝ := Real.sqrt e1726

def e1728 : ℝ := e5 + e1727

def e1729 : ℝ := e1724 / e1728

def e1730 : ℝ := Real.arcsin e1690

def e1731 : ℝ := e59 * e1730

def e1732 : ℝ := e61 * e1690

def e1733 : ℝ := e1732 * e1722

def e1734 : ℝ := e1731 - e1733

def e1735 : ℝ := e43 * e1722

def e1736 : ℝ := e1690 / e1735

def e1737 : ℝ := e1734 - e1736

def e1738 : ℝ := e5 + e1706

def e1739 : ℝ := e1689 / e1738

def e1740 : ℝ := e1739 ^ 2

def e1741 : ℝ := e5 + e1740

def e1742 : ℝ := Real.sqrt e1741

def e1743 : ℝ := e5 + e1742

def e1744 : ℝ := e1739 / e1743

def e1745 : ℝ := Real.arcsin e1689

def e1746 : ℝ := e59 * e1745

def e1747 : ℝ := e61 * e1689

def e1748 : ℝ := e1747 * e1706

def e1749 : ℝ := e1746 - e1748

def e1750 : ℝ := e43 * e1706

def e1751 : ℝ := e1689 / e1750

def e1752 : ℝ := e1749 - e1751

def e1753 : ℝ := e1737 - e1752

def e1754 : ℝ := e1753 / e1688

def e1755 : ℝ := e1719 + e1754

def e1756 : ℝ := e1690 + e4

def e1757 : ℝ := e1756 / e23

def e1758 : ℝ := e1690 / e1688

def e1759 : ℝ := e89 * e1758

def e1760 : ℝ := e1758 ^ 2

def e1761 : ℝ := e91 * e1760

def e1762 : ℝ := e5 + e1761

def e1763 : ℝ := Real.sqrt e1762

def e1764 : ℝ := e1759 * e1763

def e1765 : ℝ := e97 * e1760

def e1766 : ℝ := e1764 - e1765

def e1767 : ℝ := e1757 * e1766

def e1768 : ℝ := e1757 / e1688

def e1769 : ℝ := e89 * e1768

def e1770 : ℝ := e1768 ^ 2

def e1771 : ℝ := e91 * e1770

def e1772 : ℝ := e5 + e1771

def e1773 : ℝ := Real.sqrt e1772

def e1774 : ℝ := e1769 * e1773

def e1775 : ℝ := e97 * e1770

def e1776 : ℝ := e1774 - e1775

def e1777 : ℝ := e1690 * e1776

def e1778 : ℝ := e1767 - e1777

def e1779 : ℝ := e1757 ^ 2

def e1780 : ℝ := e8 * e1779

def e1781 : ℝ := e5 - e1780

def e1782 : ℝ := e5 - e1779

def e1783 : ℝ := Real.sqrt e1782

def e1784 : ℝ := e1781 / e1783

def e1785 : ℝ := e5 - e1784

def e1786 : ℝ := e8 * e1720

def e1787 : ℝ := e5 - e1786

def e1788 : ℝ := e1787 / e1722

def e1789 : ℝ := e5 - e1788

def e1790 : ℝ := e1785 - e1789

def e1791 : ℝ := e1778 * e1790

def e1792 : ℝ := e1776 - e1766

def e1793 : ℝ := e5 + e1783

def e1794 : ℝ := e1757 / e1793

def e1795 : ℝ := e1794 ^ 2

def e1796 : ℝ := e5 + e1795

def e1797 : ℝ := Real.sqrt e1796

def e1798 : ℝ := e5 + e1797

def e1799 : ℝ := e1794 / e1798

def e1800 : ℝ := Real.arcsin e1757

def e1801 : ℝ := e59 * e1800

def e1802 : ℝ := e61 * e1757

def e1803 : ℝ := e1802 * e1783

def e1804 : ℝ := e1801 - e1803

def e1805 : ℝ := e43 * e1783

def e1806 : ℝ := e1757 / e1805

def e1807 : ℝ := e1804 - e1806

def e1808 : ℝ := e1807 - e1737

def e1809 : ℝ := e1792 * e1808

def e1810 : ℝ := e1791 + e1809

def e1811 : ℝ := e1757 - e1690

def e1812 : ℝ := e1810 / e1811

def e1813 : ℝ := e1755 + e1812

def e1814 : ℝ := e4 * e1776

def e1815 : ℝ := e4 / e1688

def e1816 : ℝ := e89 * e1815

def e1817 : ℝ := e1815 ^ 2

def e1818 : ℝ := e91 * e1817

def e1819 : ℝ := e5 + e1818

def e1820 : ℝ := Real.sqrt e1819

def e1821 : ℝ := e1816 * e1820

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures1822To2041
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e1822 : ℝ := e97 * e1817

def e1823 : ℝ := e1821 - e1822

def e1824 : ℝ := e1757 * e1823

def e1825 : ℝ := e1814 - e1824

def e1826 : ℝ := e165 - e1785

def e1827 : ℝ := e1825 * e1826

def e1828 : ℝ := e1823 - e1776

def e1829 : ℝ := e183 - e1807

def e1830 : ℝ := e1828 * e1829

def e1831 : ℝ := e1827 + e1830

def e1832 : ℝ := e4 - e1757

def e1833 : ℝ := e1831 / e1832

def e1834 : ℝ := e1813 + e1833

def e1835 : ℝ := e924 / e1688

def e1836 : ℝ := min e7 e1835

def e1837 : ℝ := e1836 - e5

def e1838 : ℝ := e23 * e1688

def e1839 : ℝ := e1838 * e1699

def e1840 : ℝ := e1839 / e0

def e1841 : ℝ := e1837 + e1840

def e1842 : ℝ := e23 * e1693

def e1843 : ℝ := e1842 * e1699

def e1844 : ℝ := e0 + e1843

def e1845 : ℝ := Real.sqrt e1844

def e1846 : ℝ := e932 * e1845

def e1847 : ℝ := e1688 ^ 3

def e1848 : ℝ := e939 * e1847

def e1849 : ℝ := min e1848 e941

def e1850 : ℝ := e23 * e1841

def e1851 : ℝ := e944 * e1849

def e1852 : ℝ := e1846 ^ 2

def e1853 : ℝ := e1851 * e1852

def e1854 : ℝ := e1853 * e1841

def e1855 : ℝ := e1854 / e9

def e1856 : ℝ := e5 + e1855

def e1857 : ℝ := Real.sqrt e1856

def e1858 : ℝ := e5 + e1857

def e1859 : ℝ := e1850 / e1858

def e1860 : ℝ := e1849 * e954

def e1861 : ℝ := e1841 - e1859

def e1862 : ℝ := e1861 / e1846

def e1863 : ℝ := e1862 ^ 2

def e1864 : ℝ := e9 * e1863

def e1865 : ℝ := e1859 ^ 3

def e1866 : ℝ := e1849 * e1865

def e1867 : ℝ := e1864 + e1866

def e1868 : ℝ := min e1860 e1867

def e1869 : ℝ := (63 / 50 : ℝ)

def e1870 : ℝ := e1869 / e0

def e1871 : ℝ := e1869 * e7

def e1872 : ℝ := e8 * e1869

def e1873 : ℝ := e1872 / e0

def e1874 : ℝ := e1869 ^ 2

def e1875 : ℝ := e17 * e1874

def e1876 : ℝ := e1875 / e0

def e1877 : ℝ := e5 + e1876

def e1878 : ℝ := Real.sqrt e1877

def e1879 : ℝ := e5 + e1878

def e1880 : ℝ := e23 / e1879

def e1881 : ℝ := e9 * e1880

def e1882 : ℝ := e1873 + e1881

def e1883 : ℝ := e1882 - e5

def e1884 : ℝ := e0 / e1874

def e1885 : ℝ := e1870 ^ 2

def e1886 : ℝ := e5 - e1885

def e1887 : ℝ := Real.sqrt e1886

def e1888 : ℝ := e29 - e1887

def e1889 : ℝ := e1887 ^ 3

def e1890 : ℝ := e1889 / e35

def e1891 : ℝ := e1888 + e1890

def e1892 : ℝ := e8 * e1891

def e1893 : ℝ := e1885 / e1887

def e1894 : ℝ := e1893 - e23

def e1895 : ℝ := e23 * e1887

def e1896 : ℝ := e1894 + e1895

def e1897 : ℝ := e1896 / e43

def e1898 : ℝ := e1892 - e1897

def e1899 : ℝ := e1884 * e1898

def e1900 : ℝ := e1883 + e1899

def e1901 : ℝ := e1871 ^ 2

def e1902 : ℝ := e5 - e1901

def e1903 : ℝ := Real.sqrt e1902

def e1904 : ℝ := e5 + e1903

def e1905 : ℝ := e1871 / e1904

def e1906 : ℝ := e1905 ^ 2

def e1907 : ℝ := e5 + e1906

def e1908 : ℝ := Real.sqrt e1907

def e1909 : ℝ := e5 + e1908

def e1910 : ℝ := e1905 / e1909

def e1911 : ℝ := Real.arcsin e1871

def e1912 : ℝ := e59 * e1911

def e1913 : ℝ := e61 * e1871

def e1914 : ℝ := e1913 * e1903

def e1915 : ℝ := e1912 - e1914

def e1916 : ℝ := e43 * e1903

def e1917 : ℝ := e1871 / e1916

def e1918 : ℝ := e1915 - e1917

def e1919 : ℝ := e5 + e1887

def e1920 : ℝ := e1870 / e1919

def e1921 : ℝ := e1920 ^ 2

def e1922 : ℝ := e5 + e1921

def e1923 : ℝ := Real.sqrt e1922

def e1924 : ℝ := e5 + e1923

def e1925 : ℝ := e1920 / e1924

def e1926 : ℝ := Real.arcsin e1870

def e1927 : ℝ := e59 * e1926

def e1928 : ℝ := e61 * e1870

def e1929 : ℝ := e1928 * e1887

def e1930 : ℝ := e1927 - e1929

def e1931 : ℝ := e43 * e1887

def e1932 : ℝ := e1870 / e1931

def e1933 : ℝ := e1930 - e1932

def e1934 : ℝ := e1918 - e1933

def e1935 : ℝ := e1934 / e1869

def e1936 : ℝ := e1900 + e1935

def e1937 : ℝ := e1871 + e4

def e1938 : ℝ := e1937 / e23

def e1939 : ℝ := e1871 / e1869

def e1940 : ℝ := e89 * e1939

def e1941 : ℝ := e1939 ^ 2

def e1942 : ℝ := e91 * e1941

def e1943 : ℝ := e5 + e1942

def e1944 : ℝ := Real.sqrt e1943

def e1945 : ℝ := e1940 * e1944

def e1946 : ℝ := e97 * e1941

def e1947 : ℝ := e1945 - e1946

def e1948 : ℝ := e1938 * e1947

def e1949 : ℝ := e1938 / e1869

def e1950 : ℝ := e89 * e1949

def e1951 : ℝ := e1949 ^ 2

def e1952 : ℝ := e91 * e1951

def e1953 : ℝ := e5 + e1952

def e1954 : ℝ := Real.sqrt e1953

def e1955 : ℝ := e1950 * e1954

def e1956 : ℝ := e97 * e1951

def e1957 : ℝ := e1955 - e1956

def e1958 : ℝ := e1871 * e1957

def e1959 : ℝ := e1948 - e1958

def e1960 : ℝ := e1938 ^ 2

def e1961 : ℝ := e8 * e1960

def e1962 : ℝ := e5 - e1961

def e1963 : ℝ := e5 - e1960

def e1964 : ℝ := Real.sqrt e1963

def e1965 : ℝ := e1962 / e1964

def e1966 : ℝ := e5 - e1965

def e1967 : ℝ := e8 * e1901

def e1968 : ℝ := e5 - e1967

def e1969 : ℝ := e1968 / e1903

def e1970 : ℝ := e5 - e1969

def e1971 : ℝ := e1966 - e1970

def e1972 : ℝ := e1959 * e1971

def e1973 : ℝ := e1957 - e1947

def e1974 : ℝ := e5 + e1964

def e1975 : ℝ := e1938 / e1974

def e1976 : ℝ := e1975 ^ 2

def e1977 : ℝ := e5 + e1976

def e1978 : ℝ := Real.sqrt e1977

def e1979 : ℝ := e5 + e1978

def e1980 : ℝ := e1975 / e1979

def e1981 : ℝ := Real.arcsin e1938

def e1982 : ℝ := e59 * e1981

def e1983 : ℝ := e61 * e1938

def e1984 : ℝ := e1983 * e1964

def e1985 : ℝ := e1982 - e1984

def e1986 : ℝ := e43 * e1964

def e1987 : ℝ := e1938 / e1986

def e1988 : ℝ := e1985 - e1987

def e1989 : ℝ := e1988 - e1918

def e1990 : ℝ := e1973 * e1989

def e1991 : ℝ := e1972 + e1990

def e1992 : ℝ := e1938 - e1871

def e1993 : ℝ := e1991 / e1992

def e1994 : ℝ := e1936 + e1993

def e1995 : ℝ := e4 * e1957

def e1996 : ℝ := e4 / e1869

def e1997 : ℝ := e89 * e1996

def e1998 : ℝ := e1996 ^ 2

def e1999 : ℝ := e91 * e1998

def e2000 : ℝ := e5 + e1999

def e2001 : ℝ := Real.sqrt e2000

def e2002 : ℝ := e1997 * e2001

def e2003 : ℝ := e97 * e1998

def e2004 : ℝ := e2002 - e2003

def e2005 : ℝ := e1938 * e2004

def e2006 : ℝ := e1995 - e2005

def e2007 : ℝ := e165 - e1966

def e2008 : ℝ := e2006 * e2007

def e2009 : ℝ := e2004 - e1957

def e2010 : ℝ := e183 - e1988

def e2011 : ℝ := e2009 * e2010

def e2012 : ℝ := e2008 + e2011

def e2013 : ℝ := e4 - e1938

def e2014 : ℝ := e2012 / e2013

def e2015 : ℝ := e1994 + e2014

def e2016 : ℝ := e924 / e1869

def e2017 : ℝ := min e7 e2016

def e2018 : ℝ := e2017 - e5

def e2019 : ℝ := e23 * e1869

def e2020 : ℝ := e2019 * e1880

def e2021 : ℝ := e2020 / e0

def e2022 : ℝ := e2018 + e2021

def e2023 : ℝ := e23 * e1874

def e2024 : ℝ := e2023 * e1880

def e2025 : ℝ := e0 + e2024

def e2026 : ℝ := Real.sqrt e2025

def e2027 : ℝ := e932 * e2026

def e2028 : ℝ := e1869 ^ 3

def e2029 : ℝ := e939 * e2028

def e2030 : ℝ := min e2029 e941

def e2031 : ℝ := e23 * e2022

def e2032 : ℝ := e944 * e2030

def e2033 : ℝ := e2027 ^ 2

def e2034 : ℝ := e2032 * e2033

def e2035 : ℝ := e2034 * e2022

def e2036 : ℝ := e2035 / e9

def e2037 : ℝ := e5 + e2036

def e2038 : ℝ := Real.sqrt e2037

def e2039 : ℝ := e5 + e2038

def e2040 : ℝ := e2031 / e2039

def e2041 : ℝ := e2030 * e954

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2042To2262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e2042 : ℝ := e2022 - e2040

def e2043 : ℝ := e2042 / e2027

def e2044 : ℝ := e2043 ^ 2

def e2045 : ℝ := e9 * e2044

def e2046 : ℝ := e2040 ^ 3

def e2047 : ℝ := e2030 * e2046

def e2048 : ℝ := e2045 + e2047

def e2049 : ℝ := min e2041 e2048

def e2050 : ℝ := (13 / 10 : ℝ)

def e2051 : ℝ := e2050 / e0

def e2052 : ℝ := e2050 * e7

def e2053 : ℝ := e8 * e2050

def e2054 : ℝ := e2053 / e0

def e2055 : ℝ := e2050 ^ 2

def e2056 : ℝ := e17 * e2055

def e2057 : ℝ := e2056 / e0

def e2058 : ℝ := e5 + e2057

def e2059 : ℝ := Real.sqrt e2058

def e2060 : ℝ := e5 + e2059

def e2061 : ℝ := e23 / e2060

def e2062 : ℝ := e9 * e2061

def e2063 : ℝ := e2054 + e2062

def e2064 : ℝ := e2063 - e5

def e2065 : ℝ := e0 / e2055

def e2066 : ℝ := e2051 ^ 2

def e2067 : ℝ := e5 - e2066

def e2068 : ℝ := Real.sqrt e2067

def e2069 : ℝ := e29 - e2068

def e2070 : ℝ := e2068 ^ 3

def e2071 : ℝ := e2070 / e35

def e2072 : ℝ := e2069 + e2071

def e2073 : ℝ := e8 * e2072

def e2074 : ℝ := e2066 / e2068

def e2075 : ℝ := e2074 - e23

def e2076 : ℝ := e23 * e2068

def e2077 : ℝ := e2075 + e2076

def e2078 : ℝ := e2077 / e43

def e2079 : ℝ := e2073 - e2078

def e2080 : ℝ := e2065 * e2079

def e2081 : ℝ := e2064 + e2080

def e2082 : ℝ := e2052 ^ 2

def e2083 : ℝ := e5 - e2082

def e2084 : ℝ := Real.sqrt e2083

def e2085 : ℝ := e5 + e2084

def e2086 : ℝ := e2052 / e2085

def e2087 : ℝ := e2086 ^ 2

def e2088 : ℝ := e5 + e2087

def e2089 : ℝ := Real.sqrt e2088

def e2090 : ℝ := e5 + e2089

def e2091 : ℝ := e2086 / e2090

def e2092 : ℝ := Real.arcsin e2052

def e2093 : ℝ := e59 * e2092

def e2094 : ℝ := e61 * e2052

def e2095 : ℝ := e2094 * e2084

def e2096 : ℝ := e2093 - e2095

def e2097 : ℝ := e43 * e2084

def e2098 : ℝ := e2052 / e2097

def e2099 : ℝ := e2096 - e2098

def e2100 : ℝ := e5 + e2068

def e2101 : ℝ := e2051 / e2100

def e2102 : ℝ := e2101 ^ 2

def e2103 : ℝ := e5 + e2102

def e2104 : ℝ := Real.sqrt e2103

def e2105 : ℝ := e5 + e2104

def e2106 : ℝ := e2101 / e2105

def e2107 : ℝ := Real.arcsin e2051

def e2108 : ℝ := e59 * e2107

def e2109 : ℝ := e61 * e2051

def e2110 : ℝ := e2109 * e2068

def e2111 : ℝ := e2108 - e2110

def e2112 : ℝ := e43 * e2068

def e2113 : ℝ := e2051 / e2112

def e2114 : ℝ := e2111 - e2113

def e2115 : ℝ := e2099 - e2114

def e2116 : ℝ := e2115 / e2050

def e2117 : ℝ := e2081 + e2116

def e2118 : ℝ := e2052 + e4

def e2119 : ℝ := e2118 / e23

def e2120 : ℝ := e2052 / e2050

def e2121 : ℝ := e89 * e2120

def e2122 : ℝ := e2120 ^ 2

def e2123 : ℝ := e91 * e2122

def e2124 : ℝ := e5 + e2123

def e2125 : ℝ := Real.sqrt e2124

def e2126 : ℝ := e2121 * e2125

def e2127 : ℝ := e97 * e2122

def e2128 : ℝ := e2126 - e2127

def e2129 : ℝ := e2119 * e2128

def e2130 : ℝ := e2119 / e2050

def e2131 : ℝ := e89 * e2130

def e2132 : ℝ := e2130 ^ 2

def e2133 : ℝ := e91 * e2132

def e2134 : ℝ := e5 + e2133

def e2135 : ℝ := Real.sqrt e2134

def e2136 : ℝ := e2131 * e2135

def e2137 : ℝ := e97 * e2132

def e2138 : ℝ := e2136 - e2137

def e2139 : ℝ := e2052 * e2138

def e2140 : ℝ := e2129 - e2139

def e2141 : ℝ := e2119 ^ 2

def e2142 : ℝ := e8 * e2141

def e2143 : ℝ := e5 - e2142

def e2144 : ℝ := e5 - e2141

def e2145 : ℝ := Real.sqrt e2144

def e2146 : ℝ := e2143 / e2145

def e2147 : ℝ := e5 - e2146

def e2148 : ℝ := e8 * e2082

def e2149 : ℝ := e5 - e2148

def e2150 : ℝ := e2149 / e2084

def e2151 : ℝ := e5 - e2150

def e2152 : ℝ := e2147 - e2151

def e2153 : ℝ := e2140 * e2152

def e2154 : ℝ := e2138 - e2128

def e2155 : ℝ := e5 + e2145

def e2156 : ℝ := e2119 / e2155

def e2157 : ℝ := e2156 ^ 2

def e2158 : ℝ := e5 + e2157

def e2159 : ℝ := Real.sqrt e2158

def e2160 : ℝ := e5 + e2159

def e2161 : ℝ := e2156 / e2160

def e2162 : ℝ := Real.arcsin e2119

def e2163 : ℝ := e59 * e2162

def e2164 : ℝ := e61 * e2119

def e2165 : ℝ := e2164 * e2145

def e2166 : ℝ := e2163 - e2165

def e2167 : ℝ := e43 * e2145

def e2168 : ℝ := e2119 / e2167

def e2169 : ℝ := e2166 - e2168

def e2170 : ℝ := e2169 - e2099

def e2171 : ℝ := e2154 * e2170

def e2172 : ℝ := e2153 + e2171

def e2173 : ℝ := e2119 - e2052

def e2174 : ℝ := e2172 / e2173

def e2175 : ℝ := e2117 + e2174

def e2176 : ℝ := e4 * e2138

def e2177 : ℝ := e4 / e2050

def e2178 : ℝ := e89 * e2177

def e2179 : ℝ := e2177 ^ 2

def e2180 : ℝ := e91 * e2179

def e2181 : ℝ := e5 + e2180

def e2182 : ℝ := Real.sqrt e2181

def e2183 : ℝ := e2178 * e2182

def e2184 : ℝ := e97 * e2179

def e2185 : ℝ := e2183 - e2184

def e2186 : ℝ := e2119 * e2185

def e2187 : ℝ := e2176 - e2186

def e2188 : ℝ := e165 - e2147

def e2189 : ℝ := e2187 * e2188

def e2190 : ℝ := e2185 - e2138

def e2191 : ℝ := e183 - e2169

def e2192 : ℝ := e2190 * e2191

def e2193 : ℝ := e2189 + e2192

def e2194 : ℝ := e4 - e2119

def e2195 : ℝ := e2193 / e2194

def e2196 : ℝ := e2175 + e2195

def e2197 : ℝ := e924 / e2050

def e2198 : ℝ := min e7 e2197

def e2199 : ℝ := e2198 - e5

def e2200 : ℝ := e23 * e2050

def e2201 : ℝ := e2200 * e2061

def e2202 : ℝ := e2201 / e0

def e2203 : ℝ := e2199 + e2202

def e2204 : ℝ := e23 * e2055

def e2205 : ℝ := e2204 * e2061

def e2206 : ℝ := e0 + e2205

def e2207 : ℝ := Real.sqrt e2206

def e2208 : ℝ := e932 * e2207

def e2209 : ℝ := e2050 ^ 3

def e2210 : ℝ := e939 * e2209

def e2211 : ℝ := min e2210 e941

def e2212 : ℝ := e23 * e2203

def e2213 : ℝ := e944 * e2211

def e2214 : ℝ := e2208 ^ 2

def e2215 : ℝ := e2213 * e2214

def e2216 : ℝ := e2215 * e2203

def e2217 : ℝ := e2216 / e9

def e2218 : ℝ := e5 + e2217

def e2219 : ℝ := Real.sqrt e2218

def e2220 : ℝ := e5 + e2219

def e2221 : ℝ := e2212 / e2220

def e2222 : ℝ := e2211 * e954

def e2223 : ℝ := e2203 - e2221

def e2224 : ℝ := e2223 / e2208

def e2225 : ℝ := e2224 ^ 2

def e2226 : ℝ := e9 * e2225

def e2227 : ℝ := e2221 ^ 3

def e2228 : ℝ := e2211 * e2227

def e2229 : ℝ := e2226 + e2228

def e2230 : ℝ := min e2222 e2229

def e2231 : ℝ := (67 / 50 : ℝ)

def e2232 : ℝ := e2231 / e0

def e2233 : ℝ := e2231 * e7

def e2234 : ℝ := e8 * e2231

def e2235 : ℝ := e2234 / e0

def e2236 : ℝ := e2231 ^ 2

def e2237 : ℝ := e17 * e2236

def e2238 : ℝ := e2237 / e0

def e2239 : ℝ := e5 + e2238

def e2240 : ℝ := Real.sqrt e2239

def e2241 : ℝ := e5 + e2240

def e2242 : ℝ := e23 / e2241

def e2243 : ℝ := e9 * e2242

def e2244 : ℝ := e2235 + e2243

def e2245 : ℝ := e2244 - e5

def e2246 : ℝ := e0 / e2236

def e2247 : ℝ := e2232 ^ 2

def e2248 : ℝ := e5 - e2247

def e2249 : ℝ := Real.sqrt e2248

def e2250 : ℝ := e29 - e2249

def e2251 : ℝ := e2249 ^ 3

def e2252 : ℝ := e2251 / e35

def e2253 : ℝ := e2250 + e2252

def e2254 : ℝ := e8 * e2253

def e2255 : ℝ := e2247 / e2249

def e2256 : ℝ := e2255 - e23

def e2257 : ℝ := e23 * e2249

def e2258 : ℝ := e2256 + e2257

def e2259 : ℝ := e2258 / e43

def e2260 : ℝ := e2254 - e2259

def e2261 : ℝ := e2246 * e2260

def e2262 : ℝ := e2245 + e2261

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2263To2479
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e2263 : ℝ := e2233 ^ 2

def e2264 : ℝ := e5 - e2263

def e2265 : ℝ := Real.sqrt e2264

def e2266 : ℝ := e5 + e2265

def e2267 : ℝ := e2233 / e2266

def e2268 : ℝ := e2267 ^ 2

def e2269 : ℝ := e5 + e2268

def e2270 : ℝ := Real.sqrt e2269

def e2271 : ℝ := e5 + e2270

def e2272 : ℝ := e2267 / e2271

def e2273 : ℝ := Real.arcsin e2233

def e2274 : ℝ := e59 * e2273

def e2275 : ℝ := e61 * e2233

def e2276 : ℝ := e2275 * e2265

def e2277 : ℝ := e2274 - e2276

def e2278 : ℝ := e43 * e2265

def e2279 : ℝ := e2233 / e2278

def e2280 : ℝ := e2277 - e2279

def e2281 : ℝ := e5 + e2249

def e2282 : ℝ := e2232 / e2281

def e2283 : ℝ := e2282 ^ 2

def e2284 : ℝ := e5 + e2283

def e2285 : ℝ := Real.sqrt e2284

def e2286 : ℝ := e5 + e2285

def e2287 : ℝ := e2282 / e2286

def e2288 : ℝ := Real.arcsin e2232

def e2289 : ℝ := e59 * e2288

def e2290 : ℝ := e61 * e2232

def e2291 : ℝ := e2290 * e2249

def e2292 : ℝ := e2289 - e2291

def e2293 : ℝ := e43 * e2249

def e2294 : ℝ := e2232 / e2293

def e2295 : ℝ := e2292 - e2294

def e2296 : ℝ := e2280 - e2295

def e2297 : ℝ := e2296 / e2231

def e2298 : ℝ := e2262 + e2297

def e2299 : ℝ := e2233 + e4

def e2300 : ℝ := e2299 / e23

def e2301 : ℝ := e2233 / e2231

def e2302 : ℝ := e89 * e2301

def e2303 : ℝ := e2301 ^ 2

def e2304 : ℝ := e91 * e2303

def e2305 : ℝ := e5 + e2304

def e2306 : ℝ := Real.sqrt e2305

def e2307 : ℝ := e2302 * e2306

def e2308 : ℝ := e97 * e2303

def e2309 : ℝ := e2307 - e2308

def e2310 : ℝ := e2300 * e2309

def e2311 : ℝ := e2300 / e2231

def e2312 : ℝ := e89 * e2311

def e2313 : ℝ := e2311 ^ 2

def e2314 : ℝ := e91 * e2313

def e2315 : ℝ := e5 + e2314

def e2316 : ℝ := Real.sqrt e2315

def e2317 : ℝ := e2312 * e2316

def e2318 : ℝ := e97 * e2313

def e2319 : ℝ := e2317 - e2318

def e2320 : ℝ := e2233 * e2319

def e2321 : ℝ := e2310 - e2320

def e2322 : ℝ := e2300 ^ 2

def e2323 : ℝ := e8 * e2322

def e2324 : ℝ := e5 - e2323

def e2325 : ℝ := e5 - e2322

def e2326 : ℝ := Real.sqrt e2325

def e2327 : ℝ := e2324 / e2326

def e2328 : ℝ := e5 - e2327

def e2329 : ℝ := e8 * e2263

def e2330 : ℝ := e5 - e2329

def e2331 : ℝ := e2330 / e2265

def e2332 : ℝ := e5 - e2331

def e2333 : ℝ := e2328 - e2332

def e2334 : ℝ := e2321 * e2333

def e2335 : ℝ := e2319 - e2309

def e2336 : ℝ := e5 + e2326

def e2337 : ℝ := e2300 / e2336

def e2338 : ℝ := e2337 ^ 2

def e2339 : ℝ := e5 + e2338

def e2340 : ℝ := Real.sqrt e2339

def e2341 : ℝ := e5 + e2340

def e2342 : ℝ := e2337 / e2341

def e2343 : ℝ := Real.arcsin e2300

def e2344 : ℝ := e59 * e2343

def e2345 : ℝ := e61 * e2300

def e2346 : ℝ := e2345 * e2326

def e2347 : ℝ := e2344 - e2346

def e2348 : ℝ := e43 * e2326

def e2349 : ℝ := e2300 / e2348

def e2350 : ℝ := e2347 - e2349

def e2351 : ℝ := e2350 - e2280

def e2352 : ℝ := e2335 * e2351

def e2353 : ℝ := e2334 + e2352

def e2354 : ℝ := e2300 - e2233

def e2355 : ℝ := e2353 / e2354

def e2356 : ℝ := e2298 + e2355

def e2357 : ℝ := e4 * e2319

def e2358 : ℝ := e4 / e2231

def e2359 : ℝ := e89 * e2358

def e2360 : ℝ := e2358 ^ 2

def e2361 : ℝ := e91 * e2360

def e2362 : ℝ := e5 + e2361

def e2363 : ℝ := Real.sqrt e2362

def e2364 : ℝ := e2359 * e2363

def e2365 : ℝ := e97 * e2360

def e2366 : ℝ := e2364 - e2365

def e2367 : ℝ := e2300 * e2366

def e2368 : ℝ := e2357 - e2367

def e2369 : ℝ := e165 - e2328

def e2370 : ℝ := e2368 * e2369

def e2371 : ℝ := e2366 - e2319

def e2372 : ℝ := e183 - e2350

def e2373 : ℝ := e2371 * e2372

def e2374 : ℝ := e2370 + e2373

def e2375 : ℝ := e4 - e2300

def e2376 : ℝ := e2374 / e2375

def e2377 : ℝ := e2356 + e2376

def e2378 : ℝ := e924 / e2231

def e2379 : ℝ := min e7 e2378

def e2380 : ℝ := e2379 - e5

def e2381 : ℝ := e23 * e2231

def e2382 : ℝ := e2381 * e2242

def e2383 : ℝ := e2382 / e0

def e2384 : ℝ := e2380 + e2383

def e2385 : ℝ := e23 * e2236

def e2386 : ℝ := e2385 * e2242

def e2387 : ℝ := e0 + e2386

def e2388 : ℝ := Real.sqrt e2387

def e2389 : ℝ := e932 * e2388

def e2390 : ℝ := e2231 ^ 3

def e2391 : ℝ := e939 * e2390

def e2392 : ℝ := min e2391 e941

def e2393 : ℝ := e23 * e2384

def e2394 : ℝ := e944 * e2392

def e2395 : ℝ := e2389 ^ 2

def e2396 : ℝ := e2394 * e2395

def e2397 : ℝ := e2396 * e2384

def e2398 : ℝ := e2397 / e9

def e2399 : ℝ := e5 + e2398

def e2400 : ℝ := Real.sqrt e2399

def e2401 : ℝ := e5 + e2400

def e2402 : ℝ := e2393 / e2401

def e2403 : ℝ := e2392 * e954

def e2404 : ℝ := e2384 - e2402

def e2405 : ℝ := e2404 / e2389

def e2406 : ℝ := e2405 ^ 2

def e2407 : ℝ := e9 * e2406

def e2408 : ℝ := e2402 ^ 3

def e2409 : ℝ := e2392 * e2408

def e2410 : ℝ := e2407 + e2409

def e2411 : ℝ := min e2403 e2410

def e2412 : ℝ := (69 / 50 : ℝ)

def e2413 : ℝ := e2412 / e0

def e2414 : ℝ := e2412 * e7

def e2415 : ℝ := e8 * e2412

def e2416 : ℝ := e2415 / e0

def e2417 : ℝ := e2412 ^ 2

def e2418 : ℝ := e17 * e2417

def e2419 : ℝ := e2418 / e0

def e2420 : ℝ := e5 + e2419

def e2421 : ℝ := Real.sqrt e2420

def e2422 : ℝ := e5 + e2421

def e2423 : ℝ := e23 / e2422

def e2424 : ℝ := e9 * e2423

def e2425 : ℝ := e2416 + e2424

def e2426 : ℝ := e2425 - e5

def e2427 : ℝ := e0 / e2417

def e2428 : ℝ := e2413 ^ 2

def e2429 : ℝ := e5 - e2428

def e2430 : ℝ := Real.sqrt e2429

def e2431 : ℝ := e29 - e2430

def e2432 : ℝ := e2430 ^ 3

def e2433 : ℝ := e2432 / e35

def e2434 : ℝ := e2431 + e2433

def e2435 : ℝ := e8 * e2434

def e2436 : ℝ := e2428 / e2430

def e2437 : ℝ := e2436 - e23

def e2438 : ℝ := e23 * e2430

def e2439 : ℝ := e2437 + e2438

def e2440 : ℝ := e2439 / e43

def e2441 : ℝ := e2435 - e2440

def e2442 : ℝ := e2427 * e2441

def e2443 : ℝ := e2426 + e2442

def e2444 : ℝ := e2414 ^ 2

def e2445 : ℝ := e5 - e2444

def e2446 : ℝ := Real.sqrt e2445

def e2447 : ℝ := e5 + e2446

def e2448 : ℝ := e2414 / e2447

def e2449 : ℝ := e2448 ^ 2

def e2450 : ℝ := e5 + e2449

def e2451 : ℝ := Real.sqrt e2450

def e2452 : ℝ := e5 + e2451

def e2453 : ℝ := e2448 / e2452

def e2454 : ℝ := Real.arcsin e2414

def e2455 : ℝ := e59 * e2454

def e2456 : ℝ := e61 * e2414

def e2457 : ℝ := e2456 * e2446

def e2458 : ℝ := e2455 - e2457

def e2459 : ℝ := e43 * e2446

def e2460 : ℝ := e2414 / e2459

def e2461 : ℝ := e2458 - e2460

def e2462 : ℝ := e5 + e2430

def e2463 : ℝ := e2413 / e2462

def e2464 : ℝ := e2463 ^ 2

def e2465 : ℝ := e5 + e2464

def e2466 : ℝ := Real.sqrt e2465

def e2467 : ℝ := e5 + e2466

def e2468 : ℝ := e2463 / e2467

def e2469 : ℝ := Real.arcsin e2413

def e2470 : ℝ := e59 * e2469

def e2471 : ℝ := e61 * e2413

def e2472 : ℝ := e2471 * e2430

def e2473 : ℝ := e2470 - e2472

def e2474 : ℝ := e43 * e2430

def e2475 : ℝ := e2413 / e2474

def e2476 : ℝ := e2473 - e2475

def e2477 : ℝ := e2461 - e2476

def e2478 : ℝ := e2477 / e2412

def e2479 : ℝ := e2443 + e2478

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2480To2700
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e2480 : ℝ := e2414 + e4

def e2481 : ℝ := e2480 / e23

def e2482 : ℝ := e2414 / e2412

def e2483 : ℝ := e89 * e2482

def e2484 : ℝ := e2482 ^ 2

def e2485 : ℝ := e91 * e2484

def e2486 : ℝ := e5 + e2485

def e2487 : ℝ := Real.sqrt e2486

def e2488 : ℝ := e2483 * e2487

def e2489 : ℝ := e97 * e2484

def e2490 : ℝ := e2488 - e2489

def e2491 : ℝ := e2481 * e2490

def e2492 : ℝ := e2481 / e2412

def e2493 : ℝ := e89 * e2492

def e2494 : ℝ := e2492 ^ 2

def e2495 : ℝ := e91 * e2494

def e2496 : ℝ := e5 + e2495

def e2497 : ℝ := Real.sqrt e2496

def e2498 : ℝ := e2493 * e2497

def e2499 : ℝ := e97 * e2494

def e2500 : ℝ := e2498 - e2499

def e2501 : ℝ := e2414 * e2500

def e2502 : ℝ := e2491 - e2501

def e2503 : ℝ := e2481 ^ 2

def e2504 : ℝ := e8 * e2503

def e2505 : ℝ := e5 - e2504

def e2506 : ℝ := e5 - e2503

def e2507 : ℝ := Real.sqrt e2506

def e2508 : ℝ := e2505 / e2507

def e2509 : ℝ := e5 - e2508

def e2510 : ℝ := e8 * e2444

def e2511 : ℝ := e5 - e2510

def e2512 : ℝ := e2511 / e2446

def e2513 : ℝ := e5 - e2512

def e2514 : ℝ := e2509 - e2513

def e2515 : ℝ := e2502 * e2514

def e2516 : ℝ := e2500 - e2490

def e2517 : ℝ := e5 + e2507

def e2518 : ℝ := e2481 / e2517

def e2519 : ℝ := e2518 ^ 2

def e2520 : ℝ := e5 + e2519

def e2521 : ℝ := Real.sqrt e2520

def e2522 : ℝ := e5 + e2521

def e2523 : ℝ := e2518 / e2522

def e2524 : ℝ := Real.arcsin e2481

def e2525 : ℝ := e59 * e2524

def e2526 : ℝ := e61 * e2481

def e2527 : ℝ := e2526 * e2507

def e2528 : ℝ := e2525 - e2527

def e2529 : ℝ := e43 * e2507

def e2530 : ℝ := e2481 / e2529

def e2531 : ℝ := e2528 - e2530

def e2532 : ℝ := e2531 - e2461

def e2533 : ℝ := e2516 * e2532

def e2534 : ℝ := e2515 + e2533

def e2535 : ℝ := e2481 - e2414

def e2536 : ℝ := e2534 / e2535

def e2537 : ℝ := e2479 + e2536

def e2538 : ℝ := e4 * e2500

def e2539 : ℝ := e4 / e2412

def e2540 : ℝ := e89 * e2539

def e2541 : ℝ := e2539 ^ 2

def e2542 : ℝ := e91 * e2541

def e2543 : ℝ := e5 + e2542

def e2544 : ℝ := Real.sqrt e2543

def e2545 : ℝ := e2540 * e2544

def e2546 : ℝ := e97 * e2541

def e2547 : ℝ := e2545 - e2546

def e2548 : ℝ := e2481 * e2547

def e2549 : ℝ := e2538 - e2548

def e2550 : ℝ := e165 - e2509

def e2551 : ℝ := e2549 * e2550

def e2552 : ℝ := e2547 - e2500

def e2553 : ℝ := e183 - e2531

def e2554 : ℝ := e2552 * e2553

def e2555 : ℝ := e2551 + e2554

def e2556 : ℝ := e4 - e2481

def e2557 : ℝ := e2555 / e2556

def e2558 : ℝ := e2537 + e2557

def e2559 : ℝ := e924 / e2412

def e2560 : ℝ := min e7 e2559

def e2561 : ℝ := e2560 - e5

def e2562 : ℝ := e23 * e2412

def e2563 : ℝ := e2562 * e2423

def e2564 : ℝ := e2563 / e0

def e2565 : ℝ := e2561 + e2564

def e2566 : ℝ := e23 * e2417

def e2567 : ℝ := e2566 * e2423

def e2568 : ℝ := e0 + e2567

def e2569 : ℝ := Real.sqrt e2568

def e2570 : ℝ := e932 * e2569

def e2571 : ℝ := e2412 ^ 3

def e2572 : ℝ := e939 * e2571

def e2573 : ℝ := min e2572 e941

def e2574 : ℝ := e23 * e2565

def e2575 : ℝ := e944 * e2573

def e2576 : ℝ := e2570 ^ 2

def e2577 : ℝ := e2575 * e2576

def e2578 : ℝ := e2577 * e2565

def e2579 : ℝ := e2578 / e9

def e2580 : ℝ := e5 + e2579

def e2581 : ℝ := Real.sqrt e2580

def e2582 : ℝ := e5 + e2581

def e2583 : ℝ := e2574 / e2582

def e2584 : ℝ := e2573 * e954

def e2585 : ℝ := e2565 - e2583

def e2586 : ℝ := e2585 / e2570

def e2587 : ℝ := e2586 ^ 2

def e2588 : ℝ := e9 * e2587

def e2589 : ℝ := e2583 ^ 3

def e2590 : ℝ := e2573 * e2589

def e2591 : ℝ := e2588 + e2590

def e2592 : ℝ := min e2584 e2591

def e2593 : ℝ := (71 / 50 : ℝ)

def e2594 : ℝ := e2593 / e0

def e2595 : ℝ := e2593 * e7

def e2596 : ℝ := e8 * e2593

def e2597 : ℝ := e2596 / e0

def e2598 : ℝ := e2593 ^ 2

def e2599 : ℝ := e17 * e2598

def e2600 : ℝ := e2599 / e0

def e2601 : ℝ := e5 + e2600

def e2602 : ℝ := Real.sqrt e2601

def e2603 : ℝ := e5 + e2602

def e2604 : ℝ := e23 / e2603

def e2605 : ℝ := e9 * e2604

def e2606 : ℝ := e2597 + e2605

def e2607 : ℝ := e2606 - e5

def e2608 : ℝ := e0 / e2598

def e2609 : ℝ := e2594 ^ 2

def e2610 : ℝ := e5 - e2609

def e2611 : ℝ := Real.sqrt e2610

def e2612 : ℝ := e29 - e2611

def e2613 : ℝ := e2611 ^ 3

def e2614 : ℝ := e2613 / e35

def e2615 : ℝ := e2612 + e2614

def e2616 : ℝ := e8 * e2615

def e2617 : ℝ := e2609 / e2611

def e2618 : ℝ := e2617 - e23

def e2619 : ℝ := e23 * e2611

def e2620 : ℝ := e2618 + e2619

def e2621 : ℝ := e2620 / e43

def e2622 : ℝ := e2616 - e2621

def e2623 : ℝ := e2608 * e2622

def e2624 : ℝ := e2607 + e2623

def e2625 : ℝ := e2595 ^ 2

def e2626 : ℝ := e5 - e2625

def e2627 : ℝ := Real.sqrt e2626

def e2628 : ℝ := e5 + e2627

def e2629 : ℝ := e2595 / e2628

def e2630 : ℝ := e2629 ^ 2

def e2631 : ℝ := e5 + e2630

def e2632 : ℝ := Real.sqrt e2631

def e2633 : ℝ := e5 + e2632

def e2634 : ℝ := e2629 / e2633

def e2635 : ℝ := Real.arcsin e2595

def e2636 : ℝ := e59 * e2635

def e2637 : ℝ := e61 * e2595

def e2638 : ℝ := e2637 * e2627

def e2639 : ℝ := e2636 - e2638

def e2640 : ℝ := e43 * e2627

def e2641 : ℝ := e2595 / e2640

def e2642 : ℝ := e2639 - e2641

def e2643 : ℝ := e5 + e2611

def e2644 : ℝ := e2594 / e2643

def e2645 : ℝ := e2644 ^ 2

def e2646 : ℝ := e5 + e2645

def e2647 : ℝ := Real.sqrt e2646

def e2648 : ℝ := e5 + e2647

def e2649 : ℝ := e2644 / e2648

def e2650 : ℝ := Real.arcsin e2594

def e2651 : ℝ := e59 * e2650

def e2652 : ℝ := e61 * e2594

def e2653 : ℝ := e2652 * e2611

def e2654 : ℝ := e2651 - e2653

def e2655 : ℝ := e43 * e2611

def e2656 : ℝ := e2594 / e2655

def e2657 : ℝ := e2654 - e2656

def e2658 : ℝ := e2642 - e2657

def e2659 : ℝ := e2658 / e2593

def e2660 : ℝ := e2624 + e2659

def e2661 : ℝ := e2595 + e4

def e2662 : ℝ := e2661 / e23

def e2663 : ℝ := e2595 / e2593

def e2664 : ℝ := e89 * e2663

def e2665 : ℝ := e2663 ^ 2

def e2666 : ℝ := e91 * e2665

def e2667 : ℝ := e5 + e2666

def e2668 : ℝ := Real.sqrt e2667

def e2669 : ℝ := e2664 * e2668

def e2670 : ℝ := e97 * e2665

def e2671 : ℝ := e2669 - e2670

def e2672 : ℝ := e2662 * e2671

def e2673 : ℝ := e2662 / e2593

def e2674 : ℝ := e89 * e2673

def e2675 : ℝ := e2673 ^ 2

def e2676 : ℝ := e91 * e2675

def e2677 : ℝ := e5 + e2676

def e2678 : ℝ := Real.sqrt e2677

def e2679 : ℝ := e2674 * e2678

def e2680 : ℝ := e97 * e2675

def e2681 : ℝ := e2679 - e2680

def e2682 : ℝ := e2595 * e2681

def e2683 : ℝ := e2672 - e2682

def e2684 : ℝ := e2662 ^ 2

def e2685 : ℝ := e8 * e2684

def e2686 : ℝ := e5 - e2685

def e2687 : ℝ := e5 - e2684

def e2688 : ℝ := Real.sqrt e2687

def e2689 : ℝ := e2686 / e2688

def e2690 : ℝ := e5 - e2689

def e2691 : ℝ := e8 * e2625

def e2692 : ℝ := e5 - e2691

def e2693 : ℝ := e2692 / e2627

def e2694 : ℝ := e5 - e2693

def e2695 : ℝ := e2690 - e2694

def e2696 : ℝ := e2683 * e2695

def e2697 : ℝ := e2681 - e2671

def e2698 : ℝ := e5 + e2688

def e2699 : ℝ := e2662 / e2698

def e2700 : ℝ := e2699 ^ 2

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2701To2920
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e2701 : ℝ := e5 + e2700

def e2702 : ℝ := Real.sqrt e2701

def e2703 : ℝ := e5 + e2702

def e2704 : ℝ := e2699 / e2703

def e2705 : ℝ := Real.arcsin e2662

def e2706 : ℝ := e59 * e2705

def e2707 : ℝ := e61 * e2662

def e2708 : ℝ := e2707 * e2688

def e2709 : ℝ := e2706 - e2708

def e2710 : ℝ := e43 * e2688

def e2711 : ℝ := e2662 / e2710

def e2712 : ℝ := e2709 - e2711

def e2713 : ℝ := e2712 - e2642

def e2714 : ℝ := e2697 * e2713

def e2715 : ℝ := e2696 + e2714

def e2716 : ℝ := e2662 - e2595

def e2717 : ℝ := e2715 / e2716

def e2718 : ℝ := e2660 + e2717

def e2719 : ℝ := e4 * e2681

def e2720 : ℝ := e4 / e2593

def e2721 : ℝ := e89 * e2720

def e2722 : ℝ := e2720 ^ 2

def e2723 : ℝ := e91 * e2722

def e2724 : ℝ := e5 + e2723

def e2725 : ℝ := Real.sqrt e2724

def e2726 : ℝ := e2721 * e2725

def e2727 : ℝ := e97 * e2722

def e2728 : ℝ := e2726 - e2727

def e2729 : ℝ := e2662 * e2728

def e2730 : ℝ := e2719 - e2729

def e2731 : ℝ := e165 - e2690

def e2732 : ℝ := e2730 * e2731

def e2733 : ℝ := e2728 - e2681

def e2734 : ℝ := e183 - e2712

def e2735 : ℝ := e2733 * e2734

def e2736 : ℝ := e2732 + e2735

def e2737 : ℝ := e4 - e2662

def e2738 : ℝ := e2736 / e2737

def e2739 : ℝ := e2718 + e2738

def e2740 : ℝ := e924 / e2593

def e2741 : ℝ := min e7 e2740

def e2742 : ℝ := e2741 - e5

def e2743 : ℝ := e23 * e2593

def e2744 : ℝ := e2743 * e2604

def e2745 : ℝ := e2744 / e0

def e2746 : ℝ := e2742 + e2745

def e2747 : ℝ := e23 * e2598

def e2748 : ℝ := e2747 * e2604

def e2749 : ℝ := e0 + e2748

def e2750 : ℝ := Real.sqrt e2749

def e2751 : ℝ := e932 * e2750

def e2752 : ℝ := e2593 ^ 3

def e2753 : ℝ := e939 * e2752

def e2754 : ℝ := min e2753 e941

def e2755 : ℝ := e23 * e2746

def e2756 : ℝ := e944 * e2754

def e2757 : ℝ := e2751 ^ 2

def e2758 : ℝ := e2756 * e2757

def e2759 : ℝ := e2758 * e2746

def e2760 : ℝ := e2759 / e9

def e2761 : ℝ := e5 + e2760

def e2762 : ℝ := Real.sqrt e2761

def e2763 : ℝ := e5 + e2762

def e2764 : ℝ := e2755 / e2763

def e2765 : ℝ := e2754 * e954

def e2766 : ℝ := e2746 - e2764

def e2767 : ℝ := e2766 / e2751

def e2768 : ℝ := e2767 ^ 2

def e2769 : ℝ := e9 * e2768

def e2770 : ℝ := e2764 ^ 3

def e2771 : ℝ := e2754 * e2770

def e2772 : ℝ := e2769 + e2771

def e2773 : ℝ := min e2765 e2772

def e2774 : ℝ := (73 / 50 : ℝ)

def e2775 : ℝ := e2774 / e0

def e2776 : ℝ := e8 * e2774

def e2777 : ℝ := e2776 / e0

def e2778 : ℝ := e2774 ^ 2

def e2779 : ℝ := e17 * e2778

def e2780 : ℝ := e2779 / e0

def e2781 : ℝ := e5 + e2780

def e2782 : ℝ := Real.sqrt e2781

def e2783 : ℝ := e5 + e2782

def e2784 : ℝ := e23 / e2783

def e2785 : ℝ := e9 * e2784

def e2786 : ℝ := e2777 + e2785

def e2787 : ℝ := e2786 - e5

def e2788 : ℝ := e0 / e2778

def e2789 : ℝ := e2775 ^ 2

def e2790 : ℝ := e5 - e2789

def e2791 : ℝ := Real.sqrt e2790

def e2792 : ℝ := e29 - e2791

def e2793 : ℝ := e2791 ^ 3

def e2794 : ℝ := e2793 / e35

def e2795 : ℝ := e2792 + e2794

def e2796 : ℝ := e8 * e2795

def e2797 : ℝ := e2789 / e2791

def e2798 : ℝ := e2797 - e23

def e2799 : ℝ := e23 * e2791

def e2800 : ℝ := e2798 + e2799

def e2801 : ℝ := e2800 / e43

def e2802 : ℝ := e2796 - e2801

def e2803 : ℝ := e2788 * e2802

def e2804 : ℝ := e2787 + e2803

def e2805 : ℝ := e5 + e2791

def e2806 : ℝ := e2775 / e2805

def e2807 : ℝ := e2806 ^ 2

def e2808 : ℝ := e5 + e2807

def e2809 : ℝ := Real.sqrt e2808

def e2810 : ℝ := e5 + e2809

def e2811 : ℝ := e2806 / e2810

def e2812 : ℝ := Real.arcsin e2775

def e2813 : ℝ := e59 * e2812

def e2814 : ℝ := e61 * e2775

def e2815 : ℝ := e2814 * e2791

def e2816 : ℝ := e2813 - e2815

def e2817 : ℝ := e43 * e2791

def e2818 : ℝ := e2775 / e2817

def e2819 : ℝ := e2816 - e2818

def e2820 : ℝ := e183 - e2819

def e2821 : ℝ := e2820 / e2774

def e2822 : ℝ := e2804 + e2821

def e2823 : ℝ := e924 / e2774

def e2824 : ℝ := min e7 e2823

def e2825 : ℝ := e2824 - e5

def e2826 : ℝ := e23 * e2774

def e2827 : ℝ := e2826 * e2784

def e2828 : ℝ := e2827 / e0

def e2829 : ℝ := e2825 + e2828

def e2830 : ℝ := e23 * e2778

def e2831 : ℝ := e2830 * e2784

def e2832 : ℝ := e0 + e2831

def e2833 : ℝ := Real.sqrt e2832

def e2834 : ℝ := e932 * e2833

def e2835 : ℝ := e2774 ^ 3

def e2836 : ℝ := e939 * e2835

def e2837 : ℝ := min e2836 e941

def e2838 : ℝ := e23 * e2829

def e2839 : ℝ := e944 * e2837

def e2840 : ℝ := e2834 ^ 2

def e2841 : ℝ := e2839 * e2840

def e2842 : ℝ := e2841 * e2829

def e2843 : ℝ := e2842 / e9

def e2844 : ℝ := e5 + e2843

def e2845 : ℝ := Real.sqrt e2844

def e2846 : ℝ := e5 + e2845

def e2847 : ℝ := e2838 / e2846

def e2848 : ℝ := e2837 * e954

def e2849 : ℝ := e2829 - e2847

def e2850 : ℝ := e2849 / e2834

def e2851 : ℝ := e2850 ^ 2

def e2852 : ℝ := e9 * e2851

def e2853 : ℝ := e2847 ^ 3

def e2854 : ℝ := e2837 * e2853

def e2855 : ℝ := e2852 + e2854

def e2856 : ℝ := min e2848 e2855

def e2857 : ℝ := (3 / 2 : ℝ)

def e2858 : ℝ := e2857 / e0

def e2859 : ℝ := e8 * e2857

def e2860 : ℝ := e2859 / e0

def e2861 : ℝ := e2857 ^ 2

def e2862 : ℝ := e17 * e2861

def e2863 : ℝ := e2862 / e0

def e2864 : ℝ := e5 + e2863

def e2865 : ℝ := Real.sqrt e2864

def e2866 : ℝ := e5 + e2865

def e2867 : ℝ := e23 / e2866

def e2868 : ℝ := e9 * e2867

def e2869 : ℝ := e2860 + e2868

def e2870 : ℝ := e2869 - e5

def e2871 : ℝ := e0 / e2861

def e2872 : ℝ := e2858 ^ 2

def e2873 : ℝ := e5 - e2872

def e2874 : ℝ := Real.sqrt e2873

def e2875 : ℝ := e29 - e2874

def e2876 : ℝ := e2874 ^ 3

def e2877 : ℝ := e2876 / e35

def e2878 : ℝ := e2875 + e2877

def e2879 : ℝ := e8 * e2878

def e2880 : ℝ := e2872 / e2874

def e2881 : ℝ := e2880 - e23

def e2882 : ℝ := e23 * e2874

def e2883 : ℝ := e2881 + e2882

def e2884 : ℝ := e2883 / e43

def e2885 : ℝ := e2879 - e2884

def e2886 : ℝ := e2871 * e2885

def e2887 : ℝ := e2870 + e2886

def e2888 : ℝ := e5 + e2874

def e2889 : ℝ := e2858 / e2888

def e2890 : ℝ := e2889 ^ 2

def e2891 : ℝ := e5 + e2890

def e2892 : ℝ := Real.sqrt e2891

def e2893 : ℝ := e5 + e2892

def e2894 : ℝ := e2889 / e2893

def e2895 : ℝ := Real.arcsin e2858

def e2896 : ℝ := e59 * e2895

def e2897 : ℝ := e61 * e2858

def e2898 : ℝ := e2897 * e2874

def e2899 : ℝ := e2896 - e2898

def e2900 : ℝ := e43 * e2874

def e2901 : ℝ := e2858 / e2900

def e2902 : ℝ := e2899 - e2901

def e2903 : ℝ := e183 - e2902

def e2904 : ℝ := e2903 / e2857

def e2905 : ℝ := e2887 + e2904

def e2906 : ℝ := e924 / e2857

def e2907 : ℝ := min e7 e2906

def e2908 : ℝ := e2907 - e5

def e2909 : ℝ := e23 * e2857

def e2910 : ℝ := e2909 * e2867

def e2911 : ℝ := e2910 / e0

def e2912 : ℝ := e2908 + e2911

def e2913 : ℝ := e23 * e2861

def e2914 : ℝ := e2913 * e2867

def e2915 : ℝ := e0 + e2914

def e2916 : ℝ := Real.sqrt e2915

def e2917 : ℝ := e932 * e2916

def e2918 : ℝ := e2857 ^ 3

def e2919 : ℝ := e939 * e2918

def e2920 : ℝ := min e2919 e941

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2921To3142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting

def e2921 : ℝ := e23 * e2912

def e2922 : ℝ := e944 * e2920

def e2923 : ℝ := e2917 ^ 2

def e2924 : ℝ := e2922 * e2923

def e2925 : ℝ := e2924 * e2912

def e2926 : ℝ := e2925 / e9

def e2927 : ℝ := e5 + e2926

def e2928 : ℝ := Real.sqrt e2927

def e2929 : ℝ := e5 + e2928

def e2930 : ℝ := e2921 / e2929

def e2931 : ℝ := e2920 * e954

def e2932 : ℝ := e2912 - e2930

def e2933 : ℝ := e2932 / e2917

def e2934 : ℝ := e2933 ^ 2

def e2935 : ℝ := e9 * e2934

def e2936 : ℝ := e2930 ^ 3

def e2937 : ℝ := e2920 * e2936

def e2938 : ℝ := e2935 + e2937

def e2939 : ℝ := min e2931 e2938

def e2940 : ℝ := (77 / 50 : ℝ)

def e2941 : ℝ := e2940 / e0

def e2942 : ℝ := e8 * e2940

def e2943 : ℝ := e2942 / e0

def e2944 : ℝ := e2940 ^ 2

def e2945 : ℝ := e17 * e2944

def e2946 : ℝ := e2945 / e0

def e2947 : ℝ := e5 + e2946

def e2948 : ℝ := Real.sqrt e2947

def e2949 : ℝ := e5 + e2948

def e2950 : ℝ := e23 / e2949

def e2951 : ℝ := e9 * e2950

def e2952 : ℝ := e2943 + e2951

def e2953 : ℝ := e2952 - e5

def e2954 : ℝ := e0 / e2944

def e2955 : ℝ := e2941 ^ 2

def e2956 : ℝ := e5 - e2955

def e2957 : ℝ := Real.sqrt e2956

def e2958 : ℝ := e29 - e2957

def e2959 : ℝ := e2957 ^ 3

def e2960 : ℝ := e2959 / e35

def e2961 : ℝ := e2958 + e2960

def e2962 : ℝ := e8 * e2961

def e2963 : ℝ := e2955 / e2957

def e2964 : ℝ := e2963 - e23

def e2965 : ℝ := e23 * e2957

def e2966 : ℝ := e2964 + e2965

def e2967 : ℝ := e2966 / e43

def e2968 : ℝ := e2962 - e2967

def e2969 : ℝ := e2954 * e2968

def e2970 : ℝ := e2953 + e2969

def e2971 : ℝ := e5 + e2957

def e2972 : ℝ := e2941 / e2971

def e2973 : ℝ := e2972 ^ 2

def e2974 : ℝ := e5 + e2973

def e2975 : ℝ := Real.sqrt e2974

def e2976 : ℝ := e5 + e2975

def e2977 : ℝ := e2972 / e2976

def e2978 : ℝ := Real.arcsin e2941

def e2979 : ℝ := e59 * e2978

def e2980 : ℝ := e61 * e2941

def e2981 : ℝ := e2980 * e2957

def e2982 : ℝ := e2979 - e2981

def e2983 : ℝ := e43 * e2957

def e2984 : ℝ := e2941 / e2983

def e2985 : ℝ := e2982 - e2984

def e2986 : ℝ := e183 - e2985

def e2987 : ℝ := e2986 / e2940

def e2988 : ℝ := e2970 + e2987

def e2989 : ℝ := e924 / e2940

def e2990 : ℝ := min e7 e2989

def e2991 : ℝ := e2990 - e5

def e2992 : ℝ := e23 * e2940

def e2993 : ℝ := e2992 * e2950

def e2994 : ℝ := e2993 / e0

def e2995 : ℝ := e2991 + e2994

def e2996 : ℝ := e23 * e2944

def e2997 : ℝ := e2996 * e2950

def e2998 : ℝ := e0 + e2997

def e2999 : ℝ := Real.sqrt e2998

def e3000 : ℝ := e932 * e2999

def e3001 : ℝ := e2940 ^ 3

def e3002 : ℝ := e939 * e3001

def e3003 : ℝ := min e3002 e941

def e3004 : ℝ := e23 * e2995

def e3005 : ℝ := e944 * e3003

def e3006 : ℝ := e3000 ^ 2

def e3007 : ℝ := e3005 * e3006

def e3008 : ℝ := e3007 * e2995

def e3009 : ℝ := e3008 / e9

def e3010 : ℝ := e5 + e3009

def e3011 : ℝ := Real.sqrt e3010

def e3012 : ℝ := e5 + e3011

def e3013 : ℝ := e3004 / e3012

def e3014 : ℝ := e3003 * e954

def e3015 : ℝ := e2995 - e3013

def e3016 : ℝ := e3015 / e3000

def e3017 : ℝ := e3016 ^ 2

def e3018 : ℝ := e9 * e3017

def e3019 : ℝ := e3013 ^ 3

def e3020 : ℝ := e3003 * e3019

def e3021 : ℝ := e3018 + e3020

def e3022 : ℝ := min e3014 e3021

def e3023 : ℝ := (79 / 50 : ℝ)

def e3024 : ℝ := e3023 / e0

def e3025 : ℝ := e8 * e3023

def e3026 : ℝ := e3025 / e0

def e3027 : ℝ := e3023 ^ 2

def e3028 : ℝ := e17 * e3027

def e3029 : ℝ := e3028 / e0

def e3030 : ℝ := e5 + e3029

def e3031 : ℝ := Real.sqrt e3030

def e3032 : ℝ := e5 + e3031

def e3033 : ℝ := e23 / e3032

def e3034 : ℝ := e9 * e3033

def e3035 : ℝ := e3026 + e3034

def e3036 : ℝ := e3035 - e5

def e3037 : ℝ := e0 / e3027

def e3038 : ℝ := e3024 ^ 2

def e3039 : ℝ := e5 - e3038

def e3040 : ℝ := Real.sqrt e3039

def e3041 : ℝ := e29 - e3040

def e3042 : ℝ := e3040 ^ 3

def e3043 : ℝ := e3042 / e35

def e3044 : ℝ := e3041 + e3043

def e3045 : ℝ := e8 * e3044

def e3046 : ℝ := e3038 / e3040

def e3047 : ℝ := e3046 - e23

def e3048 : ℝ := e23 * e3040

def e3049 : ℝ := e3047 + e3048

def e3050 : ℝ := e3049 / e43

def e3051 : ℝ := e3045 - e3050

def e3052 : ℝ := e3037 * e3051

def e3053 : ℝ := e3036 + e3052

def e3054 : ℝ := e5 + e3040

def e3055 : ℝ := e3024 / e3054

def e3056 : ℝ := e3055 ^ 2

def e3057 : ℝ := e5 + e3056

def e3058 : ℝ := Real.sqrt e3057

def e3059 : ℝ := e5 + e3058

def e3060 : ℝ := e3055 / e3059

def e3061 : ℝ := Real.arcsin e3024

def e3062 : ℝ := e59 * e3061

def e3063 : ℝ := e61 * e3024

def e3064 : ℝ := e3063 * e3040

def e3065 : ℝ := e3062 - e3064

def e3066 : ℝ := e43 * e3040

def e3067 : ℝ := e3024 / e3066

def e3068 : ℝ := e3065 - e3067

def e3069 : ℝ := e183 - e3068

def e3070 : ℝ := e3069 / e3023

def e3071 : ℝ := e3053 + e3070

def e3072 : ℝ := e924 / e3023

def e3073 : ℝ := min e7 e3072

def e3074 : ℝ := e3073 - e5

def e3075 : ℝ := e23 * e3023

def e3076 : ℝ := e3075 * e3033

def e3077 : ℝ := e3076 / e0

def e3078 : ℝ := e3074 + e3077

def e3079 : ℝ := e23 * e3027

def e3080 : ℝ := e3079 * e3033

def e3081 : ℝ := e0 + e3080

def e3082 : ℝ := Real.sqrt e3081

def e3083 : ℝ := e932 * e3082

def e3084 : ℝ := e3023 ^ 3

def e3085 : ℝ := e939 * e3084

def e3086 : ℝ := min e3085 e941

def e3087 : ℝ := e23 * e3078

def e3088 : ℝ := e944 * e3086

def e3089 : ℝ := e3083 ^ 2

def e3090 : ℝ := e3088 * e3089

def e3091 : ℝ := e3090 * e3078

def e3092 : ℝ := e3091 / e9

def e3093 : ℝ := e5 + e3092

def e3094 : ℝ := Real.sqrt e3093

def e3095 : ℝ := e5 + e3094

def e3096 : ℝ := e3087 / e3095

def e3097 : ℝ := e3086 * e954

def e3098 : ℝ := e3078 - e3096

def e3099 : ℝ := e3098 / e3083

def e3100 : ℝ := e3099 ^ 2

def e3101 : ℝ := e9 * e3100

def e3102 : ℝ := e3096 ^ 3

def e3103 : ℝ := e3086 * e3102

def e3104 : ℝ := e3101 + e3103

def e3105 : ℝ := min e3097 e3104

def e3106 : ℝ := (81 / 50 : ℝ)

def e3107 : ℝ := e3106 / e0

def e3108 : ℝ := e8 * e3106

def e3109 : ℝ := e3108 / e0

def e3110 : ℝ := e3106 ^ 2

def e3111 : ℝ := e17 * e3110

def e3112 : ℝ := e3111 / e0

def e3113 : ℝ := e5 + e3112

def e3114 : ℝ := Real.sqrt e3113

def e3115 : ℝ := e5 + e3114

def e3116 : ℝ := e23 / e3115

def e3117 : ℝ := e9 * e3116

def e3118 : ℝ := e3109 + e3117

def e3119 : ℝ := e3118 - e5

def e3120 : ℝ := e0 / e3110

def e3121 : ℝ := e3107 ^ 2

def e3122 : ℝ := e5 - e3121

def e3123 : ℝ := Real.sqrt e3122

def e3124 : ℝ := e29 - e3123

def e3125 : ℝ := e3123 ^ 3

def e3126 : ℝ := e3125 / e35

def e3127 : ℝ := e3124 + e3126

def e3128 : ℝ := e8 * e3127

def e3129 : ℝ := e3121 / e3123

def e3130 : ℝ := e3129 - e23

def e3131 : ℝ := e23 * e3123

def e3132 : ℝ := e3130 + e3131

def e3133 : ℝ := e3132 / e43

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end


