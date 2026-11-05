-- Prove2me | Definitions.Def_CKSEndReplacementSupport
-- name    : CKSEndReplacementSupport
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T14:35:52.342713+00:00
-- url     : https://prove2.me/theorems/31d19935-fb0f-462c-b7ff-9e89245ceb8c
-- title:
--   CKS end replacement: supporting definitions and lemmas
-- statement:
--   Supporting Lean development for the area-controlled end replacement theorem in the CKS class. It contains the definitions on which the published child theorems of `OAI.CKSSourceExterior.area_controlled_end_replacement` state their results, beyond those in `Definitions.Def_CKSBondiPenrose`: the jets and raw null inputs of the collar, the collar and outer data, the heat series and bending profiles, the source collar atlases and the replacement metric and tensor. It also contains the theorems those definitions depend on, every lemma tagged with a simplification or `fun_prop` attribute in the source, and all global and local instances, since proofs use those implicitly. Everything is proved here, and no result is assumed.
--
--   **Formalization Note** **Source and credit.** The mathematics and the Lean formalization are OpenAI's: `openai/math` at commit `adc7f12`, preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026), `preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf`, Lean sources under `lean/OAI/Geometry/Relativity/CKS/`, Apache-2.0. The code was carved mechanically from those sources and ported to Lean 4.33.1 and Mathlib `0df444a`. Port changes in this file: upstream's targeted imports and module header are replaced by `import Mathlib` and the platform definitions; comments and declarations not needed here are deleted, and the remaining source modules are concatenated in dependency order, each wrapped in `section ... end`; empty `namespace X end X` pairs at the top register every namespace so that later `open` commands remain valid after carving; anonymous `local instance` declarations receive explicit names so that they can be reactivated; restatements `OAI.ite_eq_left`, `OAI.ite_eq_right`, `OAI.dite_eq_left`, `OAI.dite_eq_right` of `if_pos`, `if_neg`, `dif_pos`, `dif_neg` are added, because Lean 4.34 names used upstream are absent on Lean 4.33.1.
-- source:
--   https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS

import Mathlib
import Definitions.Def_CKSBondiPenrose

set_option linter.all false

namespace OAI
end OAI
namespace OAI.CKSADM
end OAI.CKSADM
namespace OAI.CKSAmbientCalculus
end OAI.CKSAmbientCalculus
namespace OAI.CKSAngularGeometry
end OAI.CKSAngularGeometry
namespace OAI.CKSAngularSlice
end OAI.CKSAngularSlice
namespace OAI.CKSArea
end OAI.CKSArea
namespace OAI.CKSBending
end OAI.CKSBending
namespace OAI.CKSBoundarySurface
end OAI.CKSBoundarySurface
namespace OAI.CKSCalculus
end OAI.CKSCalculus
namespace OAI.CKSCartesianOuter
end OAI.CKSCartesianOuter
namespace OAI.CKSDifferentialSeries
end OAI.CKSDifferentialSeries
namespace OAI.CKSEmbeddingDerivative
end OAI.CKSEmbeddingDerivative
namespace OAI.CKSEnd
end OAI.CKSEnd
namespace OAI.CKSEnd.ConstraintJet
end OAI.CKSEnd.ConstraintJet
namespace OAI.CKSFrame
end OAI.CKSFrame
namespace OAI.CKSFullCutArea
end OAI.CKSFullCutArea
namespace OAI.CKSGeometricCuts
end OAI.CKSGeometricCuts
namespace OAI.CKSInducedArea
end OAI.CKSInducedArea
namespace OAI.CKSInducedSphere
end OAI.CKSInducedSphere
namespace OAI.CKSIntrinsicConstraints
end OAI.CKSIntrinsicConstraints
namespace OAI.CKSIntrinsicGeometry
end OAI.CKSIntrinsicGeometry
namespace OAI.CKSIntrinsicTopology
end OAI.CKSIntrinsicTopology
namespace OAI.CKSIntrinsicVolume
end OAI.CKSIntrinsicVolume
namespace OAI.CKSLeafCalculus
end OAI.CKSLeafCalculus
namespace OAI.CKSLocalBending
end OAI.CKSLocalBending
namespace OAI.CKSLorentz
end OAI.CKSLorentz
namespace OAI.CKSLorentz.SmoothAngularPatch
end OAI.CKSLorentz.SmoothAngularPatch
namespace OAI.CKSMain
end OAI.CKSMain
namespace OAI.CKSMain.InteriorSurface
end OAI.CKSMain.InteriorSurface
namespace OAI.CKSMetricGluing
end OAI.CKSMetricGluing
namespace OAI.CKSMixedGeometry
end OAI.CKSMixedGeometry
namespace OAI.CKSMixedGeometry.FiniteLogDecay
end OAI.CKSMixedGeometry.FiniteLogDecay
namespace OAI.CKSRealizedRound
end OAI.CKSRealizedRound
namespace OAI.CKSReplacementCompleteness
end OAI.CKSReplacementCompleteness
namespace OAI.CKSRound
end OAI.CKSRound
namespace OAI.CKSRound.LapseJet
end OAI.CKSRound.LapseJet
namespace OAI.CKSRound.MassJet
end OAI.CKSRound.MassJet
namespace OAI.CKSRound.MetricJet
end OAI.CKSRound.MetricJet
namespace OAI.CKSRound.RoundTensor
end OAI.CKSRound.RoundTensor
namespace OAI.CKSSchwarzschild
end OAI.CKSSchwarzschild
namespace OAI.CKSSourceExterior
end OAI.CKSSourceExterior
namespace OAI.CKSSpatialManifold
end OAI.CKSSpatialManifold
namespace OAI.CKSSpectralHeat
end OAI.CKSSpectralHeat
namespace OAI.CKSSphericalChart
end OAI.CKSSphericalChart
namespace OAI.CKSSphericalHarmonics
end OAI.CKSSphericalHarmonics
namespace OAI.CKSSurfaceVolume
end OAI.CKSSurfaceVolume
namespace OAI.CKSTailVolume
end OAI.CKSTailVolume
namespace OAI.CKSTangentCoefficients
end OAI.CKSTangentCoefficients
namespace OAI.CKSTensorNaturality
end OAI.CKSTensorNaturality
section
namespace OAI

theorem ite_eq_left {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {c : Prop} {_ : Decidable c} (hc : c) {α : Sort*} {t : c → α} {e : ¬c → α} :
    (dite c t e) = t hc := dif_pos hc
theorem dite_eq_right {c : Prop} {_ : Decidable c} (hc : ¬c) {α : Sort*} {t : c → α} {e : ¬c → α} :
    (dite c t e) = e hc := dif_neg hc

end OAI
end

section
noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology InnerProductSpace
open CKSSchwarzschild
attribute [local instance] manifold_regular
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
attribute [local instance] CKSSpatialManifold.real_id_isometric CKSLorentz.real_smulCommClass CKSLorentz.spatialDual_smulCommClass

local instance atlas_manifold_one {N : Type u_1} [TopologicalSpace N] [ChartedSpace OAI.CKSBoundarySurface.H3 N]
    [IsManifold OAI.CKSBoundarySurface.I3 ∞ N] : IsManifold OAI.CKSBoundarySurface.I3 1 N := inferInstance

local instance atlas_tangent_vectorBundle {N : Type u_1} [TopologicalSpace N] [ChartedSpace OAI.CKSBoundarySurface.H3 N]
    [IsManifold OAI.CKSBoundarySurface.I3 ∞ N] :
    letI := OAI.CKSMain.atlas_manifold_one (N := N)
    VectorBundle ℝ OAI.CKSBoundarySurface.E3 (fun x : N => TangentSpace OAI.CKSBoundarySurface.I3 x) := by
  infer_instance

abbrev CoefficientAtlas {N : Type u_1} [TopologicalSpace N] [ChartedSpace OAI.CKSBoundarySurface.H3 N]
    [IsManifold OAI.CKSBoundarySurface.I3 ∞ N] (q : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)) (k : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N)) :=
  letI := OAI.CKSMain.atlas_manifold_one (N := N)
  letI := OAI.CKSMain.atlas_tangent_vectorBundle (N := N)
  let metric : ContMDiffRiemannianMetric OAI.CKSBoundarySurface.I3 ∞ OAI.CKSBoundarySurface.E3 (fun x : N => TangentSpace OAI.CKSBoundarySurface.I3 x) := q
  ∀ x : N, OAI.CKSIntrinsicConstraints.ConstraintChart metric.inner k x

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

structure InteriorSurface (q : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)) (k : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N))
    (A : OAI.CKSMain.CoefficientAtlas q k) (T : Type v) [TopologicalSpace T] [ChartedSpace OAI.CKSBoundarySurface.E2 T]
    [IsManifold OAI.CKSBoundarySurface.I2 ∞ T] where
  map : T → N
  smooth : ContMDiff OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 ∞ map
  embedding : Topology.IsEmbedding map
  immersion : ∀ p, Function.Injective (mfderiv OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 map p)
  interior : ∀ p, map p ∈ OAI.CKSBoundarySurface.I3.interior N
  normal : ∀ p, TangentSpace OAI.CKSBoundarySurface.I3 (map p)
  normal_unit : ∀ p, q.inner (map p) (normal p) (normal p) = 1
  normal_orthogonal : ∀ p a, q.inner (map p) (normal p) (mfderiv OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 map p a) = 0
  normal_smooth : ∀ p, ContMDiffAt OAI.CKSBoundarySurface.I2 𝓘(ℝ,OAI.CKSBoundarySurface.E3) ∞
    (fun t => mfderiv OAI.CKSBoundarySurface.I3 𝓘(ℝ,OAI.CKSBoundarySurface.E3) (A (map p)).coordinate (map t) (normal t)) p

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain.InteriorSurface
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
variable {q : SmoothMetric I3 (M := N)} {k : InnerField I3 (M := N)}
  {A : CoefficientAtlas q k} {T : Type v} [TopologicalSpace T] [ChartedSpace E2 T]
  [IsManifold I2 ∞ T] (D : InteriorSurface q k A T)

end OAI.CKSMain.InteriorSurface
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
attribute [local instance] sixteen_atLeastTwo

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
open CKSSchwarzschild

end OAI.CKSMain
end
end

section
namespace OAI

noncomputable section
open MeasureTheory Set Metric Module
open scoped ENNReal
namespace CKSIntrinsicGeometry
abbrev E3 := EuclideanSpace ℝ (Fin 3)

end CKSIntrinsicGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
namespace CKSIntrinsicVolume

lemma exists_measure_of_compatible {X ι : Type*} [MeasurableSpace X]
    (U : ι → Set X) (hU : ∀ i, MeasurableSet (U i)) (μ : ι → Measure X)
    (hc : ∀ i j, (μ i).restrict (U j) = (μ j).restrict (U i))
    (f : ℕ → ι) (hf : ⋃ n, U (f n) = univ) :
    ∃ ν : Measure X, ∀ i, ν.restrict (U i) = μ i := by
  let D := disjointed (U ∘ f)
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed (fun n => hU (f n))
  refine ⟨Measure.sum (fun n => (μ (f n)).restrict (D n)), fun i => ?_⟩
  rw [Measure.restrict_sum _ (hU i)]
  have heq : ∀ n, ((μ (f n)).restrict (D n)).restrict (U i) = (μ i).restrict (D n) := by
    intro n
    rw [Measure.restrict_comm (hU i), hc (f n) i]
    exact Measure.restrict_restrict_of_subset (disjointed_subset (U ∘ f) n)
  simp_rw [heq]
  rw [← Measure.restrict_iUnion (disjoint_disjointed (U ∘ f)) hD,
    show (⋃ n, D n) = univ from (iUnion_disjointed.trans hf), Measure.restrict_univ]

end CKSIntrinsicVolume

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
abbrev Mat := Matrix I I ℝ
abbrev Jet := Mat × (I → Mat) × (I → I → Mat)
abbrev ScalarJet := ℝ × (I → ℝ) × Mat

def determinant (q : Mat) : ℝ := q 0 0 * q 1 1 - q 0 1 * q 1 0

def inverse (q : Mat) : Mat :=
  fun i j => (!![q 1 1, -q 0 1; -q 1 0, q 0 0] : Mat) i j / determinant q

lemma determinant_eq (q : Mat) : determinant q = q.det := by
  exact (Matrix.det_fin_two q).symm

def christoffel (j : Jet) (a i k : I) : ℝ :=
  (∑ l, inverse j.1 a l * (j.2.1 i k l + j.2.1 k i l - j.2.1 l i k)) / 2

def inverseDerivative (j : Jet) (s a b : I) : ℝ :=
  - ∑ i, ∑ k, inverse j.1 a i * j.2.1 s i k * inverse j.1 k b

def christoffelDerivative (j : Jet) (s a i k : I) : ℝ :=
  (∑ l, (inverseDerivative j s a l * (j.2.1 i k l + j.2.1 k i l - j.2.1 l i k) +
    inverse j.1 a l * (j.2.2 s i k l + j.2.2 s k i l - j.2.2 s l i k))) / 2

def ricci (j : Jet) (i k : I) : ℝ :=
  (∑ a, (christoffelDerivative j a a i k - christoffelDerivative j k a i a)) +
  ∑ a, ∑ b, (christoffel j a a b * christoffel j b i k -
    christoffel j a k b * christoffel j b i a)

def scalarCurvature (j : Jet) : ℝ := ∑ i, ∑ k, inverse j.1 i k * ricci j i k

def lapseLaplacian (j : Jet) (z : ScalarJet) : ℝ :=
  (∑ i, ∑ k, inverse j.1 i k *
    (2 * z.2.1 i * z.2.1 k / z.1^2 - z.2.2 i k / z.1 +
      (∑ a, christoffel j a i k * z.2.1 a) / z.1))

lemma determinant_smooth : ContDiff ℝ ∞ determinant := by
  unfold determinant
  fun_prop

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_mul (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y * g y) x = f x * D e g x + g x * D e f x := by
  simp [D, fderiv_fun_mul hf hg]

lemma D_clm (e x : E) (A : E →L[ℝ] ℝ) : D e A x = A e := by simp [D]

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

end
end CKSCalculus

end

noncomputable section
namespace CKSRound
noncomputable section

namespace MetricJet

end MetricJet

namespace LapseJet

end LapseJet

namespace MetricJet

end MetricJet

namespace RoundTensor

end RoundTensor

structure MassJet where
  F : ℝ
  Fr : ℝ
  Ft : ℝ
  Fp : ℝ
  Frr : ℝ
  Frt : ℝ
  Frp : ℝ
  Ftt : ℝ
  Ftp : ℝ
  Fpp : ℝ

namespace MassJet

def laplace (f : MassJet) (s c : ℝ) : ℝ := f.Ftt + c / s * f.Ft + f.Fpp / s ^ 2

end MassJet

end
end CKSRound

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

def metric (u : Point → ℝ) (x : Point) : Mat :=
  Matrix.diagonal ![1 / u x ^ 2, x 0 ^ 2, x 0 ^ 2 * Real.sin (x 1) ^ 2]

def metricJet (u : Point → ℝ) (x : Point) : MetricJet where
  inv := (metric u x)⁻¹
  d := fun a i j => D (basis a) (fun y => metric u y i j) x
  dd := fun a b i j => D (basis a) (D (basis b) (fun y => metric u y i j)) x

end
end CKSRealizedRound

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound Filter
open scoped Topology ContDiff

def radial (v : ℝ → ℝ) (x : Point) : ℝ := v (x 0)

def massJet (F : Point → ℝ) (x : Point) : MassJet where
  F := F x
  Fr := D (basis 0) F x
  Ft := D (basis 1) F x
  Fp := D (basis 2) F x
  Frr := D (basis 0) (D (basis 0) F) x
  Frt := D (basis 1) (D (basis 0) F) x
  Frp := D (basis 2) (D (basis 0) F) x
  Ftt := D (basis 1) (D (basis 1) F) x
  Ftp := D (basis 2) (D (basis 1) F) x
  Fpp := D (basis 2) (D (basis 2) F) x

def radicand (F : Point → ℝ) (v : ℝ → ℝ) (x : Point) : ℝ :=
  1 + radial v x ^ 2 - 2 * F x / x 0

def lapse (F : Point → ℝ) (v : ℝ → ℝ) (x : Point) : ℝ :=
  Real.sqrt (radicand F v x)

end
end CKSRealizedRound

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound
open scoped Topology ContDiff

def tensor (u : Point → ℝ) (v : ℝ → ℝ) (L a b : Point → ℝ) (x : Point) : Mat :=
  !![L x / u x ^ 2, 0, 0;
    0, radial v x * x 0 + a x, b x;
    0, b x, (radial v x * x 0 - a x) * Real.sin (x 1) ^ 2]

def tensorJet (u : Point → ℝ) (v : ℝ → ℝ) (L a b : Point → ℝ) (x : Point) : TensorJet where
  val := tensor u v L a b x
  d := fun d i j => D (basis d) (fun y => tensor u v L a b y i j) x

end
end CKSRealizedRound

end

noncomputable section
namespace CKSBending
noncomputable section

abbrev Vec2 := WithLp 2 (ℝ × ℝ)

def A (v : ℝ) : ℝ := 1 + v ^ 2

end
end CKSBending

end

noncomputable section
namespace CKSLocalBending
noncomputable section
open CKSRound CKSBending

def sphereGrad (f : MassJet) (s : ℝ) : Vec2 :=
  WithLp.toLp 2 (f.Ft, f.Fp / s)

end
end CKSLocalBending

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound CKSLocalBending CKSBending
open scoped Topology ContDiff

def normalEntry (v β : ℝ → ℝ) (r : ℝ) : ℝ := deriv v r + β r / r ^ 2

def correctionCoeff (v : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * (deriv v r - v r / r) / (1 + v r ^ 2)

def correctedComponent (v : ℝ → ℝ) (a : Point → ℝ) (x : Point) : ℝ :=
  correctionCoeff v (x 0) * a x

end
end CKSRealizedRound

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
def actualJet (q : Point → Mat) (x : Point) : Jet :=
  (q x, (fun a i k => D (basis a) (fun y => q y i k) x),
    fun a b i k => D (basis a) (D (basis b) (fun y => q y i k)) x)

def actualScalarJet (z : Point → ℝ) (x : Point) : ScalarJet :=
  (z x, (fun a => D (basis a) z x), fun a b => D (basis a) (D (basis b) z) x)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def rescale (c : ℝ) (j : Jet) : Jet :=
  (fun i k => c*j.1 i k, (fun s i k => c*j.2.1 s i k), fun s t i k => c*j.2.2 s t i k)

lemma inverse_rescale (c : ℝ) (j : Jet) (hc : c ≠ 0) (i k : I) :
    inverse (rescale c j).1 i k = inverse j.1 i k / c := by
  have heq : determinant (rescale c j).1 = c^2*determinant j.1 := by
    dsimp [rescale,determinant]
    ring
  simp only [inverse,heq]
  fin_cases i <;> fin_cases k <;> dsimp [rescale] <;> field_simp

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def reciprocalJet (z : ScalarJet) : ScalarJet :=
  (1/z.1, (fun a => -z.2.1 a/z.1^2), fun a b =>
    2*z.2.1 a*z.2.1 b/z.1^3-z.2.2 a b/z.1^2)

end
end CKSAngularGeometry

end

end OAI
end

section
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
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def constantJet (c : ℝ) : ScalarJet := (c,0,0)

def productJet (f g : ScalarJet) : ScalarJet :=
  (f.1*g.1, (fun a => f.1*g.2.1 a+g.1*f.2.1 a), fun a b =>
    f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)

def sqrtJet (f : ScalarJet) : ScalarJet :=
  (Real.sqrt f.1, (fun a => f.2.1 a/(2*Real.sqrt f.1)), fun a b =>
    f.2.2 a b/(2*Real.sqrt f.1)-f.2.1 a*f.2.1 b/(4*Real.sqrt f.1^3))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev MatrixScalarJet := Matrix I I ScalarJet

def matrixScalarJets (q : Point → Mat) (x : Point) : MatrixScalarJet :=
  fun i k => actualScalarJet (fun y => q y i k) x

def determinantJet (q : MatrixScalarJet) : ScalarJet :=
  productJet (q 0 0) (q 1 1)-productJet (q 0 1) (q 1 0)

def inverseMatrixJet (q : MatrixScalarJet) (i k : I) : ScalarJet :=
  productJet ((!![q 1 1, -q 0 1; -q 1 0, q 0 0] : MatrixScalarJet) i k)
    (reciprocalJet (determinantJet q))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev ExpansionInput := MatrixScalarJet × (I → MatrixScalarJet) × MatrixScalarJet ×
  (I → ScalarJet) × (I → I → ScalarJet)

def normalizedLieJet (j : ExpansionInput) (i k : I) : ScalarJet := ∑ a,
  (productJet (j.2.2.2.1 a) (j.2.1 a i k)+
    productJet (j.1 a k) (j.2.2.2.2 i a)+productJet (j.1 i a) (j.2.2.2.2 k a))

def normalizedLie (q : Point → Mat) (S : Point → Point) (x : Point) (i k : I) : ℝ := ∑ a,
  (S x a*D (basis a) (fun y => q y i k) x+
    q x a k*D (basis i) (fun y => S y a) x+q x i a*D (basis k) (fun y => S y a) x)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_trace (q : Mat) (hq : determinant q ≠ 0) :
    (∑ i, ∑ k, inverse q i k * q k i) = 2 := by
  simp only [Fin.sum_univ_two,inverse]
  field_simp
  dsimp [determinant] at *
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev Mat := Matrix A A ℝ
abbrev ScalarJet := ℝ × (I → ℝ) × (I → I → ℝ)
def actualScalarJet (f : Point → ℝ) (x : Point) : ScalarJet :=
  (f x,fun a => D (basis a) f x,fun a b => D (basis a) (D (basis b) f) x)

def constantJet (c : ℝ) : ScalarJet := (c,0,0)

def productJet (f g : ScalarJet) : ScalarJet :=
  (f.1*g.1, (fun a => f.1*g.2.1 a+g.1*f.2.1 a), fun a b =>
    f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)

def reciprocalJet (z : ScalarJet) : ScalarJet :=
  (1/z.1, (fun a => -z.2.1 a/z.1^2), fun a b =>
    2*z.2.1 a*z.2.1 b/z.1^3-z.2.2 a b/z.1^2)

lemma productJet_smooth : ContDiff ℝ ∞ (fun j : ScalarJet × ScalarJet => productJet j.1 j.2) := by
  unfold productJet
  fun_prop

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev ScalarThreeJet := ScalarJet × (I → ScalarJet)
def actualThreeJet (f : Point → ℝ) (x : Point) : ScalarThreeJet :=
  (actualScalarJet f x,fun a => actualScalarJet (D (basis a) f) x)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev MatrixThreeJet := Matrix I I ScalarThreeJet

def matrixThreeJets (q : Point → Mat) (x : Point) : MatrixThreeJet :=
  fun i k => actualThreeJet (fun y => q y i k) x

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev ScalarThreeJet := ScalarJet × (I → ScalarJet)
def actualThreeJet (f : Point → ℝ) (x : Point) : ScalarThreeJet :=
  (actualScalarJet f x,fun a => actualScalarJet (D (basis a) f) x)
def constantThreeJet (c : ℝ) : ScalarThreeJet := (constantJet c,0)
def productThreeJet (f g : ScalarThreeJet) : ScalarThreeJet :=
  (productJet f.1 g.1,fun a => productJet f.1 (g.2 a)+productJet g.1 (f.2 a))
def reciprocalThreeJet (f : ScalarThreeJet) : ScalarThreeJet :=
  (reciprocalJet f.1,fun a => -productJet (productJet (reciprocalJet f.1) (reciprocalJet f.1)) (f.2 a))

lemma productThreeJet_smooth : ContDiff ℝ ∞ (fun j : ScalarThreeJet × ScalarThreeJet => productThreeJet j.1 j.2) := by
  unfold productThreeJet
  apply ContDiff.prodMk
  · exact productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : ScalarThreeJet × ScalarThreeJet => (j.1.1,j.2.1)))
  apply contDiff_pi.mpr
  intro a
  exact (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : ScalarThreeJet × ScalarThreeJet => (j.1.1,j.2.2 a)))).add
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : ScalarThreeJet × ScalarThreeJet => (j.2.1,j.1.2 a))))

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff

def sqrtJet (f : ScalarJet) : ScalarJet :=
  (Real.sqrt f.1, (fun a => f.2.1 a/(2*Real.sqrt f.1)), fun a b =>
    f.2.2 a b/(2*Real.sqrt f.1)-f.2.1 a*f.2.1 b/(4*Real.sqrt f.1^3))

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

def phi (x : ℝ) : ℝ :=
  (1 - Real.smoothTransition ((x-6)/6)) + Real.smoothTransition ((x-6)/6) * (x⁻¹)^3

def xi (x : ℝ) : ℝ := 1 - Real.smoothTransition (x-1)
def zeta (x : ℝ) : ℝ := Real.smoothTransition (x-4)
def beta (x : ℝ) : ℝ := 1 - Real.smoothTransition (2*x-7)

def bendingV (R r : ℝ) : ℝ := r * phi (r/R) * xi (r/R^2)
def bendingZeta (R r : ℝ) : ℝ := zeta (r/R)
def bendingBeta (R r : ℝ) : ℝ := beta (r/R)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev MatrixScalarJet := Matrix A A ScalarJet

def matrixScalarJets (q : Point → Mat) (x : Point) : MatrixScalarJet :=
  fun i k => actualScalarJet (fun y => q y i k) x

def determinantJet (q : MatrixScalarJet) : ScalarJet :=
  productJet (q 0 0) (q 1 1)-productJet (q 0 1) (q 1 0)

def inverseMatrixJet (q : MatrixScalarJet) (i k : A) : ScalarJet :=
  productJet ((!![q 1 1, -q 0 1; -q 1 0, q 0 0] : MatrixScalarJet) i k)
    (reciprocalJet (determinantJet q))

abbrev MatrixThreeJet := Matrix A A ScalarThreeJet

def matrixThreeJets (q : Point → Mat) (x : Point) : MatrixThreeJet :=
  fun i k => actualThreeJet (fun y => q y i k) x

def determinantThreeJet (q : MatrixThreeJet) : ScalarThreeJet :=
  productThreeJet (q 0 0) (q 1 1)-productThreeJet (q 0 1) (q 1 0)

def inverseMatrixThreeJet (q : MatrixThreeJet) (i k : A) : ScalarThreeJet :=
  productThreeJet ((!![q 1 1, -q 0 1; -q 1 0, q 0 0] : MatrixThreeJet) i k)
    (reciprocalThreeJet (determinantThreeJet q))

end
end CKSMixedGeometry

end

end OAI
end

section
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
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev LapseCoefficientInput := ℝ × ScalarJet × ScalarJet × ScalarJet
abbrev lz (p : LapseCoefficientInput) := p.1
abbrev lT (p : LapseCoefficientInput) := p.2.1
abbrev lF (p : LapseCoefficientInput) := p.2.2.1
abbrev lD (p : LapseCoefficientInput) := p.2.2.2

def lapseV (p : LapseCoefficientInput) : ScalarJet :=
  (1/(1+lz p^2)) • ((2:ℝ) • lT p+lz p^3 • productJet (lT p) (lT p)-(2:ℝ) • lF p)
def lapseRad (p : LapseCoefficientInput) : ScalarJet := constantJet 1+lz p^3 • lapseV p
def lapseD (p : LapseCoefficientInput) : ScalarJet := constantJet 1+lz p^3 • lD p

def lapseA (p : LapseCoefficientInput) : ScalarJet :=
  productJet (productJet (lapseV p) (reciprocalJet (sqrtJet (lapseRad p)+constantJet 1))-lD p)
    (reciprocalJet (lapseD p))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise InnerProductSpace

def positiveAngular (q : Mat) : Prop := 0 < q 1 1 ∧ 0 < determinant q

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

@[simp] lemma productJet_zero_right (f : ScalarJet) : productJet f 0 = 0 := by
  ext a b <;> simp [productJet]
@[simp] lemma productJet_zero_left (f : ScalarJet) : productJet 0 f = 0 := by
  ext a b <;> simp [productJet]
@[simp] lemma productThreeJet_zero_right (f : ScalarThreeJet) : productThreeJet f 0 = 0 := by
  apply Prod.ext
  · exact productJet_zero_right f.1
  · funext a; simp [productThreeJet]
@[simp] lemma productThreeJet_zero_left (f : ScalarThreeJet) : productThreeJet 0 f = 0 := by
  apply Prod.ext
  · exact productJet_zero_left f.1
  · funext a; simp [productThreeJet]

def powJet (f : ScalarJet) : ℕ → ScalarJet
  | 0 => constantJet 1
  | n+1 => productJet (powJet f n) f

def powThreeJet (f : ScalarThreeJet) : ℕ → ScalarThreeJet
  | 0 => constantThreeJet 1
  | n+1 => productThreeJet (powThreeJet f n) f

@[simp] lemma powJet_zero_succ (n : ℕ) : powJet 0 (n+1) = 0 := by simp [powJet]
@[simp] lemma powThreeJet_zero_succ (n : ℕ) : powThreeJet 0 (n+1) = 0 := by simp [powThreeJet]

lemma powJet_smooth (n : ℕ) : ContDiff ℝ ∞ (fun j : ScalarJet => powJet j n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih => exact productJet_smooth.comp (ih.prodMk contDiff_id)
lemma powThreeJet_smooth (n : ℕ) : ContDiff ℝ ∞ (fun j : ScalarThreeJet => powThreeJet j n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih => exact productThreeJet_smooth.comp (ih.prodMk contDiff_id)

section SmoothRules
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
@[fun_prop] lemma productJet_contDiff {f g : E → ScalarJet} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => productJet (f x) (g x)) := productJet_smooth.comp (hf.prodMk hg)
@[fun_prop] lemma productJet_contDiffAt {f g : E → ScalarJet} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => productJet (f y) (g y)) x := productJet_smooth.contDiffAt.comp x (hf.prodMk hg)
@[fun_prop] lemma powJet_contDiff {f : E → ScalarJet} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (fun x => powJet (f x) n) := (powJet_smooth n).comp hf
@[fun_prop] lemma powJet_contDiffAt {f : E → ScalarJet} {x : E} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ContDiffAt ℝ ∞ (fun y => powJet (f y) n) x := (powJet_smooth n).contDiffAt.comp x hf
@[fun_prop] lemma productThreeJet_contDiff {f g : E → ScalarThreeJet} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => productThreeJet (f x) (g x)) := productThreeJet_smooth.comp (hf.prodMk hg)
@[fun_prop] lemma productThreeJet_contDiffAt {f g : E → ScalarThreeJet} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => productThreeJet (f y) (g y)) x := productThreeJet_smooth.contDiffAt.comp x (hf.prodMk hg)
@[fun_prop] lemma powThreeJet_contDiff {f : E → ScalarThreeJet} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (fun x => powThreeJet (f x) n) := (powThreeJet_smooth n).comp hf
@[fun_prop] lemma powThreeJet_contDiffAt {f : E → ScalarThreeJet} {x : E} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ContDiffAt ℝ ∞ (fun y => powThreeJet (f y) n) x := (powThreeJet_smooth n).contDiffAt.comp x hf
end SmoothRules

def massNumeratorJet (z D T V : ScalarJet) : ScalarJet :=
  productJet (constantJet 1+powJet z 2) V+(2:ℝ) • T-
    (2:ℝ) • productJet (constantJet 1+powJet z 2) D+
    productJet (powJet z 3) (productJet T T+(2:ℝ) • productJet T V-
      productJet (constantJet 1+powJet z 2) (productJet D D))+
    productJet (powJet z 6) (productJet (productJet T T) V)
def normalizedMassJet (z D T V : ScalarJet) : ScalarJet :=
  (1/2:ℝ) • productJet (massNumeratorJet z D T V)
    (reciprocalJet (constantJet 1+productJet (powJet z 3) V))

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev MassInput := (Fin 3 → MatrixThreeJet) × (Fin 3 → MatrixScalarJet) ×
  (A → ScalarThreeJet) × (A → ScalarJet)

instance massInputNormed : NormedAddCommGroup MassInput := by
  letI : NormedAddCommGroup (Fin 3 → MatrixThreeJet) := inferInstance
  letI : NormedAddCommGroup (Fin 3 → MatrixScalarJet) := inferInstance
  letI : NormedAddCommGroup ((A → ScalarThreeJet) × (A → ScalarJet)) := inferInstance
  exact Prod.normedAddCommGroup
instance massInputSpace : NormedSpace ℝ MassInput := by
  letI : NormedSpace ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  letI : NormedSpace ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  letI : NormedSpace ℝ ((A → ScalarThreeJet) × (A → ScalarJet)) := inferInstance
  exact Prod.normedSpace
abbrev MassParameter := ScalarThreeJet × MassInput

def lowerMatrixJet (q : MatrixThreeJet) : MatrixScalarJet := fun i k => (q i k).1
def mulMatrixJet (z : ScalarJet) (q : MatrixScalarJet) : MatrixScalarJet := fun i k => productJet z (q i k)
def mulMatrixThreeJet (z : ScalarThreeJet) (q : MatrixThreeJet) : MatrixThreeJet := fun i k => productThreeJet z (q i k)
def traceProductJet (q p : MatrixScalarJet) : ScalarJet := ∑ i, ∑ k, productJet (q i k) (p k i)

def coefficientMetric (z : ScalarThreeJet) (j : MassInput) : MatrixThreeJet :=
  j.1 0+mulMatrixThreeJet (powThreeJet z 3) (j.1 1)+mulMatrixThreeJet (powThreeJet z 4) (j.1 2)
def coefficientShift (z : ScalarThreeJet) (j : MassInput) : A → ScalarThreeJet :=
  fun a => ∑ b, productThreeJet (inverseMatrixThreeJet (coefficientMetric z j) a b) (j.2.2.1 b)
def lieJet (q : MatrixThreeJet) (h : A → ScalarThreeJet) : MatrixScalarJet := fun i k => ∑ a,
  (productJet (h a).1 ((q i k).2 a.succ)+productJet (q a k).1 ((h a).2 i.succ)+
    productJet (q i a).1 ((h a).2 k.succ))
def coefficientLie (z : ScalarThreeJet) (j : MassInput) : MatrixScalarJet :=
  lieJet (coefficientMetric z j) (coefficientShift z j)
def coefficientD (z : ScalarThreeJet) (j : MassInput) : ScalarJet :=
  (1/4:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (coefficientMetric z j)))
    ((-3:ℝ) • lowerMatrixJet (j.1 1)+mulMatrixJet z.1 (j.2.1 0-(2:ℝ) • lowerMatrixJet (j.1 2)-coefficientLie z j))
def coefficientT (z : ScalarThreeJet) (j : MassInput) : ScalarJet :=
  (1/2:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (coefficientMetric z j)))
    (j.2.1 1-lowerMatrixJet (j.1 1)+mulMatrixJet z.1 (j.2.1 2-lowerMatrixJet (j.1 2)))
def coefficientBB (z : ScalarThreeJet) (j : MassInput) : ScalarJet := ∑ i, ∑ k,
  productJet (inverseMatrixJet (lowerMatrixJet (coefficientMetric z j)) i k)
    (productJet (j.2.2.1 i).1 (j.2.2.1 k).1)
def coefficientV (z : ScalarThreeJet) (j : MassInput) : ScalarJet :=
  j.2.2.2 0+productJet z.1 (j.2.2.2 1)+
    productJet (powJet z.1 2) (j.2.2.2 0)+productJet (powJet z.1 3) (j.2.2.2 1)-
    productJet (productJet (powJet z.1 3) (constantJet 1+powJet z.1 2)) (coefficientBB z j)
def cksMassJet (z : ScalarThreeJet) (j : MassInput) : ScalarJet :=
  normalizedMassJet z.1 (coefficientD z j) (coefficientT z j) (coefficientV z j)
def leadingMassJet (j : MassInput) : ScalarJet :=
  (1/2:ℝ) • j.2.2.2 0+
    (1/4:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (j.1 0))) (lowerMatrixJet (j.1 1))+
    (1/2:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (j.1 0))) (j.2.1 1)

@[simp] lemma mulMatrixJet_zero (q : MatrixScalarJet) : mulMatrixJet 0 q = 0 := by
  funext i k; exact productJet_zero_left _
@[simp] lemma mulMatrixThreeJet_zero (q : MatrixThreeJet) : mulMatrixThreeJet 0 q = 0 := by
  funext i k; exact productThreeJet_zero_left _
@[simp] lemma coefficientMetric_zero (j : MassInput) : coefficientMetric 0 j = j.1 0 := by
  simp [coefficientMetric]

@[fun_prop] lemma lowerMatrixJet_smooth : ContDiff ℝ ∞ lowerMatrixJet := by unfold lowerMatrixJet; fun_prop

lemma mulMatrixJet_smooth : ContDiff ℝ ∞
    (fun j : ScalarJet × MatrixScalarJet => mulMatrixJet j.1 j.2) := by
  unfold mulMatrixJet
  fun_prop
lemma mulMatrixThreeJet_smooth : ContDiff ℝ ∞
    (fun j : ScalarThreeJet × MatrixThreeJet => mulMatrixThreeJet j.1 j.2) := by
  unfold mulMatrixThreeJet
  fun_prop
section SmoothRules
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
@[fun_prop] lemma mulMatrixThreeJet_contDiff {f : E → ScalarThreeJet} {g : E → MatrixThreeJet}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => mulMatrixThreeJet (f x) (g x)) :=
  mulMatrixThreeJet_smooth.comp (hf.prodMk hg)
@[fun_prop] lemma mulMatrixJet_contDiff {f : E → ScalarJet} {g : E → MatrixScalarJet}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => mulMatrixJet (f x) (g x)) :=
  mulMatrixJet_smooth.comp (hf.prodMk hg)
@[fun_prop] lemma mulMatrixJet_contDiffAt {f : E → ScalarJet} {g : E → MatrixScalarJet} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => mulMatrixJet (f y) (g y)) x :=
  mulMatrixJet_smooth.contDiffAt.comp x (hf.prodMk hg)
end SmoothRules

attribute [local irreducible] coefficientMetric

attribute [local irreducible] coefficientShift

attribute [local irreducible] lieJet

attribute [local irreducible] coefficientLie

attribute [local irreducible] coefficientD

attribute [local irreducible] coefficientT

attribute [local irreducible] coefficientBB

attribute [local irreducible] coefficientV

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def traceProduct (q p : Mat) : ℝ := ∑ i, ∑ k, q i k*p k i

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def normalizedLie (q : Point → Mat) (S : Point → A → ℝ) (x : Point) (i k : A) : ℝ := ∑ a,
  (S x a*D (basis a.succ) (fun y => q y i k) x+
    q x a k*D (basis i.succ) (fun y => S y a) x+q x i a*D (basis k.succ) (fun y => S y a) x)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev TensorInput := MassInput × ScalarJet × (A → ScalarJet)
abbrev TensorParameter := ScalarThreeJet × TensorInput
instance tensorInputNormed : NormedAddCommGroup TensorInput := by
  letI : NormedAddCommGroup (ScalarJet × (A → ScalarJet)) := inferInstance
  exact Prod.normedAddCommGroup
instance tensorInputSpace : NormedSpace ℝ TensorInput := by
  letI : NormedSpace ℝ (ScalarJet × (A → ScalarJet)) := inferInstance
  exact Prod.normedSpace
instance tensorParameterNormed : NormedAddCommGroup TensorParameter := Prod.normedAddCommGroup
instance tensorParameterSpace : NormedSpace ℝ TensorParameter := Prod.normedSpace

def tensorQ (p : TensorParameter) : MatrixScalarJet := lowerMatrixJet (coefficientMetric p.1 p.2.1)
def tensorK (p : TensorParameter) : MatrixScalarJet := lowerMatrixJet (p.2.1.1 0)+
  mulMatrixJet (powJet p.1.1 3) (p.2.1.2.1 1)+mulMatrixJet (powJet p.1.1 4) (p.2.1.2.1 2)
def tensorH (p : TensorParameter) (a : A) : ScalarJet := (coefficientShift p.1 p.2.1 a).1

def tensorDen (p : TensorParameter) : ScalarJet :=
  constantJet 1+productJet (powJet p.1.1 3) (coefficientV p.1 p.2.1)
def tensorLapseSq (p : TensorParameter) : ScalarJet :=
  productJet (constantJet 1+powJet p.1.1 2) (reciprocalJet (tensorDen p))
def tensorLapse (p : TensorParameter) : ScalarJet :=
  productJet (sqrtJet (constantJet 1+powJet p.1.1 2)) (reciprocalJet (sqrtJet (tensorDen p)))

def tensorCross (p : TensorParameter) : ScalarJet := ∑ a, productJet (tensorH p a) (p.2.2.2 a)
def tensorNormalQuad (p : TensorParameter) : ScalarJet := ∑ a, ∑ b,
  productJet (tensorK p a b) (productJet (tensorH p a) (tensorH p b))

def tensorLCoeff (p : TensorParameter) : ScalarJet := productJet (tensorLapseSq p)
  (p.2.2.1-p.2.1.2.2.2 0-productJet p.1.1 (p.2.1.2.2.2 1)+productJet (powJet p.1.1 3)
    (coefficientBB p.1 p.2.1-(2:ℝ) • tensorCross p+tensorNormalQuad p))
def tensorEtaCoeff (p : TensorParameter) (a : A) : ScalarJet := productJet (tensorLapse p)
  (p.2.2.2 a-∑ b, productJet (tensorH p b) (tensorK p b a))
def tensorTauCoeff (p : TensorParameter) : MatrixScalarJet :=
  p.2.1.2.1 1-lowerMatrixJet (p.2.1.1 1)+
  mulMatrixJet p.1.1 (p.2.1.2.1 2-lowerMatrixJet (p.2.1.1 2))-
  mulMatrixJet (coefficientT p.1 p.2.1) (tensorQ p)

attribute [local irreducible] tensorK tensorQ

attribute [local irreducible] tensorH

attribute [local irreducible] tensorDen

attribute [local irreducible] tensorLapseSq

attribute [local irreducible] tensorLapse

attribute [local irreducible] tensorCross

attribute [local irreducible] tensorNormalQuad

attribute [local irreducible] tensorLCoeff

attribute [local irreducible] tensorEtaCoeff

attribute [local irreducible] tensorTauCoeff

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure MassFields where
  sigma : Point → Mat
  mg : Point → Mat
  eg : Point → Mat
  er : Point → Mat
  mK : Point → Mat
  ek : Point → Mat
  b : Point → A → ℝ
  mr : Point → ℝ
  err : Point → ℝ

structure MassFields.RegularAt (f : MassFields) (x : Point) : Prop where
  sigma : ContDiffAt ℝ 3 f.sigma x
  mg : ContDiffAt ℝ 3 f.mg x
  eg : ContDiffAt ℝ 3 f.eg x
  er : ContDiffAt ℝ 2 f.er x
  mK : ContDiffAt ℝ 2 f.mK x
  ek : ContDiffAt ℝ 2 f.ek x
  b : ContDiffAt ℝ 3 f.b x
  mr : ContDiffAt ℝ 2 f.mr x
  err : ContDiffAt ℝ 2 f.err x

def cksLeadingField (f : MassFields) : Point → ℝ :=
  fun y => (1/2:ℝ)*f.mr y+(1/4:ℝ)*traceProduct (inverse (f.sigma y)) (f.mg y)+
    (1/2:ℝ)*traceProduct (inverse (f.sigma y)) (f.mK y)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def foliationDen (p : MassParameter) : ScalarJet :=
  constantJet 1+productJet (powJet p.1.1 3) (coefficientV p.1 p.2)
def lapseCorrection (p : MassParameter) : ScalarJet :=
  -productJet (coefficientV p.1 p.2) (reciprocalJet
    (productJet (sqrtJet (foliationDen p)) (constantJet 1+sqrtJet (foliationDen p))))
def uCorrection (p : MassParameter) : ScalarJet :=
  coefficientD p.1 p.2+lapseCorrection p+
    productJet (powJet p.1.1 3) (productJet (coefficientD p.1 p.2) (lapseCorrection p))

attribute [local irreducible] lapseCorrection

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_smul (c : ℝ) (q : Mat) (hc : c ≠ 0) (i k : I) :
    inverse (c • q) i k = inverse q i k/c := inverse_rescale c (q,0,0) hc i k

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure TensorFields where
  base : MassFields
  kr : Point → ℝ
  kb : Point → A → ℝ

structure TensorFields.RegularAt (f : TensorFields) (x : Point) : Prop where
  base : f.base.RegularAt x
  kr : ContDiffAt ℝ 2 f.kr x
  kb : ContDiffAt ℝ 2 f.kb x

end
end CKSMixedGeometry

end

end OAI
end

section
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
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def radialMatrixD (f : Point → Mat) : Point → Mat := fun y i k => D (basis 0) (fun z => f z i k) y

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

 def foliationMetric (U : ℝ) (γ : Mat) (s : Point) : AmbientMat :=
  metricBlock (1/U^2+∑ a, ∑ b, γ a b*s a*s b) (fun a => ∑ b, γ a b*s b) γ

 def foliationNormal (U : ℝ) (s : Point) : Fin 3 → ℝ := ![U,-U*s 0,-U*s 1]

 def foliationTensor (U L : ℝ) (η : Point) (kT : Mat) (s : Point) : AmbientMat :=
  metricBlock (L/U^2+2/U*(∑ a, η a*s a)+∑ a, ∑ b, kT a b*s a*s b)
    (fun a => η a/U+∑ b, kT a b*s b) kT

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse inverse_smul inverse_trace)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def logGamma (f : MassFields) : Point → Mat := fun y =>
  Real.exp (y 0)^2 • f.sigma y+(1/Real.exp (y 0)) • f.mg y+f.eg y

def logGammaRadial (f : MassFields) : Point → Mat := fun y =>
  (2*Real.exp (y 0)) • f.sigma y-(1/Real.exp (y 0)^2) • f.mg y+
    (1/Real.exp (y 0)) • radialMatrixD f.eg y

def logTangentialK (f : MassFields) : Point → Mat := fun y =>
  Real.exp (y 0)^2 • f.sigma y+(1/Real.exp (y 0)) • f.mK y+f.ek y

def logShift (f : MassFields) : Point → A → ℝ := fun y a =>
  ∑ b, inverse (logGamma f y) a b*f.b y b

def logRadialMetric (f : MassFields) : Point → ℝ := fun y =>
  1/(1+Real.exp (y 0)^2)+f.mr y/Real.exp (y 0)^5+f.err y

def logSchur (f : MassFields) : Point → ℝ := fun y =>
  logRadialMetric f y-∑ i, ∑ k, inverse (logGamma f y) i k*(f.b y i*f.b y k)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse inverse_smul inverse_trace)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def logExpansion (f : MassFields) : Point → ℝ := fun x =>
  Real.exp (x 0)/4*traceProduct (inverse (logGamma f x))
    (logGammaRadial f x-(show Mat from normalizedLie (logGamma f) (logShift f) x))

def logPhysicalMass (f : MassFields) : Point → ℝ := fun x =>
  Real.exp (x 0)/2*(1+(Real.exp (x 0)/2*traceProduct (inverse (logGamma f x)) (logTangentialK f x))^2-
    ((1/Real.sqrt (logSchur f x))*logExpansion f x)^2)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def logRadialK (f : TensorFields) : Point → ℝ := fun y => 1/(1+Real.exp (y 0)^2)+f.kr y

def logOriginalL (f : TensorFields) : Point → ℝ := fun y =>
  (1/Real.sqrt (logSchur f.base y))^2*(logRadialK f y-
    2*∑ a, logShift f.base y a*f.kb y a+
    ∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b))

def logOriginalEta (f : TensorFields) : Point → A → ℝ := fun y a =>
  (1/Real.sqrt (logSchur f.base y))*(f.kb y a-∑ b, logShift f.base y b*logTangentialK f.base y b a)

def logOriginalTau (f : TensorFields) : Point → Mat := fun y =>
  logTangentialK f.base y-
    (traceProduct (inverse (logGamma f.base y)) (logTangentialK f.base y)/2) • logGamma f.base y

end
end CKSMixedGeometry

end

end OAI
end

section
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
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def logT (f : MassFields) : Point → ℝ := fun y =>
  (1/2:ℝ)*traceProduct (CKSAngularGeometry.inverse (logGamma f y)) (logTangentialK f y)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def logMetric (f : MassFields) (x : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  CKSAngularGeometry.metricBlock (logRadialMetric f x) (f.b x) (logGamma f x)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

attribute [local irreducible] cksMassJet leadingMassJet

def logQError (f : MassFields) : Point → Mat := fun y =>
  radiusPower (-3) y • f.mg y+radiusPower (-2) y • f.eg y

end
end CKSMixedGeometry

end

end OAI
end

section
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
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def lapseVField (z : ℝ) (T F : Point → ℝ) (y : Point) : ℝ :=
  (1/(1+z^2))*(2*T y+z^3*(T y*T y)-2*F y)
def lapseRadField (z : ℝ) (T F : Point → ℝ) (y : Point) : ℝ := 1+z^3*lapseVField z T F y
def lapseDField (z : ℝ) (d : Point → ℝ) (y : Point) : ℝ := 1+z^3*d y
def lapseAField (z : ℝ) (T F d : Point → ℝ) (y : Point) : ℝ :=
  (lapseVField z T F y*(1/(Real.sqrt (lapseRadField z T F y)+1))-d y)*(1/lapseDField z d y)
def lapseNormalizedField (z : ℝ) (T F d : Point → ℝ) (y : Point) : ℝ :=
  Real.sqrt ((z^2+(1+z^3*T y)^2-2*z^3*F y)/(1+z^2))/(1+z^3*d y)

end
end CKSAngularGeometry

end

end OAI
end

section
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
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

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
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

def sourceChi (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) : Mat := fun a b =>
  U x/2 * (D (CKSRealizedRound.basis 0) (fun y => γ y a b) x -
    ∑ c, (s x c*D (CKSRealizedRound.basis c.succ) (fun y => γ y a b) x +
      γ x c b*D (CKSRealizedRound.basis a.succ) (fun y => s y c) x +
      γ x a c*D (CKSRealizedRound.basis b.succ) (fun y => s y c) x))

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

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
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

def momentumCovector (G K : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : PhysicalPoint :=
  fun i => coordinateMomentum G K x (CKSRealizedRound.basis i)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev CovectorJet := I → ScalarJet
abbrev CovariantTensorJet := I → I → ScalarJet

def covectorDiv (q : Jet) (E : CovectorJet) : ℝ :=
  ∑ i, ∑ k, inverse q.1 i k*((E k).2.1 i-∑ a, christoffel q a i k*(E a).1)
def tensorDiv (q : Jet) (T : CovariantTensorJet) (a : I) : ℝ :=
  ∑ i, ∑ k, inverse q.1 i k*((T k a).2.1 i-
    ∑ b, (christoffel q b i k*(T b a).1+christoffel q b i a*(T k b).1))
def covectorLie (S E : CovectorJet) (a : I) : ℝ :=
  ∑ b, ((S b).1*(E a).2.1 b+(E b).1*(S b).2.1 a)
def covectorPair (q : Jet) (E B : I → ℝ) : ℝ :=
  ∑ i, ∑ k, inverse q.1 i k*E i*B k
def tensorPair (q : Jet) (X T : Mat) : ℝ :=
  ∑ i, ∑ k, ∑ a, ∑ b, inverse q.1 i a*inverse q.1 k b*X i k*T a b

def normalMomentum (q : Jet) (H L t Np : ℝ) (X T : Mat)
    (E : CovectorJet) (B : I → ℝ) : ℝ :=
  H*(L-t)-tensorPair q X T-Np+covectorDiv q E-2*covectorPair q (fun a => (E a).1) B

def angularMomentum (q : Jet) (H U : ℝ) (L t : ScalarJet)
    (S E : CovectorJet) (T : CovariantTensorJet) (Er B : I → ℝ) (a : I) : ℝ :=
  U*(Er a-covectorLie S E a)+H*(E a).1+tensorDiv q T a-
    (L.2.1 a+t.2.1 a)+(L.1-t.1)*B a-
      ∑ i, ∑ k, (T i a).1*inverse q.1 i k*B k

abbrev MomentumInput := ℝ × ℝ × Jet × (Fin 5 → ScalarJet) × CovectorJet ×
  CovectorJet × CovariantTensorJet × Mat × (I → ℝ)

abbrev mz (p : MomentumInput) := p.1
abbrev mw (p : MomentumInput) := p.2.1
abbrev mq (p : MomentumInput) := p.2.2.1
abbrev mc (p : MomentumInput) := p.2.2.2.1
abbrev mS (p : MomentumInput) := p.2.2.2.2.1
abbrev mE (p : MomentumInput) := p.2.2.2.2.2.1
abbrev mT (p : MomentumInput) := p.2.2.2.2.2.2.1
abbrev mX (p : MomentumInput) := p.2.2.2.2.2.2.2.1
abbrev mEr (p : MomentumInput) := p.2.2.2.2.2.2.2.2

def normalizedSpeed (p : MomentumInput) : ℝ :=
  Real.sqrt (1+mz p^2)*(1+mz p^3*(mc p 0).1)
def normalizedMean (p : MomentumInput) : ℝ :=
  2*normalizedSpeed p*(1+mz p^3*(mc p 4).1)
def accelerationCoefficient (p : MomentumInput) (a : I) : ℝ :=
  (mc p 0).2.1 a/(1+mz p^3*(mc p 0).1)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def physicalLJet (p : MomentumInput) : ScalarJet := constantJet (1+mw p*mz p^2)+mz p^3 • mc p 2
def physicalTJet (p : MomentumInput) : ScalarJet := constantJet 1+mz p^3 • mc p 1

def coordinateQ (p : MomentumInput) : ℝ :=
  normalMomentum (rescale (1/mz p^2) (mq p)) (normalizedMean p)
    (physicalLJet p).1 (physicalTJet p).1
    (2*normalizedSpeed p*mz p^3*((mc p 3).1-mz p^4*∑ a, (mS p a).1*(mc p 1).2.1 a))
    (mz p • mX p) (mz p • ((fun i k => (mT p i k).1) : Mat)) (mz p^2 • mE p)
    (mz p^3 • accelerationCoefficient p)

def coordinateZ (p : MomentumInput) (a : I) : ℝ :=
  angularMomentum (rescale (1/mz p^2) (mq p)) (normalizedMean p) (normalizedSpeed p/mz p)
    (physicalLJet p) (physicalTJet p) (mz p^5 • mS p) (mz p^2 • mE p)
    (mz p • mT p) (mz p^3 • mEr p) (mz p^3 • accelerationCoefficient p) a

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev RawMetricData := ((Fin 3 → MatrixScalarJet) × (Fin 2 → I → MatrixScalarJet)) ×
  (CovectorJet × (I → I → ScalarJet))
abbrev RawTensorData := ((Fin 5 → ScalarJet) × CovectorJet) × (CovariantTensorJet × (I → ℝ))
instance rawMetricNormedGroup : NormedAddCommGroup RawMetricData := inferInstance
instance rawTensorNormedGroup : NormedAddCommGroup RawTensorData := inferInstance
instance rawMetricNormedSpace : NormedSpace ℝ RawMetricData := inferInstance
instance rawTensorNormedSpace : NormedSpace ℝ RawTensorData := inferInstance
abbrev RawCollarData := RawMetricData × RawTensorData
instance rawCollarNormedGroup : NormedAddCommGroup RawCollarData := inferInstance
instance rawCollarNormedSpace : NormedSpace ℝ RawCollarData := inferInstance

abbrev RawCollarInput := (Fin 5 → ℝ) × RawCollarData
abbrev rz (p : RawCollarInput) := p.1 0
abbrev re (p : RawCollarInput) := p.1 1
abbrev rθ (p : RawCollarInput) := p.1 2
abbrev rpad (p : RawCollarInput) := p.1 3
abbrev rwgt (p : RawCollarInput) := p.1 4
abbrev rmat (p : RawCollarInput) := p.2.1.1.1
abbrev rdmat (p : RawCollarInput) := p.2.1.1.2
abbrev rshift (p : RawCollarInput) := p.2.1.2.1
abbrev rdshift (p : RawCollarInput) := p.2.1.2.2
abbrev rscalar (p : RawCollarInput) := p.2.2.1.1
abbrev reta (p : RawCollarInput) := p.2.2.1.2
abbrev rtau (p : RawCollarInput) := p.2.2.2.1
abbrev retar (p : RawCollarInput) := p.2.2.2.2

def rawQ (p : RawCollarInput) : MatrixScalarJet := rmat p 0+ (rz p^3*(1-re p)) • rmat p 1
def rawDQ (p : RawCollarInput) (a : I) : MatrixScalarJet := rdmat p 0 a+(rz p^3*(1-re p)) • rdmat p 1 a
def rawS (p : RawCollarInput) : CovectorJet := (1-re p) • rshift p
def rawDS (p : RawCollarInput) : I → I → ScalarJet := (1-re p) • rdshift p
def rawQr (p : RawCollarInput) : MatrixScalarJet := (1-re p) • rmat p 2-rθ p • rmat p 1
def rawExpansionInput (p : RawCollarInput) : ExpansionInput :=
  (rawQ p,rawDQ p,rawQr p,rawS p,rawDS p)
def rawC (p : RawCollarInput) (i k : I) : ScalarJet :=
  rawQr p i k-rz p • normalizedLieJet (rawExpansionInput p) i k

def matrixTraceJet (q t : MatrixScalarJet) : ScalarJet :=
  ∑ i, ∑ k, productJet (inverseMatrixJet q i k) (t k i)
def traceFreeJet (q t : MatrixScalarJet) (i k : I) : ScalarJet :=
  t i k-(1/2:ℝ) • productJet (matrixTraceJet q t) (q i k)
def rawD (p : RawCollarInput) : ScalarJet := (1/4:ℝ) • matrixTraceJet (rawQ p) (rawC p)
def rawT (p : RawCollarInput) : ScalarJet := (1-re p) • rscalar p 0
def rawF (p : RawCollarInput) : ScalarJet :=
  (1-re p) • rscalar p 1+re p • rscalar p 4+constantJet (rpad p)
def rawL (p : RawCollarInput) : ScalarJet := (1-re p) • rscalar p 2
def rawTr (p : RawCollarInput) : ScalarJet := (1-re p) • rscalar p 3-rθ p • rscalar p 0
def rawLapseInput (p : RawCollarInput) : LapseCoefficientInput := (rz p,rawT p,rawF p,rawD p)
def rawA (p : RawCollarInput) : ScalarJet := lapseA (rawLapseInput p)
def rawLambda (p : RawCollarInput) : ℝ := Real.sqrt (1+rz p^2)*(1+rz p^3*(rawA p).1)
def rawX (p : RawCollarInput) (i k : I) : ℝ :=
  (rawLambda p/2)*(traceFreeJet (rawQ p) (rawC p) i k).1

def scalarMatrixToJet (q : MatrixScalarJet) : Jet :=
  ((fun i k => (q i k).1),(fun a i k => (q i k).2.1 a),(fun a b i k => (q i k).2.2 a b))
def rawMomentumInput (p : RawCollarInput) : MomentumInput :=
  (rz p,rwgt p,scalarMatrixToJet (rawQ p),![rawA p,rawT p,rawL p,rawTr p,rawD p],
    rawS p,(1-re p) • reta p,(1-re p) • traceFreeJet (rawQ p) (rtau p),
    rawX p,fun a => (1-re p)*retar p a-rθ p*(reta p a).1)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def nullD (p : MomentumInput) : ℝ := 1+mz p^3*(mc p 4).1

def nullRatio (p : MomentumInput) : ℝ :=
  (1+mz p^3*(mc p 1).1)/(normalizedSpeed p*nullD p)

abbrev NullInput := MomentumInput × ScalarJet × ℝ
abbrev nP (p : NullInput) := p.1
abbrev nF (p : NullInput) := p.2.1
abbrev nFr (p : NullInput) := p.2.2

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def rawOriginal (p : RawCollarInput) : RawCollarInput := (fun i => if i=0 then rz p else 0,p.2)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def physicalNullQuadratic (p : MomentumInput) : ℝ :=
  -(tensorPair (rescale (1/mz p^2) (mq p)) (mz p • mX p) (mz p • mX p)+
    tensorPair (rescale (1/mz p^2) (mq p))
      (mz p • ((fun i k => (mT p i k).1) : Mat))
      (mz p • ((fun i k => (mT p i k).1) : Mat)))/2+
  nullRatio p*tensorPair (rescale (1/mz p^2) (mq p))
    (mz p • mX p) (mz p • ((fun i k => (mT p i k).1) : Mat))-
  covectorPair (rescale (1/mz p^2) (mq p))
    (mz p^2 • (fun a => (mE p a).1)) (mz p^2 • (fun a => (mE p a).1))

def physicalNullEta (p : MomentumInput) : ℝ :=
  covectorDiv (rescale (1/mz p^2) (mq p)) (mz p^2 • mE p)-
    2*covectorPair (rescale (1/mz p^2) (mq p))
      (mz p^2 • (fun a => (mE p a).1)) (mz p^3 • accelerationCoefficient p)

def coordinateSmallNull (p : NullInput) (r : ℝ) : ℝ :=
  2*(mw (nP p)/(r*Real.sqrt r)+mz (nP p)^2*nFr p-
    mz (nP p)^5*∑ a, (mS (nP p) a).1*(nF p).2.1 a)/nullD (nP p)*mz (nP p)^2+
  (scalarCurvature (rescale (1/mz (nP p)^2) (mq (nP p)))/2-mz (nP p)^2)+
  (1/nullD (nP p)-1)*(2-6*mz (nP p)*(nF p).1)*mz (nP p)^2-
  lapseLaplacian (rescale (1/mz (nP p)^2) (mq (nP p)))
    (constantJet 1+mz (nP p)^3 • mc (nP p) 0)+
  physicalNullQuadratic (nP p)-nullRatio (nP p)*physicalNullEta (nP p)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev RawNullInput := RawCollarInput × ℝ × ℝ

def rawNullMap (p : RawNullInput) : NullInput :=
  (rawMomentumInput p.1,rawF p.1,(1-re p.1)*p.2.1-rθ p.1*p.2.2)
def rawNullOriginal (p : RawNullInput) : RawNullInput := (rawOriginal p.1,p.2)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure CollarCoefficientFields where
  metric : Fin 3 → Point → Mat
  shift : Point → Point
  scalar : Fin 5 → Point → ℝ
  eta : Point → Point
  tau : Point → Mat
  etar : Point → Point
  massRadial : Point → ℝ
  massGap : Point → ℝ

def fieldRaw (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) : RawNullInput :=
  let m : RawMetricData :=
    (((fun i => matrixScalarJets (f.metric i) x),
      fun i a => matrixScalarJets (fun y j k => D (basis a) (fun z => f.metric i.castSucc z j k) y) x),
      ((fun a => actualScalarJet (fun y => f.shift y a) x),
      fun a k => actualScalarJet (D (basis a) (fun y => f.shift y k)) x))
  let t : RawTensorData :=
    (((fun i => actualScalarJet (f.scalar i) x),
      (fun a => actualScalarJet (fun y => f.eta y a) x)),
      (matrixScalarJets f.tau x,f.etar x))
  ((b,(m,t)),(f.massRadial x,f.massGap x))

def fieldQ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  f.metric 0 y+(b 0^3*(1-b 1)) • f.metric 1 y

def fieldQr (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  (1-b 1) • f.metric 2 y-b 2 • f.metric 1 y

def fieldS (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Point :=
  (1-b 1) • f.shift y

def fieldC (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  fun i k => fieldQr b f y i k-b 0*normalizedLie (fieldQ b f) (fieldS b f) y i k

def fieldD (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ :=
  (1/4:ℝ)*∑ i, ∑ k, inverse (fieldQ b f y) i k*fieldC b f y k i

def fieldT (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ := (1-b 1)*f.scalar 0 y

def fieldF (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ :=
  (1-b 1)*f.scalar 1 y+b 1*f.scalar 4 y+b 3

def fieldL (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ := (1-b 1)*f.scalar 2 y

def fieldTr (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : ℝ :=
  (1-b 1)*f.scalar 3 y-b 2*f.scalar 0 y

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def angularLift {E : Type*} (f : Angle → E) : Point → E := fun x => f (angularProjection x)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise InnerProductSpace

def rawAngularMatrix (p : RawNullInput) : Mat := fun i k => (rawQ p.1 i k).1

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure SourceMassFields where
  sigma : Angle → Mat
  mg : Angle → Mat
  mK : Angle → Mat
  mr : Angle → ℝ
  eg : Point → Mat
  ek : Point → Mat
  b : Point → Angle
  err : Point → ℝ

def SourceMassFields.logFields (f : SourceMassFields) : MassFields where
  sigma := angularLift f.sigma
  mg := angularLift f.mg
  mK := angularLift f.mK
  mr := angularLift f.mr
  eg := fun y => f.eg (logRadiusChart y)
  ek := fun y => f.ek (logRadiusChart y)
  b := fun y => f.b (logRadiusChart y)
  err := fun y => f.err (logRadiusChart y)
  er := 0

lemma angularProjection_logRadiusChart (x : Point) :
    angularProjection (logRadiusChart x) = angularProjection x := by
  ext a
  simp [angularProjection,logRadiusChart]

structure SourceMassFields.RegularAt (f : SourceMassFields) (y : Point) : Prop where
  sigma : ContDiffAt ℝ 3 f.sigma (angularProjection y)
  mg : ContDiffAt ℝ 3 f.mg (angularProjection y)
  mK : ContDiffAt ℝ 2 f.mK (angularProjection y)
  mr : ContDiffAt ℝ 2 f.mr (angularProjection y)
  eg : ContDiffAt ℝ 3 f.eg y
  ek : ContDiffAt ℝ 2 f.ek y
  b : ContDiffAt ℝ 3 f.b y
  err : ContDiffAt ℝ 2 f.err y

def sourceGamma (f : SourceMassFields) : Point → Mat := fun y =>
  (y 0)^2 • f.sigma (angularProjection y)+(1/(y 0)) • f.mg (angularProjection y)+f.eg y

def sourceTangentialK (f : SourceMassFields) : Point → Mat := fun y =>
  (y 0)^2 • f.sigma (angularProjection y)+(1/(y 0)) • f.mK (angularProjection y)+f.ek y

def sourceRadialMetric (f : SourceMassFields) : Point → ℝ := fun y =>
  1/(1+(y 0)^2)+f.mr (angularProjection y)/(y 0)^5+f.err y

structure SourceMassFields.ComponentBounds (f : SourceMassFields) (B : ℝ) (y : Point) : Prop where
  eg : ∀ i k, ScaledComponentBound (fun z => f.eg z i k) 3 2 B y
  ek : ∀ i k, ScaledComponentBound (fun z => f.ek z i k) 2 2 B y
  b : ∀ a, ScaledComponentBound (fun z => f.b z a) 3 3 B y
  err : ScaledComponentBound f.err 2 6 B y

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def fieldA (b : Fin 5 → ℝ) (f : CollarCoefficientFields) : Point → ℝ :=
  lapseAField (b 0) (fieldT b f) (fieldF b f) (fieldD b f)

def fieldNormalizedLapse (b : Fin 5 → ℝ) (f : CollarCoefficientFields) : Point → ℝ :=
  lapseNormalizedField (b 0) (fieldT b f) (fieldF b f) (fieldD b f)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def coordinateEnergy (p : NullInput) (r : ℝ) : ℝ :=
  coordinateSmallNull p r+nullRatio (nP p)*coordinateQ (nP p)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceMetric (f : SourceMassFields) (y : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  CKSAngularGeometry.metricBlock (sourceRadialMetric f y) (f.b y) (sourceGamma f y)

def sourceShift (f : SourceMassFields) : Point → Angle := fun y a =>
  ∑ b, inverse (sourceGamma f y) a b*f.b y b

def sourceSchur (f : SourceMassFields) : Point → ℝ := fun y =>
  sourceRadialMetric f y-∑ i, ∑ k, inverse (sourceGamma f y) i k*(f.b y i*f.b y k)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def traceFreeField (q t : Point → Mat) (y : Point) : Mat := fun i k =>
  t y i k-(1/2:ℝ)*(∑ a, ∑ b, inverse (q y) a b*t y b a)*q y i k

def fieldEta (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Point := (1-b 1) • f.eta y

def fieldTau (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  (1-b 1) • traceFreeField (fieldQ b f) f.tau y

def fieldEr (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Point :=
  fun a => (1-b 1)*f.etar y a-b 2*f.eta y a

def fieldX (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (y : Point) : Mat :=
  (Real.sqrt (1+b 0^2)*fieldNormalizedLapse b f y/2) • traceFreeField (fieldQ b f) (fieldC b f) y

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise InnerProductSpace

def coordinateDEC (p : NullInput) (r : ℝ) : Prop :=
  Real.sqrt ((coordinateQ (nP p))^2+
    covectorPair (rescale (1/mz (nP p)^2) (mq (nP p))) (coordinateZ (nP p)) (coordinateZ (nP p))) ≤
      coordinateEnergy p r

end
end CKSAngularGeometry

end

end OAI
end

section
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
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def CollarCoefficientFields.ThinBoundedAt (f : CollarCoefficientFields) (B : ℝ) (x : Point) : Prop :=
  (∀ i : Fin 2, ‖matrixThreeJets (f.metric i.castSucc) x‖ ≤ B) ∧
  ‖matrixScalarJets (f.metric 2) x‖ ≤ B ∧
  ‖fun a => actualThreeJet (fun y => f.shift y a) x‖ ≤ B ∧
  (∀ i, i ≠ 3 → ‖actualScalarJet (f.scalar i) x‖ ≤ B) ∧ |f.scalar 3 x| ≤ B ∧
  ‖fun a => actualScalarJet (fun y => f.eta y a) x‖ ≤ B ∧
  ‖matrixScalarJets f.tau x‖ ≤ B ∧ ‖f.etar x‖ ≤ B ∧
  |f.massRadial x| ≤ B ∧ |f.massGap x| ≤ B

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def fieldMomentumInput (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) : MomentumInput :=
  (b 0,b 4,actualJet (fieldQ b f) x,
    ![actualScalarJet (fieldA b f) x,actualScalarJet (fieldT b f) x,
      actualScalarJet (fieldL b f) x,actualScalarJet (fieldTr b f) x,
      actualScalarJet (fieldD b f) x],
    (fun a => actualScalarJet (fun y => fieldS b f y a) x),
    (fun a => actualScalarJet (fun y => fieldEta b f y a) x),
    matrixScalarJets (fieldTau b f) x,fieldX b f x,fieldEr b f x)

def fieldNullInput (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) : NullInput :=
  (fieldMomentumInput b f x,actualScalarJet (fieldF b f) x,
    (1-b 1)*f.massRadial x-b 2*f.massGap x)

def oldParams (b : Fin 5 → ℝ) : Fin 5 → ℝ := fun i => if i=0 then b 0 else 0

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open CKSCalculus
open scoped BigOperators

abbrev Chart := I → ℝ

def massField (H p : Chart → ℝ) : Chart → ℝ := fun x =>
  x 0/2*(1+(x 0*p x/2)^2-(x 0*H x/2)^2)

end
end CKSFrame

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceLapse (f : SourceMassFields) : Point → ℝ := fun y => 1/Real.sqrt (sourceSchur f y)

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
abbrev AMat := CKSAngularGeometry.Mat
abbrev MJ := CKSMixedGeometry.actualScalarJet
abbrev M3 := CKSMixedGeometry.actualThreeJet

structure LogCollarData where
  sigma : MP → AMat
  metricError : MP → AMat
  shift : MP → AP
  tError : MP → ℝ
  LError : MP → ℝ
  massError : MP → ℝ
  fstar : MP → ℝ
  etaDivR : MP → AP
  tauDivR2 : MP → AMat

def LogCollarData.angular (f : LogCollarData) (ρ : ℝ) : CKSAngularGeometry.CollarCoefficientFields where
  metric := ![fun y => f.sigma (slice ρ y),
    fun y => Real.exp ρ^3 • f.metricError (slice ρ y),
    fun y a b => Real.exp ρ^3*D (CKSMixedGeometry.basis 0) (fun z => f.metricError z a b) (slice ρ y)]
  shift := fun y => Real.exp ρ^5 • f.shift (slice ρ y)
  scalar := ![fun y => Real.exp ρ^3*f.tError (slice ρ y),
    fun y => f.fstar (slice ρ y)+f.massError (slice ρ y),
    fun y => Real.exp ρ^3*f.LError (slice ρ y),
    fun y => Real.exp ρ^3*D (CKSMixedGeometry.basis 0) f.tError (slice ρ y),
    fun y => f.fstar (slice ρ y)]
  eta := fun y => Real.exp ρ^3 • f.etaDivR (slice ρ y)
  tau := fun y => Real.exp ρ^3 • f.tauDivR2 (slice ρ y)
  etar := fun y a => Real.exp ρ^3*(f.etaDivR (slice ρ y) a+
    D (CKSMixedGeometry.basis 0) (fun z => f.etaDivR z a) (slice ρ y))
  massRadial := fun y => Real.exp ρ*D (CKSMixedGeometry.basis 0) f.massError (slice ρ y)
  massGap := fun y => Real.exp ρ*f.massError (slice ρ y)

structure LogCollarData.BoundedAt (f : LogCollarData) (B : ℝ) (x : MP) : Prop where
  sigma : ∀ a b, ‖M3 (fun y => f.sigma y a b) x‖ ≤ B
  metricError : ∀ a b, ‖M3 (fun y => f.metricError y a b) x‖ ≤ B/Real.exp (x 0)^3
  shift : ∀ a, ‖M3 (fun y => f.shift y a) x‖ ≤ B/Real.exp (x 0)^5
  tError : ‖MJ f.tError x‖ ≤ B/Real.exp (x 0)^3
  LError : ‖MJ f.LError x‖ ≤ B/Real.exp (x 0)^3
  massError : ‖MJ f.massError x‖ ≤ B/Real.exp (x 0)
  fstar : ‖MJ f.fstar x‖ ≤ B
  etaDivR : ∀ a, ‖MJ (fun y => f.etaDivR y a) x‖ ≤ B/Real.exp (x 0)^3
  tauDivR2 : ∀ a b, ‖MJ (fun y => f.tauDivR2 y a b) x‖ ≤ B/Real.exp (x 0)^3

end
end CKSAngularSlice

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Finset
abbrev Vec := Ix → ℝ
abbrev Mat := Matrix Ix Ix ℝ

def proj (x : Vec) (i j : Ix) : ℝ := (if i = j then 1 else 0) - x i * x j

def tangentTrace (x : Vec) (H : Mat) : ℝ := ∑ i, ∑ j, proj x i j * H i j

def hessTF (x : Vec) (H : Mat) (i j : Ix) : ℝ :=
  (∑ a, ∑ b, proj x i a * H a b * proj x b j) - tangentTrace x H / 2 * proj x i j

def roundLap (x : Vec) (g : Vec) (H : Mat) : ℝ :=
  tangentTrace x H - 2 * (∑ i, x i * g i)

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceCollarData (f : TensorFields) : CKSAngularSlice.LogCollarData where
  sigma := f.base.sigma
  metricError := logQError f.base
  shift := logShift f.base
  tError := fun y => logT f.base y-1
  LError := fun y => logOriginalL f y-1
  massError := fun y => logPhysicalMass f.base y-cksLeadingField f.base y
  fstar := cksLeadingField f.base
  etaDivR := fun y a => logOriginalEta f y a/Real.exp (y 0)
  tauDivR2 := fun y a b => logOriginalTau f y a b/Real.exp (y 0)^2

structure TensorFields.LogComponentBound (f : TensorFields) (B : ℝ) (x : Point) : Prop where
  sigma : ‖matrixThreeJets f.base.sigma x‖ ≤ B
  mg : ‖matrixThreeJets f.base.mg x‖ ≤ B
  eg : ‖matrixThreeJets f.base.eg x‖ ≤ B/Real.exp (x 0)^2
  mK : ‖matrixScalarJets f.base.mK x‖ ≤ B
  ek : ‖matrixScalarJets f.base.ek x‖ ≤ B/Real.exp (x 0)^2
  b : ‖fun a => actualThreeJet (fun y => f.base.b y a) x‖ ≤ B/Real.exp (x 0)^3
  mr : ‖actualScalarJet f.base.mr x‖ ≤ B
  err : ‖actualScalarJet f.base.err x‖ ≤ B/Real.exp (x 0)^6
  kr : ‖actualScalarJet f.kr x‖ ≤ B/Real.exp (x 0)^5
  kb : ‖fun a => actualScalarJet (fun y => f.kb y a) x‖ ≤ B/Real.exp (x 0)^3

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial
abbrev Poly := MvPolynomial (Fin 3) ℝ

def laplacian : Poly →ₗ[ℝ] Poly :=
  ∑ i : Fin 3, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap

def rotation (i j : Fin 3) : Derivation ℝ Poly Poly :=
  (X i : Poly) • pderiv j - (X j : Poly) • pderiv i

def sphereCoordinate (i : Fin 3) : C(Sphere, ℝ) :=
  ⟨fun x => x.1 i, (EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩

def sphereEval : Poly →ₐ[ℝ] C(Sphere, ℝ) := aeval sphereCoordinate

def harmonicPolynomials (l : ℕ) : Submodule ℝ Poly :=
  homogeneousSubmodule (Fin 3) ℝ l ⊓ LinearMap.ker laplacian

def harmonicSpace (l : ℕ) : Submodule ℝ C(Sphere, ℝ) :=
  (harmonicPolynomials l).map sphereEval.toLinearMap

instance harmonicPolynomials_finite (l : ℕ) :
    Module.Finite ℝ (harmonicPolynomials l) :=
  Module.Finite.iff_fg.mpr
    ((homogeneousSubmodule_fg (Fin 3) ℝ l).of_le inf_le_left)

instance harmonicSpace_finite (l : ℕ) : Module.Finite ℝ (harmonicSpace l) :=
  Module.Finite.iff_fg.mpr
    ((Module.Finite.iff_fg.mp (harmonicPolynomials_finite l)).map sphereEval.toLinearMap)

open MeasureTheory

abbrev SphereL2 := Lp ℝ 2 surfaceMeasure

def toL2 : C(Sphere, ℝ) →L[ℝ] SphereL2 := ContinuousMap.toLp 2 surfaceMeasure ℝ

def harmonicL2 (l : ℕ) : Submodule ℝ SphereL2 :=
  (harmonicSpace l).map toL2.toLinearMap

instance harmonicL2_finite (l : ℕ) : Module.Finite ℝ (harmonicL2 l) :=
  Module.Finite.iff_fg.mpr
    ((Module.Finite.iff_fg.mp (harmonicSpace_finite l)).map toL2.toLinearMap)

def harmonicProjection (l : ℕ) : SphereL2 →L[ℝ] harmonicL2 l :=
  (harmonicL2 l).orthogonalProjectionOnto

open scoped Pointwise

def planeRotationMap (i j : Fin 3) (t : ℝ) : Ambient →ₗ[ℝ] Ambient where
  toFun x := WithLp.toLp 2 (fun k =>
    if k = i then Real.cos t * x i - Real.sin t * x j
    else if k = j then Real.sin t * x i + Real.cos t * x j else x k)
  map_add' x y := by
    apply PiLp.ext
    intro k
    dsimp
    split_ifs <;> ring
  map_smul' a x := by
    apply PiLp.ext
    intro k
    dsimp
    split_ifs <;> ring

lemma planeRotationMap_apply (i j k : Fin 3) (t : ℝ) (x : Ambient) :
    planeRotationMap i j t x k =
      if k = i then Real.cos t * x i - Real.sin t * x j
      else if k = j then Real.sin t * x i + Real.cos t * x j else x k := rfl

lemma planeRotationMap_norm (i j : Fin 3) (hij : i ≠ j) (t : ℝ) (x : Ambient) :
    ‖planeRotationMap i j t x‖ = ‖x‖ := by
  have hs : ‖planeRotationMap i j t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    have h := congrArg (fun z : ℝ => z * (x i ^ 2 + x j ^ 2))
      (Real.cos_sq_add_sin_sq t)
    ring_nf at h
    fin_cases i <;> fin_cases j <;>
      simp_all [Fin.sum_univ_three, planeRotationMap_apply] <;> nlinarith
  nlinarith only [hs, norm_nonneg (planeRotationMap i j t x), norm_nonneg x]

lemma planeRotationMap_neg (i j : Fin 3) (hij : i ≠ j) (t : ℝ) (x : Ambient) :
    planeRotationMap i j (-t) (planeRotationMap i j t x) = x := by
  apply PiLp.ext
  intro k
  by_cases hi : k = i
  · subst k
    simp [planeRotationMap_apply, hij.symm]
    linear_combination (x i) * (Real.cos_sq_add_sin_sq t)
  · by_cases hj : k = j
    · subst k
      simp [planeRotationMap_apply, hij.symm]
      linear_combination (x j) * (Real.cos_sq_add_sin_sq t)
    · simp [planeRotationMap_apply, hi, hj]

def planeRotation (i j : Fin 3) (hij : i ≠ j) (t : ℝ) :
    Ambient ≃ₗᵢ[ℝ] Ambient where
  toLinearEquiv :=
    { planeRotationMap i j t with
      invFun := planeRotationMap i j (-t)
      left_inv := planeRotationMap_neg i j hij t
      right_inv := by intro x; simpa using planeRotationMap_neg i j hij (-t) x }
  norm_map' := planeRotationMap_norm i j hij t

lemma planeRotation_apply (i j : Fin 3) (hij : i ≠ j) (t : ℝ) (x : Ambient) :
    planeRotation i j hij t x = planeRotationMap i j t x := rfl

def sphereIntegral : C(Sphere, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (toL2 1)).comp toL2

lemma harmonicL2_exists_polynomial {l : ℕ} (v : harmonicL2 l) :
    ∃ p : Poly, p.IsHomogeneous l ∧ laplacian p = 0 ∧ toL2 (sphereEval p) = v := by
  obtain ⟨f, ⟨p, ⟨hp, hΔ⟩, rfl⟩, hf⟩ := v.property
  exact ⟨p, hp, hΔ, hf⟩

def sphereArea : ℝ := sphereIntegral 1

def rotationWord : List (Fin 3 × Fin 3) → Poly → Poly
  | [], p => p
  | ij :: w, p => rotation ij.1 ij.2 (rotationWord w p)

open scoped Manifold ContDiff Topology
open Set
instance ambient_finrank : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

def puncturedSpace : TopologicalSpace.Opens Ambient :=
  ⟨{x | x ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩

lemma sphere_ne_zero (x : Sphere) : (x : Ambient) ≠ 0 :=
  ne_zero_of_mem_unit_sphere x

lemma normalize_mem_sphere (x : Ambient) (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Ambient) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

def normalizeSphere (x : puncturedSpace) : Sphere :=
  ⟨‖(x : Ambient)‖⁻¹ • (x : Ambient), normalize_mem_sphere x x.2⟩

lemma normalizeSphere_smooth : ContMDiff 𝓘(ℝ, Ambient) (𝓡 2) ∞ normalizeSphere := by
  have hcoe : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, Ambient) ∞
      (fun x : puncturedSpace => (x : Ambient)) := contMDiff_subtype_val
  have hn : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, ℝ) ∞
      (fun x : puncturedSpace => ‖(x : Ambient)‖) := by
    intro x
    exact (contDiffAt_norm ℝ (show (x : Ambient) ≠ 0 from x.2)).comp_contMDiffAt hcoe.contMDiffAt
  have h := (hn.inv₀ (fun x => norm_ne_zero_iff.mpr (show (x : Ambient) ≠ 0 from x.2))).smul hcoe
  exact h.codRestrict_sphere (fun x => normalize_mem_sphere x x.2)

def radialExtension (f : Sphere → ℝ) (x : Ambient) : ℝ :=
  if hx : x ≠ 0 then f (normalizeSphere ⟨x, hx⟩) else 0

lemma radialExtension_on_sphere (f : Sphere → ℝ) (x : Sphere) :
    radialExtension f x = f x := by
  rw [radialExtension, dite_eq_left (sphere_ne_zero x)]
  congr 1
  apply Subtype.ext
  have hx : ‖(x : Ambient)‖ = 1 := by simp
  simp [normalizeSphere, hx]

theorem radialExtension_smooth {f : Sphere → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (radialExtension f) puncturedSpace := by
  have h : ContMDiff 𝓘(ℝ, Ambient) 𝓘(ℝ, ℝ) ∞
      (fun x : puncturedSpace => radialExtension f x) := by
    have he : (fun x : puncturedSpace => radialExtension f x) = f ∘ normalizeSphere := by
      funext x
      exact dite_eq_left (show (x : Ambient) ≠ 0 from x.2)
    rw [he]
    exact hf.comp normalizeSphere_smooth
  intro x hx
  have hx' := (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : puncturedSpace))).mp
    (h.contMDiffAt (x := ⟨x, hx⟩))
  exact hx'.contDiffAt.contDiffWithinAt

def rotationGenerator (i j : Fin 3) : Ambient →ₗ[ℝ] Ambient where
  toFun x := WithLp.toLp 2 (fun k => (if k = j then x i else 0) - (if k = i then x j else 0))
  map_add' x y := by ext k; dsimp; split_ifs <;> ring
  map_smul' a x := by ext k; dsimp; split_ifs <;> ring

local instance cksLocalInst_1853 : ContinuousSMul ℝ Ambient := IsBoundedSMul.continuousSMul

def smoothRotation (i j : Fin 3) (F : Ambient → ℝ) (x : Ambient) : ℝ :=
  fderiv ℝ F x (rotationGenerator i j x)

def smoothRestriction (F : Ambient → ℝ) (hF : ContDiffOn ℝ ∞ F puncturedSpace) : C(Sphere, ℝ) :=
  ⟨fun x => F x, hF.continuousOn.comp_continuous continuous_subtype_val sphere_ne_zero⟩

@[simp] lemma planeRotation_zero (i j : Fin 3) (hij : i ≠ j) (x : Ambient) :
    planeRotation i j hij 0 x = x := by
  apply PiLp.ext
  intro k
  simp only [planeRotation_apply, planeRotationMap_apply, Real.cos_zero, Real.sin_zero,
    one_mul, zero_mul, sub_zero, zero_add]
  split_ifs <;> simp_all

def smoothCasimir (F : Ambient → ℝ) : Ambient → ℝ :=
  smoothRotation 0 1 (smoothRotation 0 1 F) +
    smoothRotation 0 2 (smoothRotation 0 2 F) +
    smoothRotation 1 2 (smoothRotation 1 2 F)

def harmonicCoefficientPolynomial (l : ℕ) (f : SphereL2) : Poly :=
  Classical.choose (harmonicL2_exists_polynomial (harmonicProjection l f))

end
end CKSSphericalHarmonics

end

noncomputable section
namespace CKSSpectralHeat
noncomputable section
open Set Filter Real
open scoped Topology ContDiff

def eigenvalue (n : ℕ) : ℝ := (n + 2) * (n + 3)

def kernel (t : ℝ) : ℝ := smoothTransition (t + 1) * exp (-t)

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

end
end CKSSpectralHeat

end

end OAI
end

section
namespace OAI

namespace CKSLorentz
end CKSLorentz

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

abbrev U : Set E := {x | x ≠ 0}

attribute [local instance] CKSLorentz.two_atLeastTwo

@[simp] lemma e_apply (i j : Ix) : e i j = if j = i then 1 else 0 := by
  simp [e, eq_comm]

def grad (F : E → ℝ) (x : E) : Vec := fun i => pd i F x

def hess (F : E → ℝ) (x : E) : Mat := fun i j => pd i (pd j F) x

lemma partial_of_clm (A : E →L[ℝ] ℝ) (i : Ix) (x : E) : pd i A x = A (e i) := by
  rw [pd, A.fderiv]

@[simp] lemma pd_const (k : Ix) (c : ℝ) (x : E) : pd k (fun _ => c) x = 0 := by
  simp [pd]

@[simp] lemma pd_coordinate (k i : Ix) (x : E) :
    pd k (fun y : E => y i) x = if k = i then 1 else 0 := by
  change pd k (EuclideanSpace.proj i) x = _
  rw [partial_of_clm]
  simp [eq_comm]

def roundLaplacian (F : E → ℝ) (x : E) : ℝ := roundLap (fun i => x i) (grad F x) (hess F x)

def traceFreeHess (F : E → ℝ) (x : E) (i j : Ix) : ℝ := hessTF (fun a => x a) (hess F x) i j

def tensorDivergence (T : E → Mat) (x : E) (j : Ix) : ℝ :=
  ∑ k, ∑ i, ∑ l, proj (fun a => x a) k i * proj (fun a => x a) j l *
    pd k (fun y => T y i l) x

def sphereGradient (F : E → ℝ) (x : E) (j : Ix) : ℝ :=
  ∑ k, proj (fun a => x a) j k * grad F x k

lemma unit_sum_sq {x : E} (hx : ‖x‖ = 1) : ∑ i, x i ^ 2 = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, hx]
  norm_num

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure SourceTensorFields where
  base : SourceMassFields
  kr : Point → ℝ
  kb : Point → A → ℝ

structure SourceTensorFields.RegularAt (f : SourceTensorFields) (x : Point) : Prop where
  base : f.base.RegularAt x
  kr : ContDiffAt ℝ 2 f.kr x
  kb : ContDiffAt ℝ 2 f.kb x

structure SourceTensorFields.ComponentBounds (f : SourceTensorFields) (B : ℝ) (y : Point) : Prop where
  base : f.base.ComponentBounds B y
  kr : ScaledComponentBound f.kr 2 5 B y
  kb : ∀ a, ScaledComponentBound (fun z => f.kb z a) 2 3 B y

def SourceTensorFields.logFields (f : SourceTensorFields) : TensorFields where
  base := f.base.logFields
  kr := fun y => f.kr (logRadiusChart y)
  kb := fun y => f.kb (logRadiusChart y)

def sourceRadialK (f : SourceTensorFields) : Point → ℝ := fun y => 1/(1+(y 0)^2)+f.kr y

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff

def temporalJet (b n : ℕ) (t : ℝ) : ℝ :=
  CKSSpectralHeat.eigenvalue n ^ b *
    iteratedDeriv b CKSSpectralHeat.kernel (CKSSpectralHeat.eigenvalue n * t)

abbrev SpaceTime := ℝ × Ambient

abbrev HeatJet := ℕ × List (Fin 3 × Fin 3)

def heatTerm (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime) : ℝ :=
  temporalJet a.1 n z.1 * radialExtension (sphereEval (rotationWord a.2 (p n))) z.2

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence)
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
      D_sin _ hd1, D_sin _ hd2, D_cos _ hd1, D_cos _ hd2, dc, Fin.reduceEq, ite_false, ite_true]
    norm_num
    <;> ring

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSDifferentialSeries
noncomputable section
open Set Filter
open scoped Topology ContDiff
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
variable {s : Set E} (hs : IsOpen s)
variable (A : J → E → E →L[ℝ] ℝ) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) s)
variable (next : I → J → I) (F : I → ℕ → E → ℝ)
variable (hF : ∀ i n x, x ∈ s → HasFDerivAt (F i n)
  (∑ j, F (next i j) n x • A j x) x)
variable (bound : ∀ i, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n x, x ∈ s → ‖F i n x‖ ≤ u n)

include bound

include hF

include hs hA

end
end CKSDifferentialSeries

end

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

def PolynomialRapid (p : ℕ → Poly) : Prop :=
  ∀ (w : List (Fin 3 × Fin 3)) (b : ℕ), Summable (fun n =>
    CKSSpectralHeat.eigenvalue n ^ b * ‖sphereEval (rotationWord w (p n))‖)

def heatPolynomials (f : C(Sphere, ℝ)) (n : ℕ) : Poly :=
  harmonicCoefficientPolynomial (n + 2) (toL2 f)

def jointHeatSeries (p : ℕ → Poly) (a : HeatJet) (z : SpaceTime) : ℝ :=
  ∑' n, heatTerm p a n z

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence)
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
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

def primitive (a : ℝ) (q : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s in a..r, q s

def paddingDensity (r : ℝ) : ℝ := 1/(r * Real.sqrt r)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

def Balanced (f : C(Sphere, ℝ)) (m : ℝ) : Prop :=
  sphereIntegral f = m * sphereArea ∧ ∀ i : Fin 3, sphereIntegral (f * sphereCoordinate i) = 0

def spatialHeat (p : ℕ → Poly) (a : HeatJet) (t : ℝ) (x : Ambient) : ℝ :=
  jointHeatSeries p a (t, x)

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

def paddingWeight (R r : ℝ) : ℝ := Real.smoothTransition (r/R-1)
def paddingMass (R : ℝ) : ℝ → ℝ := primitive R (fun s => paddingWeight R s * paddingDensity s)
def heatDensity (R r : ℝ) : ℝ := bendingZeta R r / (2*r*(1+(bendingV R r)^2))
def heatTime (R : ℝ) : ℝ → ℝ := primitive (3*R) (heatDensity R)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

def pair (M : Mat) (v w : E) : ℝ := ∑ i : Ix, ∑ j : Ix, v i * w j * M i j

def dPair (T : E → Mat) (n d v w : E) : ℝ :=
  pair (fun i j => fderiv ℝ (fun y => T y i j) n d) v w

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
@[simp] lemma dPair_smul_dir (T : E → Mat) (n d v w : E) (c : ℝ) :
    dPair T n (c • d) v w = c * dPair T n d v w := by
  simp only [dPair,pair,map_smul,smul_eq_mul,mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

def inversePolynomials (p : ℕ → Poly) (n : ℕ) : Poly :=
  (1 - CKSSpectralHeat.eigenvalue n / 2)⁻¹ • p n

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

def roundingWeight (R r : ℝ) : ℝ := Real.smoothTransition (r/R-2)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix Mat e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

def tensorA (T : E → Mat) (x : Point) := pair (T (sphereParam x)) (thetaFrame x) (thetaFrame x)
def tensorB (T : E → Mat) (x : Point) := pair (T (sphereParam x)) (thetaFrame x) (phiUnit x)

def tensorPhi (T : E → Mat) (x : Point) := Real.sin (x 1) * tensorB T x

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics

def heatTensor (p : ℕ → Poly) (t : ℝ) (x : E) : Mat :=
  traceFreeHess (spatialHeat (inversePolynomials p) (0,[]) t) x

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

def collarParams (R r : ℝ) : Fin 5 → ℝ :=
  ![1/r,roundingWeight R r,r*deriv (roundingWeight R) r,paddingMass R r,paddingWeight R r]

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open CKSMixedGeometry (basis radiusPower)
open CKSBending
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

 def radialLift (h : ℝ → ℝ) : MP → ℝ := fun y => h (Real.exp (y 0))

def collarQ (R : ℝ) (f : LogCollarData) (y : MP) : AMat :=
  f.sigma y+(1-radialLift (roundingWeight R) y) • f.metricError y

def collarShift (R : ℝ) (f : LogCollarData) (y : MP) : AP :=
  (1-radialLift (roundingWeight R) y) • f.shift y

def collarT (R : ℝ) (f : LogCollarData) (y : MP) : ℝ :=
  1+(1-radialLift (roundingWeight R) y)*f.tError y

def collarLb (R : ℝ) (f : LogCollarData) (y : MP) : ℝ :=
  1+(1-radialLift (roundingWeight R) y)*f.LError y

def collarL (R : ℝ) (f : LogCollarData) (y : MP) : ℝ :=
  collarLb R f y+paddingWeight R (Real.exp (y 0))/Real.exp (y 0)^2

def collarF (R : ℝ) (f : LogCollarData) (y : MP) : ℝ :=
  f.fstar y+(1-radialLift (roundingWeight R) y)*f.massError y+radialLift (paddingMass R) y

def collarEtaDivR (R : ℝ) (f : LogCollarData) (y : MP) : AP :=
  (1-radialLift (roundingWeight R) y) • f.etaDivR y

end
end CKSAngularSlice

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSAngularGeometry

def sourceTensor (f : SourceTensorFields) (y : Point) : AmbientMat :=
  metricBlock (sourceRadialK f y) (f.kb y) (sourceTangentialK f.base y)
end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

@[simp] lemma pd_const_add (m : ℝ) (F : E → ℝ) (k : Ix) (x : E) :
    pd k (fun y => m + F y) x = pd k F x := by
  simp only [pd, fderiv_const_add]

@[simp] lemma pd_const_add_fun (m : ℝ) (F : E → ℝ) (k : Ix) :
    pd k (fun y => m + F y) = pd k F := by
  funext x
  exact pd_const_add m F k x

@[simp] lemma roundLaplacian_const_add (m : ℝ) (F : E → ℝ) (x : E) :
    roundLaplacian (fun y => m + F y) x = roundLaplacian F x := by
  simp only [roundLaplacian, roundLap, tangentTrace, grad, hess, pd_const_add_fun, pd_const_add]

@[simp] lemma sphereGradient_const_add (m : ℝ) (F : E → ℝ) (x : E) (j : Ix) :
    sphereGradient (fun y => m + F y) x j = sphereGradient F x j := by
  simp only [sphereGradient, grad, pd_const_add]

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise

 def quadratic3 (g : AmbientMat) (v : Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, g i j*v i*v j

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

 def normalizedFoliationMetric (z U : ℝ) (q : Mat) (S : Point) : AmbientMat :=
  metricBlock (1/U^2+z^6*(1+z^2)*(∑ a, ∑ b, q a b*S a*S b))
    (fun a => z^3*Real.sqrt (1+z^2)*(∑ b, q a b*S b)) q

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics
open CKSInducedSphere (E Ix Mat U)
open scoped Topology ContDiff

def positiveChart : Set Point := {x | 0 < x 0}

def chartMass (f : ℝ → E → ℝ) (t c : ℝ → ℝ) (x : Point) : ℝ :=
  c (x 0) + f (t (x 0)) (sphereParam x)
def chartTensorA (T : ℝ → E → Mat) (t : ℝ → ℝ) (x : Point) : ℝ :=
  tensorA (T (t (x 0))) x
def chartTensorPhi (T : ℝ → E → Mat) (t : ℝ → ℝ) (x : Point) : ℝ :=
  tensorPhi (T (t (x 0))) x

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

 def radialScale (r : ℝ) : Fin 3 → ℝ := ![Real.sqrt (1+r^2),1/r,1/r]
 def radialNormalize (r : ℝ) (G : AmbientMat) : AmbientMat :=
  fun i j => radialScale r i*G i j*radialScale r j

 def fieldNormalizedMetric (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) : AmbientMat :=
  normalizedFoliationMetric (b 0) (fieldNormalizedLapse b f x) (fieldQ b f x) (fieldS b f x)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere
open scoped Topology ContDiff

def canonicalF (f₀ : C(Sphere,ℝ)) (m : ℝ) : ℝ → E → ℝ :=
  fun t y => m + spatialHeat (heatPolynomials f₀) (0,[]) t y
def canonicalT (f₀ : C(Sphere,ℝ)) : ℝ → E → Mat := heatTensor (heatPolynomials f₀)

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

def outerMass (f₀ : C(Sphere,ℝ)) (m R : ℝ) : Point → ℝ :=
  chartMass (canonicalF f₀ m) (heatTime R) (paddingMass R)
def outerA (f₀ : C(Sphere,ℝ)) (R : ℝ) : Point → ℝ :=
  chartTensorA (canonicalT f₀) (heatTime R)
def outerPhi (f₀ : C(Sphere,ℝ)) (R : ℝ) : Point → ℝ :=
  chartTensorPhi (canonicalT f₀) (heatTime R)

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology Matrix

end
end CKSSphericalChart

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set
def minkowski (x y : V) : ℝ := -x.1 * y.1 + inner ℝ x.2 y.2

def mass (e : ℝ) (p : E) : ℝ := Real.sqrt (e^2 - ‖p‖^2)

lemma energy_pos {e : ℝ} {p : E} (h : ‖p‖ < e) : 0 < e := (norm_nonneg p).trans_lt h
lemma mass_pos {e : ℝ} {p : E} (h : ‖p‖ < e) : 0 < mass e p := by
  apply Real.sqrt_pos.2
  nlinarith [norm_nonneg p, energy_pos h]
lemma mass_sq {e : ℝ} {p : E} (h : ‖p‖ < e) : mass e p ^2 = e^2 - ‖p‖^2 := by
  apply Real.sq_sqrt
  nlinarith [norm_nonneg p, energy_pos h]
lemma inner_momentum {e m : ℝ} {p : E} (hm : m^2 = e^2 - ‖p‖^2) :
    inner ℝ p p = e^2-m^2 := by rw [real_inner_self_eq_norm_sq]; linarith

def boost (e m : ℝ) (p : E) (x : V) : V :=
  ((e*x.1 + inner ℝ p x.2)/m,
    x.2 + (x.1/m + inner ℝ p x.2/(m*(e+m))) • p)

lemma boost_minkowski {e m : ℝ} {p : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (x y : V) :
    minkowski (boost e m p x) (boost e m p y) = minkowski x y := by
  simp only [minkowski, boost, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_trivial]
  rw [real_inner_comm x.2 p, inner_momentum hm]
  field_simp
  ring

lemma boost_neg_inverse {e m : ℝ} {p : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (x : V) :
    boost e m (-p) (boost e m p x) = x := by
  apply Prod.ext
  · simp only [boost, inner_neg_left, inner_add_right, inner_smul_right,
      inner_momentum hm]
    field_simp
    ring
  · simp only [boost, inner_neg_left, inner_add_right, inner_smul_right,
      inner_momentum hm, smul_neg]
    have hc : x.1 / m + inner ℝ p x.2 / (m * (e + m)) -
        ((e * x.1 + inner ℝ p x.2) / m / m +
          -(inner ℝ p x.2 + (x.1 / m + inner ℝ p x.2 / (m * (e+m))) * (e^2-m^2)) / (m*(e+m))) = 0 := by
      field_simp
      ring
    calc
      _ = x.2 + (x.1 / m + inner ℝ p x.2 / (m * (e + m)) -
        ((e * x.1 + inner ℝ p x.2) / m / m +
          -(inner ℝ p x.2 + (x.1 / m + inner ℝ p x.2 / (m*(e+m))) * (e^2-m^2)) / (m*(e+m)))) • p := by module
      _ = x.2 := by rw [hc]; simp

lemma boost_smooth (e m : ℝ) (p : E) : ContDiff ℝ ∞ (boost e m p) := by
  have hi : ContDiff ℝ ∞ (fun x : V => inner ℝ p x.2) := ContDiff.inner ℝ contDiff_const contDiff_snd
  unfold boost
  exact (((contDiff_const.mul contDiff_fst).add hi).div_const m).prodMk
    (contDiff_snd.add (((contDiff_fst.div_const m).add
      (hi.div_const (m*(e+m)))).smul contDiff_const))

lemma sphere_norm (n : Sphere) : ‖(n : E)‖ = 1 := by simp

def denominator (e m : ℝ) (p : E) (n : E) : ℝ := (e + inner ℝ p n)/m

def boundarySpatial (e m : ℝ) (p : E) (n : E) : E :=
  n + (1/m + inner ℝ p n/(m*(e+m))) • p

lemma denominator_pos {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm : 0 < m) (n : Sphere) :
    0 < denominator e m p n := by
  apply div_pos _ hm
  have hi := neg_le_abs (inner ℝ p (n:E))
  have hb := (abs_real_inner_le_norm p (n:E))
  rw [sphere_norm] at hb
  nlinarith

lemma boundarySpatial_norm {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (n : Sphere) :
    ‖boundarySpatial e m p n‖ = denominator e m p n := by
  have hd : e+m ≠ 0 := ne_of_gt (add_pos (energy_pos he) hm0)
  have h := boost_minkowski hm0.ne' hd hm ((1:ℝ),(n:E)) ((1:ℝ),(n:E))
  have hn := sphere_norm n
  change -((e*1 + inner ℝ p (n:E))/m) * ((e*1 + inner ℝ p (n:E))/m) +
    inner ℝ (boundarySpatial e m p n) (boundarySpatial e m p n) =
    -(1:ℝ)*1 + inner ℝ (n:E) (n:E) at h
  simp only [mul_one] at h
  change -(denominator e m p n) * (denominator e m p n) + _ = _ at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hn] at h
  have hp := denominator_pos he hm0 n
  nlinarith [norm_nonneg (boundarySpatial e m p n)]

def boundary (e : ℝ) (p : E) (he : ‖p‖ < e) (n : Sphere) : Sphere :=
  ⟨(denominator e (mass e p) p n)⁻¹ • boundarySpatial e (mass e p) p n, by
    have hm := mass_pos he
    have hp := denominator_pos he hm n
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp), boundarySpatial_norm he hm (mass_sq he), inv_mul_cancel₀ hp.ne']⟩

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
    · simp only [boost, Prod.fst_add, Prod.snd_add, inner_add_right]; ring
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

lemma mass_neg (e : ℝ) (p : E) : mass e (-p) = mass e p := by simp [mass]

instance : Fact (Module.finrank ℝ E = 2+1) := ⟨by simp [E]⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

def hyperTime (x : E) : ℝ := Real.sqrt (1+‖x‖^2)
def hyperboloid (x : E) : V := (hyperTime x, x)
def hyperbolicMap (e m : ℝ) (p : E) (x : E) : E := (boost e m p (hyperboloid x)).2

lemma hyperTime_pos (x : E) : 0 < hyperTime x := Real.sqrt_pos.2 (by positivity)
lemma hyperTime_sq (x : E) : hyperTime x ^2 = 1+‖x‖^2 := Real.sq_sqrt (by positivity)
lemma norm_lt_hyperTime (x : E) : ‖x‖ < hyperTime x := by
  have := hyperTime_sq x
  have := hyperTime_pos x
  nlinarith [norm_nonneg x]
lemma hyperTime_smooth : ContDiff ℝ ∞ hyperTime :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x => by positivity)
lemma hyperboloid_smooth : ContDiff ℝ ∞ hyperboloid := hyperTime_smooth.prodMk contDiff_id
lemma hyperbolicMap_smooth (e m : ℝ) (p : E) : ContDiff ℝ ∞ (hyperbolicMap e m p) :=
  ((boost_smooth e m p).comp hyperboloid_smooth).snd

lemma boosted_time_pos {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm : 0 < m) (x : E) :
    0 < (boost e m p (hyperboloid x)).1 := by
  apply div_pos _ hm
  have hab := abs_real_inner_le_norm p x
  have hneg := neg_le_abs (inner ℝ p x)
  have hprod : ‖p‖ * ‖x‖ < e * hyperTime x := by
    calc
      _ ≤ ‖p‖ * hyperTime x := mul_le_mul_of_nonneg_left (norm_lt_hyperTime x).le (norm_nonneg p)
      _ < _ := mul_lt_mul_of_pos_right he (hyperTime_pos x)
  change 0 < e * hyperTime x + inner ℝ p x
  linarith

lemma hyperboloid_minkowski (x : E) : minkowski (hyperboloid x) (hyperboloid x) = -1 := by
  simp only [minkowski, hyperboloid, real_inner_self_eq_norm_sq]
  nlinarith [hyperTime_sq x]

theorem hyperboloid_boost {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (x : E) :
    hyperboloid (hyperbolicMap e m p x) = boost e m p (hyperboloid x) := by
  apply Prod.ext
  · have h := boost_minkowski hm0.ne' (add_pos (energy_pos he) hm0).ne' hm
      (hyperboloid x) (hyperboloid x)
    rw [hyperboloid_minkowski] at h
    change -(boost e m p (hyperboloid x)).1 * (boost e m p (hyperboloid x)).1 +
      inner ℝ (hyperbolicMap e m p x) (hyperbolicMap e m p x) = -1 at h
    rw [real_inner_self_eq_norm_sq] at h
    change hyperTime _ = _
    nlinarith [hyperTime_sq (hyperbolicMap e m p x),
      hyperTime_pos (hyperbolicMap e m p x), boosted_time_pos he hm0 x]
  · rfl

lemma hyperbolicMap_inverse (e : ℝ) (p : E) (he : ‖p‖ < e) (x : E) :
    hyperbolicMap e (mass e p) (-p) (hyperbolicMap e (mass e p) p x) = x := by
  change (boost e (mass e p) (-p) (hyperboloid (hyperbolicMap e (mass e p) p x))).2 = x
  rw [hyperboloid_boost he (mass_pos he) (mass_sq he),
    boost_neg_inverse (mass_pos he).ne' (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he)]
  rfl

def hyperbolicHomeomorph (e : ℝ) (p : E) (he : ‖p‖ < e) : E ≃ₜ E where
  toEquiv := {
    toFun := hyperbolicMap e (mass e p) p
    invFun := hyperbolicMap e (mass e p) (-p)
    left_inv := hyperbolicMap_inverse e p he
    right_inv := by intro x; simpa [mass_neg] using hyperbolicMap_inverse e (-p) (by simpa using he) x }
  continuous_toFun := (hyperbolicMap_smooth e (mass e p) p).continuous
  continuous_invFun := (hyperbolicMap_smooth e (mass e p) (-p)).continuous

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff

def timeDifferential (m : ℝ) (p : E) : E →L[ℝ] ℝ := m⁻¹ • innerSL ℝ p

def spaceDifferential (e m : ℝ) (p : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + ((m*(e+m))⁻¹ • innerSL ℝ p).smulRight p

@[simp] lemma timeDifferential_apply (m : ℝ) (p Y : E) :
    timeDifferential m p Y = inner ℝ p Y /m := by simp [timeDifferential, div_eq_mul_inv, mul_comm]
@[simp] lemma spaceDifferential_apply (e m : ℝ) (p Y : E) :
    spaceDifferential e m p Y = Y + (inner ℝ p Y/(m*(e+m))) • p := by
  simp [spaceDifferential, div_eq_mul_inv, mul_comm]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

def compactRoot (s : ℝ) : ℝ := Real.sqrt (1+s^2)
def compactSpatial (e m : ℝ) (p : E) (z : ℝ × E) : E :=
  z.2 + (compactRoot z.1/m + inner ℝ p z.2/(m*(e+m))) • p
def compactScale (e m : ℝ) (p : E) (z : ℝ × E) : ℝ := ‖compactSpatial e m p z‖

@[simp] lemma compactRoot_zero : compactRoot 0 = 1 := by simp [compactRoot]

@[simp] lemma compactSpatial_zero (e m : ℝ) (p n : E) :
    compactSpatial e m p (0,n) = boundarySpatial e m p n := by
  simp [compactSpatial, boundarySpatial]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

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
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def logAffineCompactMap (L : Point →L[ℝ] Point) (f : Point → Point) (x : Point) : Point :=
  L x + f (inverseLogRadiusChart x)

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice
open scoped ContDiff

def radialLinear : Point →L[ℝ] Point :=
  (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).smulRight (basis 0)

def compactPolar (φ : Angle → E) (z : Point) : ℝ × E :=
  (z 0, φ (angularProjection z))

def compactAngle (e m : ℝ) (p : E) (z : ℝ × E) : E :=
  (compactScale e m p z)⁻¹ • compactSpatial e m p z

def compactLorentzCoefficients (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (z : Point) : Point :=
  slice (Real.log (compactScale e m p (compactPolar φ z)))
    (ψ (compactAngle e m p (compactPolar φ z)))

def logLorentzChart (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) : Point → Point :=
  logAffineCompactMap radialLinear (compactLorentzCoefficients e m p φ ψ)

def lorentzPolarChart (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (y : Point) : Point :=
  let v := hyperbolicMap e m p (y 0 • φ (angularProjection y))
  slice ‖v‖ (ψ (‖v‖⁻¹ • v))

end
end CKSLorentz

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

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

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
open Set Filter CKSCalculus
open scoped Topology ContDiff

def boundaryProjection : Point →L[ℝ] Point :=
  ContinuousLinearMap.id ℝ Point -
    (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).smulRight (basis 0)

@[simp] lemma boundaryProjection_zero (z : Point) : boundaryProjection z 0 = 0 := by
  simp [boundaryProjection,basis]

@[simp] lemma boundaryProjection_idem (z : Point) :
    boundaryProjection (boundaryProjection z) = boundaryProjection z := by
  simp [boundaryProjection, basis]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

namespace FiniteLogDecay
variable {j : ℕ} {q r : ℝ} {U : Set Point} {f g : Point → ℝ}

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff
namespace FiniteLogDecay

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

def compactLeadingCoefficient (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (q : ℝ) (M : Angle → ℝ) (z : Point) : ℝ :=
  Real.exp (-q*compactLorentzCoefficients e m p φ ψ z 0) *
    M (angularProjection (compactLorentzCoefficients e m p φ ψ z))

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set
open scoped ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set
open scoped ContDiff Topology

def squareRadialChart (z : Point) : Point := slice ((z 0)^2) (angularProjection z)

@[simp] lemma angularProjection_squareRadialChart (z : Point) :
    angularProjection (squareRadialChart z) = angularProjection z := by
  ext a
  simp [squareRadialChart,angularProjection]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set
open scoped ContDiff Topology

def lorentzLogJac (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (a i : I) (z : Point) : ℝ :=
  (if a=0 ∧ i=0 then 1 else 0) +
    backwardScaledD a (fun w => compactLorentzCoefficients e m p φ ψ w i) z

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def logCovariantPullback (J : I → I → Point → ℝ) (T : I → I → Point → ℝ)
    (a b : I) (x : Point) : ℝ := ∑ i, ∑ k, J a i x * J b k x * T i k x

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def angularLeadingEntry (C : I → I → Point → ℝ) (i k : I) (z : Point) : ℝ :=
  if i≠0 ∧ k≠0 then C i k z else 0

def transformedAngularLeading (J C : I → I → Point → ℝ) (a b : I) (z : Point) : ℝ :=
  ∑ i, ∑ k, J a i z * J b k z * angularLeadingEntry C i k z

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set
open scoped ContDiff

def radialIndexWeight (i k : I) : ℝ := (if i=0 then 1 else 0)+(if k=0 then 1 else 0)

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

def oldLogTensor (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (A : I → I → Point → ℝ) (i k : I) (x : Point) : ℝ :=
  radiusPower (radialIndexWeight i k) (logLorentzChart e m p φ ψ x) *
    A i k (logRadiusChart (logLorentzChart e m p φ ψ x))

def lorentzLogTensor (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (A : I → I → Point → ℝ) : I → I → Point → ℝ :=
  logCovariantPullback (fun a i x => lorentzLogJac e m p φ ψ a i (inverseLogRadiusChart x))
    (oldLogTensor e m p φ ψ A)

def compactAngularCoefficient (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (mg : I → I → Angle → ℝ) (i k : I) : Point → ℝ :=
  compactLeadingCoefficient e m p φ ψ 1 (mg i k)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

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

def lorentzOrdinaryTensor (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (A : I → I → Point → ℝ) (a b : I) (y : Point) : ℝ :=
  radiusPower (-radialIndexWeight a b) (radialLogChart y) *
    lorentzLogTensor e m p φ ψ A a b (radialLogChart y)

def lorentzRadialLeading (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (mr : Angle → ℝ) (θ : Angle) : ℝ :=
  compactLeadingCoefficient e m p φ ψ 3 mr (slice 0 θ)

def lorentzAngularLeading (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (mg : I → I → Angle → ℝ) (a b : I) (θ : Angle) : ℝ :=
  transformedAngularLeading (lorentzLogJac e m p φ ψ)
    (compactAngularCoefficient e m p φ ψ mg) a b (slice 0 θ)

@[simp] lemma lorentzOrdinaryTensor_log (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (A : I → I → Point → ℝ) (a b : I) (x : Point) :
    lorentzOrdinaryTensor e m p φ ψ A a b (logRadiusChart x) =
      radiusPower (-radialIndexWeight a b) x * lorentzLogTensor e m p φ ψ A a b x := by
  simp only [lorentzOrdinaryTensor,radialLogChart_logRadiusChart]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice

def coordinateTensorPullback (F : Point → Point) (A : I → I → Point → ℝ)
    (a b : I) (y : Point) : ℝ :=
  ∑ i, ∑ k, D (basis a) (fun z => F z i) y *
    D (basis b) (fun z => F z k) y * A i k (F y)

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

namespace SmoothAngularPatch

end SmoothAngularPatch

theorem stereoDimension : Fact (Module.finrank ℝ E = 2+1) := ⟨by simp [E]⟩

attribute [local instance] stereoDimension

def stereoAngleEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] Angle :=
  EuclideanSpace.equiv (Fin 2) ℝ

def stereoAngularChart (v : Sphere) : OpenPartialHomeomorph Sphere Angle :=
  (stereographic' 2 v).trans stereoAngleEquiv.toHomeomorph.toOpenPartialHomeomorph

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
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

structure BoostPatchEstimates (e : ℝ) (p : E) (Q : CKSTensorPatch)
    (P : SmoothAngularPatch) (θ : Angle) (δ R : ℝ) : Prop where
  radius_pos : 0 < R
  ball_pos : 0 < δ
  ball_target : Metric.ball θ δ ⊆ P.chart.target
  metric_CKS : SourceCKSComponents 3 6 (angularRadialTail R (Metric.ball θ δ))
    (lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension Q.metric)
    (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg)
  second_CKS : SourceCKSComponents 2 5 (angularRadialTail R (Metric.ball θ δ))
    (lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension Q.second)
    (fun _ => 0)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK)
  radial_smooth : ContDiffOn ℝ ∞
    (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr) (Metric.ball θ δ)
  angular_smooth : ∀ i k, ContDiffOn ℝ ∞
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg i k) (Metric.ball θ δ)
  second_smooth : ∀ i k, ContDiffOn ℝ ∞
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK i k) (Metric.ball θ δ)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def boostedDirection (e m : ℝ) (p : E) (φ : Angle → E) (y : Point) : E :=
  let v := hyperbolicMap e m p (y 0 • φ (angularProjection y))
  ‖v‖⁻¹ • v

structure GenuineBoostPatch (e : ℝ) (p : E) (he : ‖p‖ < e) (Q : CKSTensorPatch)
    (P : SmoothAngularPatch) (θ : Angle) (δ R : ℝ) : Prop where
  estimates : BoostPatchEstimates e p Q P θ δ R
  boundary_image : ∀ η ∈ Metric.ball θ δ,
    boundary e p he (P.chart.symm η) ∈ Q.patch.sphereRegion Q.region
  chart_image : ∀ y ∈ angularRadialTail R (Metric.ball θ δ),
    ∃ n : Sphere, n ∈ Q.patch.sphereRegion Q.region ∧
      (n:E)=boostedDirection e (mass e p) p P.param y
  genuine_tensor : ∀ y ∈ angularRadialTail R (Metric.ball θ δ),
    ∀ (A : I → I → Point → ℝ) (a b : I),
      lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension A a b y =
      coordinateTensorPullback (lorentzPolarChart e (mass e p) p P.param Q.patch.extension) A a b y
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice
attribute [local instance] real_continuousAdd

def spatialTensorPullback (F : E → E) (A : SpatialTensor) : SpatialTensor :=
  fun x => (A (F x)).bilinearComp (fderiv ℝ F x) (fderiv ℝ F x)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

structure SpatialBoostPatch (e : ℝ) (p : E) (he : ‖p‖ < e) (A B : SpatialTensor)
    (Q : CKSTensorPatch) (P : SmoothAngularPatch) (θ : Angle) (δ R : ℝ) : Prop where
  genuine : GenuineBoostPatch e p he Q P θ δ R
  old_tail : MapsTo (lorentzPolarChart e (mass e p) p P.param Q.patch.extension)
    (angularRadialTail R (Metric.ball θ δ)) (angularRadialTail Q.radius Q.region)
  metric_CKS : SourceCKSComponents 3 6 (angularRadialTail R (Metric.ball θ δ))
    (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A))
    (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg)
  second_CKS : SourceCKSComponents 2 5 (angularRadialTail R (Metric.ball θ δ))
    (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) B))
    (fun _ => 0) (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK)
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
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

end
end CKSLorentz

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
open Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped Topology ContDiff

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry
open CKSAngularGeometry (metricBlock AmbientMat)

def cksSourceFields (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) : SourceTensorFields where
  base := {
    sigma := σ
    mg := fun θ a b => mg a.succ b.succ θ
    mK := fun θ a b => mK a.succ b.succ θ
    mr := mr
    eg := fun y a b => A a.succ b.succ y-ordinaryLeadingComponent 1 (mg a.succ b.succ) y
    ek := fun y a b => B a.succ b.succ y-ordinaryLeadingComponent 1 (mK a.succ b.succ) y
    b := fun y a => A 0 a.succ y
    err := fun y => A 0 0 y-ordinaryLeadingComponent 5 mr y }
  kr := B 0 0
  kb := fun y a => B 0 a.succ y

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Set
open CKSAngularGeometry (metricBlock AmbientMat)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def boostSourceFields (e : ℝ) (p : E) (A B : SpatialTensor)
    (Q : CKSTensorPatch) (P : SmoothAngularPatch) : SourceTensorFields :=
  cksSourceFields (angularRoundMetric P.param)
    (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A))
    (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) B))
    (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK)
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set CKSAngularSlice CKSCalculus
open scoped ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open scoped Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set CKSAngularSlice
open scoped Matrix.Norms.Elementwise

def SourceTensorFields.UniformCollarInput (f : SourceTensorFields)
    (K : Set MatrixThreeJet) (C R : ℝ) (W : Set Angle) : Prop :=
  ∀ η ∈ W, ∀ ρ : ℝ,
    matrixThreeJets (angularLift f.base.sigma) (slice ρ η) ∈ K ∧
    ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ η)‖ ≤ C ∧
    ‖matrixThreeJets (angularLift f.base.mg) (slice ρ η)‖ ≤ C ∧
    ‖matrixScalarJets (angularLift f.base.mK) (slice ρ η)‖ ≤ C ∧
    ‖actualScalarJet (angularLift f.base.mr) (slice ρ η)‖ ≤ C ∧
    (R < Real.exp ρ → f.ComponentBounds C (logRadiusChart (slice ρ η)))
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSTensorNaturality
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end
end CKSTensorNaturality

end

noncomputable section
namespace CKSTensorNaturality
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end
end CKSTensorNaturality

end

noncomputable section
namespace CKSTensorNaturality
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [completeF : CompleteSpace F]

end
end CKSTensorNaturality

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalAngularJet (γ : PhysicalPoint → Mat) (x : PhysicalPoint) : Jet :=
  (γ x, (fun i j k => D (CKSRealizedRound.basis i.succ) (fun y => γ y j k) x),
    fun a i j k => D (CKSRealizedRound.basis a.succ)
      (fun y => D (CKSRealizedRound.basis i.succ) (fun z => γ z j k) y) x)

def physicalAngularScalarJet (U : PhysicalPoint → ℝ) (x : PhysicalPoint) : ScalarJet :=
  (U x, (fun i => D (CKSRealizedRound.basis i.succ) U x),
    fun i j => D (CKSRealizedRound.basis i.succ)
      (D (CKSRealizedRound.basis j.succ) U) x)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def leafTensorTrace (γ T : Mat) : ℝ := (γ⁻¹ * T).trace

def leafTensorTraceFree (γ T : Mat) : Mat := T - (leafTensorTrace γ T / 2) • γ

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLeafCalculus
noncomputable section
open Matrix CKSCalculus CKSAngularGeometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLeafCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped BigOperators Topology ContDiff NNReal Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLeafCalculus
noncomputable section
open Matrix CKSAngularGeometry
open scoped BigOperators

end
end CKSLeafCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSLeafCalculus
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

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

def sourceH (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) : ℝ :=
  leafTensorTrace (γ x) (sourceChi U γ s x)
def sourceP (γ T : PhysicalPoint → Mat) (x : PhysicalPoint) : ℝ :=
  leafTensorTrace (γ x) (T x)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def sourceD (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (y : PhysicalPoint) : ℝ :=
  y 0 * sourceH U γ s y / (2*U y)

def sourceMass (U : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) : PhysicalPoint → ℝ :=
  CKSFrame.massField (sourceH U γ s) (sourceP γ T)

def physicalBaseLapse (r : ℝ) : ℝ := r*Real.sqrt (1+(1/r)^2)

def physicalMomentumInput (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ) : MomentumInput :=
  let r := x 0
  let t := fun y => sourceP γ T y/2
  (1/r,w,rescale (1/r^2) (physicalAngularJet γ x),
    ![r^3 • ((1/physicalBaseLapse r) • physicalAngularScalarJet U x-constantJet 1),
      r^3 • (physicalAngularScalarJet t x-constantJet 1),
      r^3 • (physicalAngularScalarJet L x-constantJet (1+w/r^2)),
      r^4 • physicalAngularScalarJet (D (CKSRealizedRound.basis 0) t) x,
      r^3 • (physicalAngularScalarJet (sourceD U γ s) x-constantJet 1)],
    r^5 • (fun a => physicalAngularScalarJet (fun y => s y a) x),
    r^2 • (fun a => physicalAngularScalarJet (fun y => η y a) x),
    r • (fun a b => physicalAngularScalarJet (fun y => leafTensorTraceFree (γ y) (T y) a b) x),
    r • leafTensorTraceFree (γ x) (sourceChi U γ s x),
    r^3 • (fun a => D (CKSRealizedRound.basis 0) (fun y => η y a) x))

def physicalNullInput (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ) : NullInput :=
  (physicalMomentumInput U L γ T s η x w,physicalAngularScalarJet (sourceMass U γ T s) x,
    (x 0)^2*(D (CKSRealizedRound.basis 0) (sourceMass U γ T s) x-w/(x 0*Real.sqrt (x 0))))

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def leafRadialRate (γ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (x : PhysicalPoint) : Mat := fun a b =>
  D (CKSRealizedRound.basis 0) (fun y => γ y a b) x-
    ∑ c, (s x c*D (CKSRealizedRound.basis c.succ) (fun y => γ y a b) x+
      γ x c b*D (CKSRealizedRound.basis a.succ) (fun y => s y c) x+
      γ x a c*D (CKSRealizedRound.basis b.succ) (fun y => s y c) x)

def radialExpansion (γ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (x : PhysicalPoint) : ℝ := x 0/4*leafTensorTrace (γ x) (leafRadialRate γ s x)

def radialMassRadical (t F : PhysicalPoint → ℝ) (x : PhysicalPoint) : ℝ :=
  1+(x 0*t x)^2-2*F x/x 0

def radialMassLapse (γ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (t F : PhysicalPoint → ℝ) (x : PhysicalPoint) : ℝ :=
  Real.sqrt (radialMassRadical t F x)/radialExpansion γ s x

def radialTangential (γ : PhysicalPoint → Mat) (t : PhysicalPoint → ℝ)
    (τ : PhysicalPoint → Mat) (x : PhysicalPoint) : Mat :=
  t x • γ x+leafTensorTraceFree (γ x) (τ x)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSTensorNaturality CKSCalculus
open scoped BigOperators Matrix.Norms.Elementwise

def radialFlow (s : PhysicalPoint → Point) (x : PhysicalPoint) : PhysicalPoint :=
  CKSRealizedRound.basis 0-∑ a : Fin 2, s x a • CKSRealizedRound.basis a.succ
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSTensorNaturality CKSCalculus
open scoped BigOperators Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSTensorNaturality CKSCalculus
open scoped BigOperators Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSAngularSlice CKSMixedGeometry

def angularChange (φ : Point → Point) (x : PhysicalPoint) : PhysicalPoint :=
  slice (x 0) (φ (angularProjection x))

def angularJacobian (φ : Point → Point) (x : PhysicalPoint) : Mat :=
  fun a b => fderiv ℝ φ (angularProjection x) (CKSAngularGeometry.basis b) a

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry CKSTensorNaturality
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
@[simp] lemma angularChange_zero (φ : Point → Point) (x : PhysicalPoint) :
    angularChange φ x 0 = x 0 := by simp [angularChange]
@[simp] lemma angularChange_succ (φ : Point → Point) (x : PhysicalPoint) (a : Fin 2) :
    angularChange φ x a.succ = φ (angularProjection x) a := by simp [angularChange]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry CKSTensorNaturality
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

@[simp] lemma radialFlow_zero (s : PhysicalPoint → Point) (x : PhysicalPoint) :
    radialFlow s x 0 = 1 := by simp [radialFlow,CKSRealizedRound.basis]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry CKSTensorNaturality
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def radiusLogPoint (x : PhysicalPoint) : PhysicalPoint :=
  fun i => if i=0 then Real.log (x 0) else x i

@[simp] lemma radiusLogPoint_slice (r : ℝ) (a : Point) :
    radiusLogPoint (slice r a) = slice (Real.log r) a := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radiusLogPoint]
  · simp [radiusLogPoint]

@[simp] lemma radiusLogPoint_logRadiusChart (x : PhysicalPoint) :
    radiusLogPoint (CKSMixedGeometry.logRadiusChart x) = x := by
  ext i
  by_cases hi : i=0
  · subst i; simp [radiusLogPoint, CKSMixedGeometry.logRadiusChart]
  · simp [radiusLogPoint, CKSMixedGeometry.logRadiusChart, hi]

@[simp] lemma logRadiusChart_radiusLogPoint {x : PhysicalPoint} (hr : 0 < x 0) :
    CKSMixedGeometry.logRadiusChart (radiusLogPoint x) = x := by
  ext i
  by_cases hi : i=0
  · subst i; simp [radiusLogPoint, CKSMixedGeometry.logRadiusChart, Real.exp_log hr]
  · simp [radiusLogPoint, CKSMixedGeometry.logRadiusChart, hi]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalCollarGamma (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : Mat :=
  (x 0)^2 • collarQ R f (radiusLogPoint x)
def physicalCollarShift (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : Point :=
  collarShift R f (radiusLogPoint x)
def physicalCollarT (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : ℝ :=
  collarT R f (radiusLogPoint x)
def physicalCollarF (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : ℝ :=
  collarF R f (radiusLogPoint x)
def physicalCollarL (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : ℝ :=
  collarL R f (radiusLogPoint x)
def physicalCollarEta (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : Point :=
  x 0 • collarEtaDivR R f (radiusLogPoint x)

def physicalCollarRawTau (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : Mat :=
  ((x 0)^2*(1-roundingWeight R (x 0))) • f.tauDivR2 (radiusLogPoint x)
def physicalCollarU (R : ℝ) (f : LogCollarData) : PhysicalPoint → ℝ :=
  radialMassLapse (physicalCollarGamma R f) (physicalCollarShift R f)
    (physicalCollarT R f) (physicalCollarF R f)
def physicalCollarTangential (R : ℝ) (f : LogCollarData) : PhysicalPoint → Mat :=
  radialTangential (physicalCollarGamma R f) (physicalCollarT R f) (physicalCollarRawTau R f)
def physicalCollarMetric (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : AmbientMat :=
  foliationMetric (physicalCollarU R f x) (physicalCollarGamma R f x) (physicalCollarShift R f x)
def physicalCollarTensor (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : AmbientMat :=
  foliationTensor (physicalCollarU R f x) (physicalCollarL R f x)
    (physicalCollarEta R f x) (physicalCollarTangential R f x) (physicalCollarShift R f x)
def physicalCollarFrame (R : ℝ) (f : LogCollarData) : LocalFrame :=
  fun i x => adaptedFrame (physicalCollarU R f x) (physicalCollarGamma R f x)
    (physicalCollarShift R f x) i

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter CKSBending Set
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open Matrix CKSAngularGeometry

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry
open scoped Topology ContDiff
@[simp] lemma angularProjection_radiusLogPoint (x : PhysicalPoint) :
    angularProjection (radiusLogPoint x) = angularProjection x := by
  ext a
  simp [angularProjection,radiusLogPoint]
@[simp] lemma angularJacobian_radiusLogPoint (φ : Point → Point) (x : PhysicalPoint) :
    angularJacobian φ (radiusLogPoint x) = angularJacobian φ x := by
  unfold angularJacobian
  rw [angularProjection_radiusLogPoint]
@[simp] lemma angularChange_radiusLogPoint (φ : Point → Point) (x : PhysicalPoint) :
    angularChange φ (radiusLogPoint x) = radiusLogPoint (angularChange φ x) := by
  simp [angularChange,radiusLogPoint_slice,radiusLogPoint]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter CKSBending Set
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSAngularGeometry
open scoped Topology ContDiff

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def sourceFrame (f : SourceMassFields) : LocalFrame :=
  fun i x => adaptedFrame (sourceLapse f x) (sourceGamma f x) (sourceShift f x) i

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSBending
noncomputable section
open CKSCalculus Filter CKSAngularGeometry
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSBending

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSAngularGeometry

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix Filter CKSAngularGeometry CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise
@[simp] lemma angularProjection_angularChange (φ : Angle → Angle) (x : Point) :
    angularProjection (angularChange φ x) = φ (angularProjection x) := by
  ext a; simp [angularProjection,angularChange]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix Filter CKSAngularGeometry CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry CKSAngularSlice

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise Matrix

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set CKSAngularGeometry

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry CKSAngularSlice
@[simp] lemma angularJacobian_logRadiusChart (φ : Point → Point) (x : PhysicalPoint) :
    angularJacobian φ (logRadiusChart x) = angularJacobian φ x := by
  unfold angularJacobian
  rw [angularProjection_logRadiusChart]
@[simp] lemma angularChange_logRadiusChart (φ : Point → Point) (x : PhysicalPoint) :
    angularChange φ (logRadiusChart x) = logRadiusChart (angularChange φ x) := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart,angularChange]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix Filter CKSAngularGeometry CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

structure SourceMassFields.SmoothAt (f : SourceMassFields) (y : Point) : Prop where
  sigma : ContDiffAt ℝ ∞ f.sigma (angularProjection y)
  mg : ContDiffAt ℝ ∞ f.mg (angularProjection y)
  mK : ContDiffAt ℝ ∞ f.mK (angularProjection y)
  mr : ContDiffAt ℝ ∞ f.mr (angularProjection y)
  eg : ContDiffAt ℝ ∞ f.eg y
  ek : ContDiffAt ℝ ∞ f.ek y
  b : ContDiffAt ℝ ∞ f.b y
  err : ContDiffAt ℝ ∞ f.err y

structure SourceTensorFields.SmoothAt (f : SourceTensorFields) (y : Point) : Prop where
  base : f.base.SmoothAt y
  kr : ContDiffAt ℝ ∞ f.kr y
  kb : ContDiffAt ℝ ∞ f.kb y

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry

abbrev spatialSourceFields (P : SmoothAngularPatch) (A B : SpatialTensor)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) : SourceTensorFields :=
  cksSourceFields (angularRoundMetric P.param) (polarTensorComponents P A)
    (polarTensorComponents P B) mr mg mK
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Filter
open scoped Topology

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

def flowEnergy (p : E) (t : ℝ) : ℝ := Real.sqrt (1+t^2*‖p‖^2)
def flowCoeff (p : E) (t : ℝ) : ℝ := t^2/(flowEnergy p t+1)
def flowD (p : E) (t : ℝ) (n : E) : ℝ := flowEnergy p t+t*inner ℝ p n
def flowS (p : E) (t : ℝ) (n : E) : E := n+(t+flowCoeff p t*inner ℝ p n) • p
def flowPhi (p : E) (t : ℝ) (n : E) : E := (flowD p t n)⁻¹ • flowS p t n

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

def paddingCharge (R : ℝ) : ℝ := paddingMass R (2*R) + 2/Real.sqrt (2*R)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open Set

def normalizeAmbient (x : E) : E := ‖x‖⁻¹ • x

def weightedPullback (p : E) (t : ℝ) (F : E → ℝ) (x : E) : ℝ :=
  (flowD p t x)⁻¹ ^2 * F (flowPhi p t x)

def normalizedPullback (p : E) (F : E → ℝ) (z : ℝ × E) : ℝ :=
  weightedPullback p z.1 F (normalizeAmbient z.2)

lemma normalizeAmbient_smooth {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ normalizeAmbient x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

@[simp] lemma normalizeAmbient_sphere (n : Sphere) : normalizeAmbient n = n := by
  simp [normalizeAmbient]

@[simp] lemma normalizedPullback_sphere (p : E) (F : E → ℝ) (t : ℝ) (n : Sphere) :
    normalizedPullback p F (t,(n:E)) = weightedPullback p t F n := by
  simp [normalizedPullback]

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere radialExtension radialExtension_smooth radialExtension_on_sphere surfaceMeasure)

def aspectPullback (e : ℝ) (p : E) (he : ‖p‖ < e) (M : Sphere → ℝ) (n : Sphere) : ℝ :=
  (denominator e (mass e p) p n)⁻¹ ^3 * M (boundary e p he n)

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure Balanced sphereIntegral sphereArea)

def heatDatum (M : Sphere → ℝ) (hM : SmoothSphere M) : C(Sphere,ℝ) :=
  ⟨fun n => M n/4, hM.continuous.div_const 4⟩

end
end CKSLorentz

end

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
    ((polarParam_contDiffAt P hy).differentiableAt (by simp)),fderiv_id] at hg
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
namespace CKSMetricGluing
noncomputable section
open Bundle Manifold Set Bornology
open scoped Bundle Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] real_continuousAdd

variable {I}

end
end CKSMetricGluing

end

noncomputable section
namespace CKSMetricGluing
noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

end
end CKSMetricGluing

end

noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators
abbrev V := Fin 3 → ℝ
abbrev Mat := Fin 3 → Fin 3 → ℝ
abbrev Bil := V →L[ℝ] V →L[ℝ] ℝ

def matrixBilinear (G : Mat) : Bil :=
  ∑ i : Fin 3, ∑ j : Fin 3, G i j •
    (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj j)
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ V H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
abbrev TangentTriv := Trivialization V (π V (fun x : M => TangentSpace I x))
local instance scalarAtlas : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℝ) :=
  ⟨by rfl⟩
def bilinearTriv (e : TangentTriv I (M := M)) [MemTrivializationAtlas e] :
    Trivialization Bil (π Bil (fun x : M =>
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  e.continuousLinearMap (RingHom.id ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Bundle.Trivial.trivialization M ℝ))

end
end CKSTangentCoefficients

end

noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators Topology

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] scalarAtlas
instance bilinearTriv_atlas (e : TangentTriv I (M := M)) [MemTrivializationAtlas e] :
    MemTrivializationAtlas (bilinearTriv I e) := by unfold bilinearTriv; infer_instance
@[simp] lemma bilinearTriv_baseSet (e : TangentTriv I (M := M)) [MemTrivializationAtlas e] :
    (bilinearTriv I e).baseSet = e.baseSet := by simp [bilinearTriv]

end
end CKSTangentCoefficients

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients

def polarLift (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ) : SpatialTensor :=
  fun x => (matrixBilinear (F (polarInverse P x))).bilinearComp
    (fderiv ℝ (polarInverse P) x) (fderiv ℝ (polarInverse P) x)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped BigOperators

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set CKSAngularGeometry

end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
open scoped BigOperators

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped ContDiff Matrix.Norms.Elementwise
local instance bilNorm : NormedAddCommGroup CKSTangentCoefficients.Bil :=
  ContinuousLinearMap.toNormedAddCommGroup (E := CKSTangentCoefficients.V) (F := CKSTangentCoefficients.V →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance bilSpace : NormedSpace ℝ CKSTangentCoefficients.Bil := ContinuousLinearMap.toNormedSpace
local instance epNorm : NormedAddCommGroup (E →L[ℝ] Point →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := Point →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance epSpace : NormedSpace ℝ (E →L[ℝ] Point →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance peNorm : NormedAddCommGroup (Point →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := Point) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance peSpace : NormedSpace ℝ (Point →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance eeNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance eeSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Set Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
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
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise

structure PhysicalRegularAt (g k : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : Prop where
  metric_smooth : ContDiffAt ℝ ∞ g x
  tensor_smooth : ContDiffAt ℝ ∞ k x
  metric_positive : (g x).PosDef
  tensor_symmetric : (k x).IsHermitian
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

structure CollarSourcePatch (A B : SpatialTensor) where
  patch : SmoothAngularPatch
  region : Set Angle
  region_open : IsOpen region
  region_target : region ⊆ patch.chart.target
  radius : ℝ
  mr : Angle → ℝ
  mg : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ
  mK : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ
  metric_CKS : SourceCKSComponents 3 6 (angularRadialTail radius region)
    (polarTensorComponents patch A) mr mg
  tensor_CKS : SourceCKSComponents 2 5 (angularRadialTail radius region)
    (polarTensorComponents patch B) (fun _ => 0) mK

def CollarSourcePatch.fields {A B : SpatialTensor} (Q : CollarSourcePatch A B) : SourceTensorFields :=
  spatialSourceFields Q.patch A B Q.mr Q.mg Q.mK

def CollarSourcePatch.metric {A B : SpatialTensor} (Q : CollarSourcePatch A B) (R : ℝ) : SpatialTensor :=
  polarLift Q.patch (physicalCollarMetric R (sourceCollarData Q.fields.logFields))
def CollarSourcePatch.tensor {A B : SpatialTensor} (Q : CollarSourcePatch A B) (R : ℝ) : SpatialTensor :=
  polarLift Q.patch (physicalCollarTensor R (sourceCollarData Q.fields.logFields))
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def spatialDirection (x : E) : Sphere := if h : x = 0 then
  Classical.choice ((NormedSpace.sphere_nonempty.mpr (zero_le_one : (0:ℝ) ≤ 1)).coe_sort : Nonempty Sphere) else
  ⟨normalizeAmbient x, by
    simp only [Metric.mem_sphere,dist_zero_right,normalizeAmbient,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)⟩
def polarCone (P : SmoothAngularPatch) (W : Set Angle) : Set E :=
  {x | x ≠ 0 ∧ spatialDirection x ∈ P.sphereRegion W}
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

structure SourceCollarAtlas (A B : SpatialTensor) (ι : Type*) where
  patch : ι → CollarSourcePatch A B
  radius : ℝ
  radius_pos : 0 < radius
  jetSet : Set CKSMixedGeometry.MatrixThreeJet
  jetSet_compact : IsCompact jetSet
  jetSet_positive : ∀ q ∈ jetSet, Matrix.PosDef (fun i k => (q i k).1.1)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounds : ∀ i, (patch i).fields.UniformCollarInput jetSet bound radius (patch i).region
  source_smooth : ∀ i y, y ∈ angularRadialTail radius (patch i).region → (patch i).fields.SmoothAt y
  source_positive : ∀ i y, y ∈ angularRadialTail radius (patch i).region → (sourceMetric (patch i).fields.base y).PosDef
  source_symmetric : ∀ i y, y ∈ angularRadialTail radius (patch i).region → (sourceTangentialK (patch i).fields.base y).IsHermitian
  source_DEC : ∀ i y, y ∈ angularRadialTail radius (patch i).region →
    physicalDEC (sourceMetric (patch i).fields.base) (sourceTensor (patch i).fields)
      (sourceFrame (patch i).fields.base) y
  covers : ∀ n : Sphere, ∃ i, n ∈ (patch i).patch.sphereRegion (patch i).region

def SourceCollarAtlas.localIndex {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (x : E) : ι := Classical.choose (q.covers (spatialDirection x))
def SourceCollarAtlas.metric {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (R : ℝ) : SpatialTensor := fun x => (q.patch (q.localIndex x)).metric R x
def SourceCollarAtlas.tensor {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (R : ℝ) : SpatialTensor := fun x => (q.patch (q.localIndex x)).tensor R x
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
local instance globalCollarEeNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance globalCollarEeSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Matrix
open CKSAngularGeometry (metricBlock AmbientMat)

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Set Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Set Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularSlice CKSAngularGeometry CKSBending Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter MeasureTheory CKSSphericalHarmonics CKSSphericalChart CKSBending CKSInducedSphere
open scoped Topology ContDiff

def unitVector (x : E) : E := ‖x‖⁻¹ • x

def cartMass (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : ℝ :=
  paddingMass R ‖x‖ + canonicalF f₀ m (heatTime R ‖x‖) (unitVector x)

end
end CKSADM

end

end OAI
end

section
namespace OAI

namespace CKSSpatialManifold

end CKSSpatialManifold

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRound CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

end
end CKSSphericalChart

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSCalculus CKSAngularGeometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSAngularGeometry
open scoped BigOperators

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open Matrix CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSRealizedRound

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSAngularGeometry CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise Matrix

end
end CKSSphericalChart

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise

def radicand (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : ℝ :=
  1 + bendingV R ‖x‖ ^ 2 - 2 * cartMass f₀ m R x / ‖x‖
def metric (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : Mat :=
  1 + ((radicand f₀ m R x)⁻¹-1) • vecMulVec (normal x) (normal x)
def tensor (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : Mat :=
  (normalEntry (bendingV R) (bendingBeta R) ‖x‖ / radicand f₀ m R x) •
      vecMulVec (normal x) (normal x) +
    (bendingV R ‖x‖/‖x‖) • (1-vecMulVec (normal x) (normal x)) +
    (correctionCoeff (bendingV R) ‖x‖ / ‖x‖^2) •
      canonicalT f₀ (heatTime R ‖x‖) (unitVector x)
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
def sphericalMap (x : PhysicalPoint) : PhysicalPoint := toPoint (x 0 • sphereParam x)
def sphericalBasis (x : PhysicalPoint) (i : Fin 3) : E :=
  ![sphereParam x,x 0 • thetaFrame x,x 0 • phiFrame x] i
def physicalMetric (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : PhysicalPoint) : AmbientMat :=
  metric f₀ m R (toPoint.symm x)
def physicalTensor (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : PhysicalPoint) : AmbientMat :=
  tensor f₀ m R (toPoint.symm x)
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
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
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
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
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
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
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable def sphericalChart (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : OpenPartialHomeomorph PhysicalPoint PhysicalPoint :=
  sphericalMap_smooth.contDiffAt.toOpenPartialHomeomorph sphericalMap
    (sphericalDerivative_hasFDerivAt x hx hs) (by simp)
@[simp] lemma sphericalChart_coe (x : PhysicalPoint) (hx : x 0≠0)
    (hs : Real.sin (x 1)≠0) : (sphericalChart x hx hs : PhysicalPoint → PhysicalPoint) = sphericalMap := rfl

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSSphericalChart

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set CKSSphericalChart CKSRealizedRound
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSBending
noncomputable section
open Set
open scoped Topology ContDiff

end
end CKSBending

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSBending Set
open scoped ContDiff

end
end CKSAngularSlice

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Matrix Set Filter CKSCalculus CKSRealizedRound CKSAngularGeometry CKSAngularSlice CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSSphericalChart

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRealizedRound CKSAngularGeometry CKSAngularSlice CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSSphericalChart

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSTangentCoefficients

def spatialMatrix (F : E → AmbientMat) : SpatialTensor := fun x =>
  (matrixBilinear (F x)).bilinearComp (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSCalculus Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSTangentCoefficients CKSCartesianOuter CKSInducedSphere CKSSphericalChart
open scoped BigOperators

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
open scoped Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
  CKSADM CKSBending CKSSphericalHarmonics CKSInducedSphere
open CKSRealizedRound (correctionCoeff)
open scoped Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
  CKSSphericalHarmonics CKSBending Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Filter
open scoped Topology ContDiff

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

def SourceCollarAtlas.HasMassAspect {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (M : Sphere → ℝ) : Prop :=
  ∀ i θ, θ ∈ (q.patch i).region →
    cksChartMassAspect (q.patch i).patch.param (q.patch i).mr
      (q.patch i).mg (q.patch i).mK θ = M ((q.patch i).patch.chart.symm θ)

def SourceCollarAtlas.replacementMetric {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m R : ℝ) : SpatialTensor := fun x =>
  if ‖x‖ ≤ R then sourceSpatial A x else
  if ‖x‖ ≤ 3*R then q.metric R x else spatialMatrix (CKSCartesianOuter.metric f₀ m R) x
def SourceCollarAtlas.replacementTensor {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m R : ℝ) : SpatialTensor := fun x =>
  if ‖x‖ ≤ R then sourceSpatial B x else
  if ‖x‖ ≤ 3*R then q.tensor R x else spatialMatrix (CKSCartesianOuter.tensor f₀ m R) x
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients
open scoped ContDiff Matrix.Norms.Elementwise
local instance smrbilNorm : NormedAddCommGroup CKSTangentCoefficients.Bil :=
  ContinuousLinearMap.toNormedAddCommGroup (E := CKSTangentCoefficients.V) (F := CKSTangentCoefficients.V →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance smrbilSpace : NormedSpace ℝ CKSTangentCoefficients.Bil := ContinuousLinearMap.toNormedSpace
local instance smrepNorm : NormedAddCommGroup (E →L[ℝ] Point →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := Point →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance smrepSpace : NormedSpace ℝ (E →L[ℝ] Point →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance smrpeNorm : NormedAddCommGroup (Point →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := Point) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance smrpeSpace : NormedSpace ℝ (Point →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance smreeNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance smreeSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularGeometry
open scoped ContDiff Matrix.Norms.Elementwise

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry

end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

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
    ((polarParam_contDiffAt P hy).differentiableAt (by simp)),ContinuousLinearEquiv.fderiv]
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
open CKSMixedGeometry CKSAngularGeometry
open scoped BigOperators

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry
open scoped BigOperators

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry Matrix Set Filter
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise

end
end CKSAngularGeometry

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
open CKSMixedGeometry CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

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

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open Matrix

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics MeasureTheory

attribute [local instance] sixteen_atLeastTwo

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped Topology ContDiff

end
end CKSLorentz

end

noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set
abbrev E := EuclideanSpace ℝ (Fin 3)

def tailRegion (L : ℝ) : Set E := {x | L < ‖x‖}
end
end CKSTailVolume

end

noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set

end
end CKSTailVolume

end

noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set
open scoped ENNReal

end
end CKSTailVolume

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry MeasureTheory

def spatialMomentum (A B : SpatialTensor) (x : E) : Fin 3 → ℝ :=
  (physicalMetricJet (spatialCoefficients A) (CKSCartesianOuter.toPoint x)).momentum
    (physicalTensorJet (spatialCoefficients B) (CKSCartesianOuter.toPoint x))

def spatialVolume (A : SpatialTensor) : Measure E :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.sqrt (spatialCartesian A x).det))
end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSCartesianOuter

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics CKSBending Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end
end CKSLorentz

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Set Filter CKSLorentz
open scoped Topology
variable {M : Type*} [TopologicalSpace M]

end
end CKSSpatialManifold

end

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Bundle Manifold
open scoped Bundle Manifold ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def MetricLower (g G : Metric I (M := M)) (ε : ℝ) : Prop :=
  ∀ x (v : TangentSpace I x), (1-ε) * g.inner x v v ≤ G.inner x v v
end
end CKSReplacementCompleteness

end

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Filter
open scoped Topology ENNReal

end
end CKSReplacementCompleteness

end

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Bundle Manifold ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable [T3Space M]

end
end CKSReplacementCompleteness

end

noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set Manifold MeasureTheory Bundle CKSReplacementCompleteness
open scoped ENNReal Manifold Bundle ContDiff
universe u
def rawHausdorffArea {X : Type u} (metric : EMetricSpace X) (s : Set X) : ℝ≥0∞ :=
  letI : EMetricSpace X := metric
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  (Measure.hausdorffMeasure (2 : ℝ) : Measure X) s
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 1 M]

def OuterDomain.cut (D : OuterDomain M) : Set M :=
  D.inclusion '' (@ModelWithCorners.boundary ℝ _ E3 _ _ H3 _ I3 D.Carrier D.topology D.charts)
def IsEnclosingCut (Γ : Set M) : Prop := ∃ D : OuterDomain M, Γ = D.cut
variable [T3Space M]
def area (g : Metric I3 (M := M)) (Γ : Set M) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi / 4) * rawHausdorffArea (metricSpace I3 g) Γ
def minEnclosingArea (g : Metric I3 (M := M)) : ℝ≥0∞ :=
  ⨅ Γ : {Γ : Set M // IsEnclosingCut M Γ}, area M g Γ.val
end
end CKSGeometricCuts

end

noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
universe u

end
end CKSGeometricCuts

end

noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set Manifold MeasureTheory CKSReplacementCompleteness
open scoped ContDiff ENNReal NNReal
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H3 M]
  [IsManifold I3 1 M] [T3Space M]

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
  infer_instance

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
open Bundle Manifold Set Filter CKSLorentz CKSGeometricCuts
open scoped Bundle Manifold ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N] [T3Space N]

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
attribute [local instance] Classical.propDecidable

end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing CKSGeometricCuts
open scoped Bundle Manifold ContDiff Topology
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M] [T3Space M]

end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] CKSLorentz.hsgNorm CKSLorentz.hsgSpace

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

end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Set Filter CKSLorentz
open scoped Topology
variable {M : Type*} [TopologicalSpace M]

end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter MeasureTheory CKSLorentz CKSMetricGluing CKSGeometricCuts
open CKSSphericalHarmonics CKSADM CKSBending
open scoped Bundle Manifold ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N] [T3Space N]

end
end CKSSpatialManifold

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSBoundarySurface
section PlaneInsertion
attribute [local instance] two_atLeastTwo

end PlaneInsertion

section PlaneProjection
attribute [local instance] two_atLeastTwo

end PlaneProjection

@[simp] lemma liftPlane_zero (z : E2) : liftPlane z 0 = 0 := rfl
@[simp] lemma liftPlane_succ (z : E2) (i : Fin 2) : liftPlane z i.succ = z i := rfl
@[simp] lemma dropPlane_apply (z : E3) (i : Fin 2) : dropPlane z i = z i.succ := rfl
@[simp] lemma drop_lift (z : E2) : dropPlane (liftPlane z) = z := by ext i; rfl

@[simp] lemma I3_liftHalf (z : E2) : I3 (liftHalf z) = liftPlane z := rfl

attribute [local instance] halfSpaceDimension_neZero

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M]

end CKSBoundarySurface

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSBoundarySurface
attribute [local instance] Classical.propDecidable
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 halfSpaceDimension_neZero) I3 ∞ M _ _]

@[simp] lemma boundaryChart_source (x : Boundary M) :
    (boundaryChart x).source = Subtype.val ⁻¹' (chartAt H3 x.val).source := rfl
@[simp] lemma boundaryChart_target (x : Boundary M) :
    (boundaryChart x).target = liftHalf ⁻¹' (chartAt H3 x.val).target := rfl
@[simp] lemma boundaryChart_apply (x y : Boundary M) :
    boundaryChart x y = dropPlane (I3 (chartAt H3 x.val y.val)) := rfl

end CKSBoundarySurface

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma chartFrame_eq_symmL (x : M) {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    chartFrame x y = (trivializationAt E (TangentSpace I) x).symmL ℝ
      ((extChartAt I x).symm y) := by
  have hs : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hy
  rw [TangentBundle.symmL_trivializationAt hs, (extChartAt I x).right_inv hy]
  rfl

lemma chartFrame_continuousOn (x : M) (v : E) :
    ContinuousOn (fun y => (⟨(extChartAt I x).symm y, chartFrame x y v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target := by
  let e := trivializationAt E (TangentSpace I) x
  have h : ContinuousOn (fun y =>
      (⟨(extChartAt I x).symm y, e.symm ((extChartAt I x).symm y) v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target :=
    e.continuousOn_symm.comp
      ((continuousOn_extChartAt_symm x).prodMk continuousOn_const)
      (fun y hy => ⟨by simpa [e] using (extChartAt I x).map_target hy, mem_univ _⟩)
  apply h.congr
  intro y hy
  dsimp only
  congr 1
  rw [chartFrame_eq_symmL x hy, Trivialization.symmL_apply]
  simpa using (extChartAt I x).map_target hy

lemma chartMatrix_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartMatrix g x) (extChartAt I x).target := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  exact (chartFrame_continuousOn x (basis i)).inner_bundle
    (chartFrame_continuousOn x (basis j))

lemma chartDensity_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartDensity g x) (extChartAt I x).target := by
  exact ((continuous_id.matrix_det : Continuous (Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ)).comp_continuousOn (chartMatrix_continuousOn g x)).sqrt

end CKSIntrinsicVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
attribute [local instance] model_finiteDimensional model_borelSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

lemma chart_target_measurable [IsManifold I 1 M] (x : M) :
    MeasurableSet (extChartAt I x).target := by
  rw [extChartAt_target]
  exact ((chartAt H x).open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

variable [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]

def chartPreimage (x : M) (s : Set M) : Set E :=
  (extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target

lemma chartPreimage_measurable (x : M) {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet (chartPreimage x s) := by
  have h : Measurable ((extChartAt I x).target.domRestrict (extChartAt I x).symm) :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt_symm x)).measurable
  have hm := (chart_target_measurable x).subtype_image (hs.preimage h)
  convert hm using 1
  ext y
  simp [chartPreimage]

lemma localVolume_apply (g : Metric (M := M)) (x : M) {s : Set M} (hs : MeasurableSet s) :
    localVolume g x s = ∫⁻ y in chartPreimage x s, ENNReal.ofReal (chartDensity g x y) := by
  have hf := (continuousOn_extChartAt_symm x).aemeasurable
    (μ := (volume : Measure E)) (chart_target_measurable x)
  rw [localVolume, Measure.map_apply_of_aemeasurable
    (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hs, withDensity_apply']
  rw [← Measure.restrict_comm (chart_target_measurable x),
    Measure.restrict_restrict (chart_target_measurable x)]
  congr 1
  exact congrArg ((volume : Measure E).restrict) (inter_comm _ _)

end CKSIntrinsicVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume

abbrev stdBasis : Module.Basis (Fin 3) ℝ E := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

lemma sqrt_gram_det_comp (B : LinearMap.BilinForm ℝ E) (L : E →L[ℝ] E) :
    Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis
      (B.comp L.toLinearMap L.toLinearMap)).det =
      |L.det| * Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis B).det := by
  rw [LinearMap.BilinForm.toMatrix_comp stdBasis stdBasis,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix]
  change Real.sqrt (L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det) = _
  rw [show L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det =
    L.det ^ 2 * (LinearMap.BilinForm.toMatrix stdBasis B).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def pullbackInner (g : Metric (M := M)) (x : M) (y : E) : LinearMap.BilinForm ℝ E :=
  (g.inner ((extChartAt I x).symm y)).toBilinForm.comp
    (chartFrame x y).toLinearMap (chartFrame x y).toLinearMap

lemma chartMatrix_eq_toMatrix (g : Metric (M := M)) (x : M) (y : E) :
    chartMatrix g x y = LinearMap.BilinForm.toMatrix stdBasis (pullbackInner g x y) := by
  ext first second
  rw [LinearMap.BilinForm.toMatrix_apply]
  change g.inner ((extChartAt I x).symm y)
    (chartFrame x y (basis first)) (chartFrame x y (basis second)) =
    g.inner ((extChartAt I x).symm y)
      (chartFrame x y (stdBasis first)) (chartFrame x y (stdBasis second))
  simp only [stdBasis, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, basis]

end CKSIntrinsicVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def chartTransition (x z : M) : E → E := (extChartAt I x) ∘ (extChartAt I z).symm

def transitionDeriv (x z : M) (y : E) : E →L[ℝ] E :=
  (mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp (chartFrame z y)

lemma hasFDerivWithinAt_chartTransition (x z : M) {y : E}
    (hz : y ∈ (extChartAt I z).target)
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y) (range I) y := by
  have hxs : (extChartAt I z).symm y ∈ (chartAt H x).source := by simpa using hx
  exact ((mdifferentiableAt_extChartAt hxs).hasMFDerivAt.comp_hasMFDerivWithinAt y
    (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt).hasFDerivWithinAt

lemma chartFrame_comp_transitionDeriv (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    (chartFrame x (chartTransition x z y)).comp (transitionDeriv x z y) = chartFrame z y := by
  unfold transitionDeriv
  change (mfderivWithin 𝓘(ℝ,E) I (extChartAt I x).symm (range I)
    (extChartAt I x ((extChartAt I z).symm y))).comp
    ((mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp
    (chartFrame z y)) = chartFrame z y
  rw [← ContinuousLinearMap.comp_assoc,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx]
  rfl

lemma pullbackInner_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    pullbackInner g z y = (pullbackInner g x (chartTransition x z y)).comp
      (transitionDeriv x z y).toLinearMap (transitionDeriv x z y).toLinearMap := by
  ext v w
  change g.inner ((extChartAt I z).symm y) (chartFrame z y v) (chartFrame z y w) =
    g.inner ((extChartAt I x).symm (chartTransition x z y))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y v))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y w))
  have hv := congrArg (fun L : E →L[ℝ] E => L v) (chartFrame_comp_transitionDeriv x z hx)
  have hw := congrArg (fun L : E →L[ℝ] E => L w) (chartFrame_comp_transitionDeriv x z hx)
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y v) = _ at hv
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y w) = _ at hw
  rw [hv, hw]
  have heq : (extChartAt I x).symm (chartTransition x z y) = (extChartAt I z).symm y :=
    (extChartAt I x).left_inv hx
  rw [heq]
  rfl

lemma chartDensity_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    chartDensity g z y = |(transitionDeriv x z y).det| *
      chartDensity g x (chartTransition x z y) := by
  simp only [chartDensity, chartMatrix_eq_toMatrix]
  rw [pullbackInner_transition g x z hx, sqrt_gram_det_comp]

end CKSIntrinsicVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g K : InnerField I (M := M)} {x : M}

omit [IsManifold I ∞ M] in
lemma chart_exists_of_DECAt [IsManifold I ∞ M] (h : PhysicalDECAt I g K x) :
    ∃ c : ConstraintChart g K x, c.momentumNorm ≤ c.energy := by
  rcases h with ⟨V,f,A,B,hV,hx,hf,hfull,hs,hpos,hrep,hdec⟩
  exact ⟨⟨V,f,A,B,hV,hx,hf,hfull,hs,hpos,hrep⟩,hdec⟩

end CKSIntrinsicConstraints

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Manifold Bundle Function
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance cksLocalInst_4133 : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩

end CKSSchwarzschild

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

lemma chartTransition_image [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    chartTransition x z '' chartPreimage z (s ∩ (extChartAt I x).source) =
      chartPreimage x (s ∩ (extChartAt I z).source) := by
  ext y
  constructor
  · rintro ⟨u, ⟨⟨hs,hx⟩,hu⟩,rfl⟩
    have heq : (extChartAt I x).symm (chartTransition x z u) = (extChartAt I z).symm u :=
      (extChartAt I x).left_inv hx
    refine ⟨?_, (extChartAt I x).map_source hx⟩
    change (extChartAt I x).symm (chartTransition x z u) ∈ s ∩ (extChartAt I z).source
    rw [heq]
    exact ⟨hs, (extChartAt I z).map_target hu⟩
  · rintro ⟨⟨hs,hz⟩,hy⟩
    refine ⟨extChartAt I z ((extChartAt I x).symm y), ?_, ?_⟩
    · refine ⟨?_, (extChartAt I z).map_source hz⟩
      change (extChartAt I z).symm (extChartAt I z ((extChartAt I x).symm y)) ∈
        s ∩ (extChartAt I x).source
      rw [(extChartAt I z).left_inv hz]
      exact ⟨hs, (extChartAt I x).map_target hy⟩
    · change extChartAt I x ((extChartAt I z).symm
        (extChartAt I z ((extChartAt I x).symm y))) = y
      rw [(extChartAt I z).left_inv hz, (extChartAt I x).right_inv hy]

lemma chartTransition_injOn [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    InjOn (chartTransition x z) (chartPreimage z (s ∩ (extChartAt I x).source)) := by
  intro u hu v hv heq
  apply (extChartAt I z).symm.injOn hu.2 hv.2
  exact (extChartAt I x).injOn hu.1.2 hv.1.2 heq

variable [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]

lemma localVolume_compatible (g : Metric (M := M)) (x z : M) :
    (localVolume g x).restrict (extChartAt I z).source =
      (localVolume g z).restrict (extChartAt I x).source := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    localVolume_apply g x (hs.inter (isOpen_extChartAt_source z).measurableSet),
    localVolume_apply g z (hs.inter (isOpen_extChartAt_source x).measurableSet),
    ← chartTransition_image x z s]
  have hd : ∀ y ∈ chartPreimage z (s ∩ (extChartAt I x).source),
      HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y)
        (chartPreimage z (s ∩ (extChartAt I x).source)) y := by
    intro y hy
    exact (hasFDerivWithinAt_chartTransition x z hy.2 hy.1.2).mono
      (fun u hu => extChartAt_target_subset_range z hu.2)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
    hd (chartTransition_injOn x z s)]
  apply setLIntegral_congr_fun
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
  intro y hy
  dsimp only
  rw [chartDensity_transition g x z hy.1.2, ENNReal.ofReal_mul (abs_nonneg _)]

end CKSIntrinsicVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

theorem exists_volume [SecondCountableTopology M] (g : Metric (M := M)) :
    ∃ ν : Measure M, IsVolume g ν := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact ⟨0, fun x => isEmptyElim x⟩
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    exact exists_measure_of_compatible (fun x : M => (extChartAt I x).source)
      (fun x => (isOpen_extChartAt_source x).measurableSet) (localVolume g)
      (localVolume_compatible g) f (eq_univ_of_univ_subset hf)

lemma volume_on_subset [SecondCountableTopology M] (g : Metric (M := M))
    {ν : Measure M} (hν : IsVolume g ν)
    (x : M) {s : Set M} (hs : s ⊆ (extChartAt I x).source) :
    ν s = (localVolume g x) s := by
  rw [← hν x, Measure.restrict_apply' (isOpen_extChartAt_source x).measurableSet,
    inter_eq_left.mpr hs]

variable [SecondCountableTopology M]

lemma volume_locallyFinite (g : Metric (M := M)) {ν : Measure M} (hν : IsVolume g ν) :
    IsLocallyFiniteMeasure ν := by
  constructor
  intro x
  have hx : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  obtain ⟨δ,hδ,hbound⟩ := (Metric.continuousWithinAt_iff.mp
    (chartDensity_continuousOn g x _ hx)) 1 zero_lt_one
  let V := (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) δ
  have hVo : IsOpen V := (continuousOn_extChartAt x).isOpen_inter_preimage
    (isOpen_extChartAt_source x) Metric.isOpen_ball
  have hxV : x ∈ V := ⟨mem_extChartAt_source x, by simpa using hδ⟩
  refine ⟨V, hVo.mem_nhds hxV, ?_⟩
  rw [volume_on_subset g hν x (inter_subset_left), localVolume_apply g x hVo.measurableSet]
  let C := chartDensity g x (extChartAt I x x) + 1
  have hpre : chartPreimage x V ⊆ Metric.ball (extChartAt I x x) δ := by
    intro y hy
    have he : extChartAt I x ((extChartAt I x).symm y) = y := (extChartAt I x).right_inv hy.2
    simpa only [mem_preimage,he] using hy.1.2
  have hden : ∀ y ∈ chartPreimage x V, chartDensity g x y ≤ C := by
    intro y hy
    have hb := hbound hy.2 (hpre hy)
    rw [Real.dist_eq] at hb
    exact le_of_lt (by linarith [(abs_lt.mp hb).2])
  calc
    ∫⁻ y in chartPreimage x V, ENNReal.ofReal (chartDensity g x y) ≤
        ∫⁻ _y in chartPreimage x V, ENNReal.ofReal C :=
      setLIntegral_mono measurable_const (fun y hy => ENNReal.ofReal_le_ofReal (hden y hy))
    _ = ENNReal.ofReal C * volume (chartPreimage x V) := by simp
    _ ≤ ENNReal.ofReal C * volume (Metric.ball (extChartAt I x x) δ) :=
      mul_le_mul_right (measure_mono hpre) _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (Metric.isBounded_ball.measure_lt_top)

end CKSIntrinsicVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume

attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable [IsManifold I 1 M]

lemma riemannianVolume_isVolume (g : Metric (M := M)) : IsVolume g (riemannianVolume g) :=
  Classical.epsilon_spec (exists_volume g)
instance riemannianVolume_locallyFinite (g : Metric (M := M)) :
    IsLocallyFiniteMeasure (riemannianVolume g) := volume_locallyFinite g (riemannianVolume_isVolume g)

end CKSIntrinsicVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable [MeasurableSpace M] [BorelSpace M]

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma chartFrame_eq_symmL (x : M) {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    chartFrame x y = (trivializationAt E (TangentSpace I) x).symmL ℝ
      ((extChartAt I x).symm y) := by
  have hs : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hy
  rw [TangentBundle.symmL_trivializationAt hs, (extChartAt I x).right_inv hy]
  rfl

lemma chartFrame_continuousOn (x : M) (v : E) :
    ContinuousOn (fun y => (⟨(extChartAt I x).symm y, chartFrame x y v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target := by
  let e := trivializationAt E (TangentSpace I) x
  have h : ContinuousOn (fun y =>
      (⟨(extChartAt I x).symm y, e.symm ((extChartAt I x).symm y) v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target :=
    e.continuousOn_symm.comp
      ((continuousOn_extChartAt_symm x).prodMk continuousOn_const)
      (fun y hy => ⟨by simpa [e] using (extChartAt I x).map_target hy, mem_univ _⟩)
  apply h.congr
  intro y hy
  dsimp only
  congr 1
  rw [chartFrame_eq_symmL x hy, Trivialization.symmL_apply]
  simpa using (extChartAt I x).map_target hy

lemma chartMatrix_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartMatrix g x) (extChartAt I x).target := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  exact (chartFrame_continuousOn x (basis i)).inner_bundle
    (chartFrame_continuousOn x (basis j))

lemma chartDensity_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartDensity g x) (extChartAt I x).target := by
  exact ((continuous_id.matrix_det : Continuous (Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ)).comp_continuousOn (chartMatrix_continuousOn g x)).sqrt

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

abbrev stdBasis : Module.Basis (Fin 2) ℝ E := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

lemma sqrt_gram_det_comp (B : LinearMap.BilinForm ℝ E) (L : E →L[ℝ] E) :
    Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis
      (B.comp L.toLinearMap L.toLinearMap)).det =
      |L.det| * Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis B).det := by
  rw [LinearMap.BilinForm.toMatrix_comp stdBasis stdBasis,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix]
  change Real.sqrt (L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det) = _
  rw [show L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det =
    L.det ^ 2 * (LinearMap.BilinForm.toMatrix stdBasis B).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def pullbackInner (g : Metric (M := M)) (x : M) (y : E) : LinearMap.BilinForm ℝ E :=
  (g.inner ((extChartAt I x).symm y)).toBilinForm.comp
    (chartFrame x y).toLinearMap (chartFrame x y).toLinearMap

lemma chartMatrix_eq_toMatrix (g : Metric (M := M)) (x : M) (y : E) :
    chartMatrix g x y = LinearMap.BilinForm.toMatrix stdBasis (pullbackInner g x y) := by
  rfl

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem real_id_compTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance
attribute [local instance] real_id_compTriple

def chartTransition (x z : M) : E → E := (extChartAt I x) ∘ (extChartAt I z).symm

def transitionDeriv (x z : M) (y : E) : E →L[ℝ] E :=
  (mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp (chartFrame z y)

lemma hasFDerivWithinAt_chartTransition (x z : M) {y : E}
    (hz : y ∈ (extChartAt I z).target)
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y) (range I) y := by
  have hxs : (extChartAt I z).symm y ∈ (chartAt H x).source := by simpa using hx
  exact ((mdifferentiableAt_extChartAt hxs).hasMFDerivAt.comp_hasMFDerivWithinAt y
    (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt).hasFDerivWithinAt

lemma chartFrame_comp_transitionDeriv (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    (chartFrame x (chartTransition x z y)).comp (transitionDeriv x z y) = chartFrame z y := by
  unfold transitionDeriv
  change (mfderivWithin 𝓘(ℝ,E) I (extChartAt I x).symm (range I)
    (extChartAt I x ((extChartAt I z).symm y))).comp
    ((mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp
    (chartFrame z y)) = chartFrame z y
  rw [← ContinuousLinearMap.comp_assoc,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx]
  rfl

lemma pullbackInner_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    pullbackInner g z y = (pullbackInner g x (chartTransition x z y)).comp
      (transitionDeriv x z y).toLinearMap (transitionDeriv x z y).toLinearMap := by
  ext v w
  change g.inner ((extChartAt I z).symm y) (chartFrame z y v) (chartFrame z y w) =
    g.inner ((extChartAt I x).symm (chartTransition x z y))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y v))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y w))
  have hv := congrArg (fun L : E →L[ℝ] E => L v) (chartFrame_comp_transitionDeriv x z hx)
  have hw := congrArg (fun L : E →L[ℝ] E => L w) (chartFrame_comp_transitionDeriv x z hx)
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y v) = _ at hv
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y w) = _ at hw
  rw [hv, hw]
  have heq : (extChartAt I x).symm (chartTransition x z y) = (extChartAt I z).symm y :=
    (extChartAt I x).left_inv hx
  rw [heq]
  rfl

lemma chartDensity_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    chartDensity g z y = |(transitionDeriv x z y).det| *
      chartDensity g x (chartTransition x z y) := by
  simp only [chartDensity, chartMatrix_eq_toMatrix]
  rw [pullbackInner_transition g x z hx, sqrt_gram_det_comp]

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

omit [IsManifold I 1 M] in
lemma chart_target_measurable [IsManifold I 1 M] (x : M) :
    MeasurableSet (extChartAt I x).target := by
  rw [extChartAt_target]
  exact ((chartAt H x).open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

variable [MeasurableSpace M] [BorelSpace M]

def chartPreimage (x : M) (s : Set M) : Set E :=
  (extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target

lemma chartPreimage_measurable (x : M) {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet (chartPreimage x s) := by
  have h : Measurable ((extChartAt I x).target.domRestrict (extChartAt I x).symm) :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt_symm x)).measurable
  have hm := (chart_target_measurable x).subtype_image (hs.preimage h)
  convert hm using 1
  ext y
  simp [chartPreimage]

lemma localVolume_apply (g : Metric (M := M)) (x : M) {s : Set M} (hs : MeasurableSet s) :
    localVolume g x s = ∫⁻ y in chartPreimage x s, ENNReal.ofReal (chartDensity g x y) := by
  have hf := (continuousOn_extChartAt_symm x).aemeasurable
    (μ := (volume : Measure E)) (chart_target_measurable x)
  rw [localVolume, Measure.map_apply_of_aemeasurable
    (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hs, withDensity_apply']
  rw [← Measure.restrict_comm (chart_target_measurable x),
    Measure.restrict_restrict (chart_target_measurable x)]
  congr 1
  exact congrArg ((volume : Measure E).restrict) (inter_comm _ _)

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

omit [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M] in
lemma chartTransition_image [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    chartTransition x z '' chartPreimage z (s ∩ (extChartAt I x).source) =
      chartPreimage x (s ∩ (extChartAt I z).source) := by
  ext y
  constructor
  · rintro ⟨u, ⟨⟨hs,hx⟩,hu⟩,rfl⟩
    have heq : (extChartAt I x).symm (chartTransition x z u) = (extChartAt I z).symm u :=
      (extChartAt I x).left_inv hx
    refine ⟨?_, (extChartAt I x).map_source hx⟩
    change (extChartAt I x).symm (chartTransition x z u) ∈ s ∩ (extChartAt I z).source
    rw [heq]
    exact ⟨hs, (extChartAt I z).map_target hu⟩
  · rintro ⟨⟨hs,hz⟩,hy⟩
    refine ⟨extChartAt I z ((extChartAt I x).symm y), ?_, ?_⟩
    · refine ⟨?_, (extChartAt I z).map_source hz⟩
      change (extChartAt I z).symm (extChartAt I z ((extChartAt I x).symm y)) ∈
        s ∩ (extChartAt I x).source
      rw [(extChartAt I z).left_inv hz]
      exact ⟨hs, (extChartAt I x).map_target hy⟩
    · change extChartAt I x ((extChartAt I z).symm
        (extChartAt I z ((extChartAt I x).symm y))) = y
      rw [(extChartAt I z).left_inv hz, (extChartAt I x).right_inv hy]

omit [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M] in
lemma chartTransition_injOn [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    InjOn (chartTransition x z) (chartPreimage z (s ∩ (extChartAt I x).source)) := by
  intro u hu v hv heq
  apply (extChartAt I z).symm.injOn hu.2 hv.2
  exact (extChartAt I x).injOn hu.1.2 hv.1.2 heq

lemma localVolume_compatible (g : Metric (M := M)) (x z : M) :
    (localVolume g x).restrict (extChartAt I z).source =
      (localVolume g z).restrict (extChartAt I x).source := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    localVolume_apply g x (hs.inter (isOpen_extChartAt_source z).measurableSet),
    localVolume_apply g z (hs.inter (isOpen_extChartAt_source x).measurableSet),
    ← chartTransition_image x z s]
  have hd : ∀ y ∈ chartPreimage z (s ∩ (extChartAt I x).source),
      HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y)
        (chartPreimage z (s ∩ (extChartAt I x).source)) y := by
    intro y hy
    exact (hasFDerivWithinAt_chartTransition x z hy.2 hy.1.2).mono
      (fun u hu => extChartAt_target_subset_range z hu.2)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
    hd (chartTransition_injOn x z s)]
  apply setLIntegral_congr_fun
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
  intro y hy
  dsimp only
  rw [chartDensity_transition g x z hy.1.2, ENNReal.ofReal_mul (abs_nonneg _)]

end CKSSurfaceVolume

end

noncomputable section
open Set MeasureTheory
namespace CKSSurfaceVolume

lemma exists_measure_of_compatible {X ι : Type*} [MeasurableSpace X]
    (U : ι → Set X) (hU : ∀ i, MeasurableSet (U i)) (μ : ι → Measure X)
    (hc : ∀ i j, (μ i).restrict (U j) = (μ j).restrict (U i))
    (f : ℕ → ι) (hf : ⋃ n, U (f n) = univ) :
    ∃ ν : Measure X, ∀ i, ν.restrict (U i) = μ i := by
  let D := disjointed (U ∘ f)
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed (fun n => hU (f n))
  refine ⟨Measure.sum (fun n => (μ (f n)).restrict (D n)), fun i => ?_⟩
  rw [Measure.restrict_sum _ (hU i)]
  have heq : ∀ n, ((μ (f n)).restrict (D n)).restrict (U i) = (μ i).restrict (D n) := by
    intro n
    rw [Measure.restrict_comm (hU i), hc (f n) i]
    exact Measure.restrict_restrict_of_subset (disjointed_subset (U ∘ f) n)
  simp_rw [heq]
  rw [← Measure.restrict_iUnion (disjoint_disjointed (U ∘ f)) hD,
    show (⋃ n, D n) = univ from (iUnion_disjointed.trans hf), Measure.restrict_univ]

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem exists_volume (g : Metric (M := M)) : ∃ ν : Measure M, IsVolume g ν := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact ⟨0, fun x => isEmptyElim x⟩
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    exact exists_measure_of_compatible (fun x : M => (extChartAt I x).source)
      (fun x => (isOpen_extChartAt_source x).measurableSet) (localVolume g)
      (localVolume_compatible g) f (eq_univ_of_univ_subset hf)

omit [SecondCountableTopology M] in
lemma volume_on_subset [SecondCountableTopology M] (g : Metric (M := M))
    {ν : Measure M} (hν : IsVolume g ν)
    (x : M) {s : Set M} (hs : s ⊆ (extChartAt I x).source) :
    ν s = (localVolume g x) s := by
  rw [← hν x, Measure.restrict_apply' (isOpen_extChartAt_source x).measurableSet,
    inter_eq_left.mpr hs]

lemma volume_locallyFinite (g : Metric (M := M)) {ν : Measure M} (hν : IsVolume g ν) :
    IsLocallyFiniteMeasure ν := by
  constructor
  intro x
  have hx : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  obtain ⟨δ,hδ,hbound⟩ := (Metric.continuousWithinAt_iff.mp
    (chartDensity_continuousOn g x _ hx)) 1 zero_lt_one
  let V := (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) δ
  have hVo : IsOpen V := (continuousOn_extChartAt x).isOpen_inter_preimage
    (isOpen_extChartAt_source x) Metric.isOpen_ball
  have hxV : x ∈ V := ⟨mem_extChartAt_source x, by simpa using hδ⟩
  refine ⟨V, hVo.mem_nhds hxV, ?_⟩
  rw [volume_on_subset g hν x (inter_subset_left), localVolume_apply g x hVo.measurableSet]
  let C := chartDensity g x (extChartAt I x x) + 1
  have hpre : chartPreimage x V ⊆ Metric.ball (extChartAt I x x) δ := by
    intro y hy
    have he : extChartAt I x ((extChartAt I x).symm y) = y := (extChartAt I x).right_inv hy.2
    simpa only [mem_preimage,he] using hy.1.2
  have hden : ∀ y ∈ chartPreimage x V, chartDensity g x y ≤ C := by
    intro y hy
    have hb := hbound hy.2 (hpre hy)
    rw [Real.dist_eq] at hb
    exact le_of_lt (by linarith [(abs_lt.mp hb).2])
  calc
    ∫⁻ y in chartPreimage x V, ENNReal.ofReal (chartDensity g x y) ≤
        ∫⁻ _y in chartPreimage x V, ENNReal.ofReal C :=
      setLIntegral_mono measurable_const (fun y hy => ENNReal.ofReal_le_ofReal (hden y hy))
    _ = ENNReal.ofReal C * volume (chartPreimage x V) := by simp
    _ ≤ ENNReal.ofReal C * volume (Metric.ball (extChartAt I x x) δ) :=
      mul_le_mul_right (measure_mono hpre) _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (Metric.isBounded_ball.measure_lt_top)

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

lemma riemannianVolume_isVolume (g : Metric (M := M)) : IsVolume g (riemannianVolume g) :=
  Classical.epsilon_spec (exists_volume g)
instance riemannianVolume_locallyFinite (g : Metric (M := M)) :
    IsLocallyFiniteMeasure (riemannianVolume g) := volume_locallyFinite g (riemannianVolume_isVolume g)

end CKSSurfaceVolume

end

end OAI
end

section
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

end CKSInducedArea

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle Function
open scoped ContDiff Topology
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N]

lemma cutInclusion_embedding [IsManifold I3 ∞ N] (D : OuterDomain N) :
    Topology.IsEmbedding (cutInclusion D) :=
  D.embedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal

variable [@IsManifold ℝ _ E3 _ _ H3
  (@instTopologicalSpaceEuclideanHalfSpace 3 CKSBoundarySurface.halfSpaceDimension_neZero) I3 ∞ N _ _]

instance surfaceCompact (D : OuterDomain N) : CompactSpace (Surface D) := by
  apply isCompact_iff_compactSpace.mp
  exact D.embedding.isEmbedding.isCompact_iff.mpr D.compact_boundary

instance surfaceT2 [T2Space N] (D : OuterDomain N) : T2Space (Surface D) :=
  (cutInclusion_embedding D).t2Space

end CKSFullCutArea

end

end OAI
end


