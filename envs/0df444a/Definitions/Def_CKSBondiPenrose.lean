-- Prove2me | Definitions.Def_CKSBondiPenrose
-- name    : CKSBondiPenrose
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:03.212329+00:00
-- url     : https://prove2.me/theorems/5a1be532-c7aa-4491-8d78-f70649f4e5f3
-- statement:
--   The block develops geometric data for three-dimensional initial-value problems with boundary and a CKS asymptotic end. Formal metric and tensor jets determine Christoffel symbols, Ricci and scalar curvature, traces, norms, and the constraint quantities ρ=(R+(tr K)²−|K|²)/2 and J=div K−d(tr K); the dominant energy condition is √(g⁻¹(J,J))≤ρ. Actual coordinate derivatives supply these jets, while the manifold version requires local smooth coordinates with bijective derivatives and smooth, symmetric coefficient tensors, with the metric positive definite. Cartesian symbol decay means smoothness sufficiently far out and O(r⁻ᵈ⁻ᵏ) bounds for every derivative of order k; ADM energy and momentum are the coordinate sphere flux integrals with factors r²/(16π) and r²/(8π). For CKS data, g and K are pullbacks of b+A and b+B, respectively, where bₓ(v,w)=⟨v,w⟩−⟨x,v⟩⟨x,w⟩/(1+|x|²). In angular patches, A has radial component mᵣ/r⁵+O(r⁻⁶), mixed components O(r⁻³), and angular components m_g/r+O(r⁻²), with bounds through three derivatives; B has radial component O(r⁻⁵), mixed components O(r⁻³), and angular components m_K/r+O(r⁻²), through two derivatives. These remainder bounds use compositions of r∂ᵣ and angular derivatives and require the corresponding differentiability. The smooth leading coefficients determine the mass aspect M=tr_σ(m_g+2m_K)+2mᵣ, where σ is the round angular metric, and the Bondi charge is (16π)⁻¹∫M(n)(1,n)dω, with ω the sphere measure obtained from Euclidean volume. A coordinate end is a smooth diffeomorphism onto the exterior of a positive-radius ball, with closed outer tails and compact inner complements; CKSData assumes such an end, smooth perturbations, and realizing angular patches covering every sphere direction and representing one smooth global mass aspect. Orientability means tangent orientations are locally constant in bundle coordinates, and completeness refers to the extended distance induced by a continuous Riemannian metric. An outer domain is a smoothly embedded three-manifold with closed, connected image containing the complement of some compact set, carrying its interior into the ambient interior and having compact boundary image. Boundary charts construct smooth surfaces, and pullback along a smooth immersion constructs their induced Riemannian metrics. Volume measures are selected by classical choice using the chart density √det(g); cut area is the induced boundary measure of the whole surface. Minimum enclosing area is defined both as an extended nonnegative infimum and, separately, as the real infimum of individual converted cut areas, where infinite area converts to zero. Integrable constraints require continuous integrable functions μ,j with 0≤j≤μ and, in every representing constraint chart, 8πμ=ρ and 8πj=|J|. For real m, the connected Schwarzschild exterior is [0,∞)×S² with radius r=2m+t. With v(r)=−1+(r+1)s(r−2m−1), where s is the smooth transition function, and L²=1−2m/r+v², the Cartesian metric and second tensor have polar expressions g=L⁻²dr²+r²σ and K=v′L⁻²dr²+vrσ, with r=|x|; their pullbacks by the position map give fields on the exterior. The advanced spacetime metric is −(1−2m/r)du²+2du dr+r²σ; the graph has u(r)=∫₂ₘʳ[L(L−v)]⁻¹ds and prescribed normal ((L−v)⁻¹,v∂ᵣ). HorizonRegularGraph is a proposition assuming ambient smoothness and nondegeneracy away from r=0, graph smoothness and its specified derivative for r>m, global graph injectivity, u(2m)=0 and prescribed slope 1/2 at r=2m, and, for r≥2m, the stated induced metric and second form together with a unit timelike orthogonal normal having positive time component. Covariant-derivative pairings, Christoffel pairings, and Gram–Schmidt tangent-frame formulas support these constructions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CKSBondiPenrose.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CKSBondiPenrose.lean; bytes 16..176105
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

/-! Area-controlled end replacement and Schwarzschild equality examples. -/

namespace OAI.CKSADM
end OAI.CKSADM
namespace OAI.CKSAngularGeometry
end OAI.CKSAngularGeometry
namespace OAI.CKSAngularSlice
end OAI.CKSAngularSlice
namespace OAI.CKSBoundarySurface
end OAI.CKSBoundarySurface
namespace OAI.CKSCalculus
end OAI.CKSCalculus
namespace OAI.CKSCartesianOuter
end OAI.CKSCartesianOuter
namespace OAI.CKSEmbeddingDerivative
end OAI.CKSEmbeddingDerivative
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
namespace OAI.CKSIntrinsicVolume
end OAI.CKSIntrinsicVolume
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
namespace OAI.CKSRound.MetricJet
end OAI.CKSRound.MetricJet
namespace OAI.CKSSchwarzschild
end OAI.CKSSchwarzschild
namespace OAI.CKSSourceExterior
end OAI.CKSSourceExterior
namespace OAI.CKSSpatialManifold
end OAI.CKSSpatialManifold
namespace OAI.CKSSphericalHarmonics
end OAI.CKSSphericalHarmonics
namespace OAI.CKSSurfaceVolume
end OAI.CKSSurfaceVolume
noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSpatialManifold


local instance real_id_isometric : RingHomIsometric (RingHom.id ℝ) := inferInstance

end OAI.CKSSpatialManifold
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMetricGluing
open Bundle Manifold Set Bornology
open scoped Bundle Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local instance real_continuousAdd : ContinuousAdd ℝ := inferInstance

local instance real_continuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance

local instance real_smulCommClass :
    @SMulCommClass ℝ ℝ ℝ Algebra.toSMul
      (@instSMulOfMul ℝ (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ (@CommSemiring.toSemiring ℝ Real.instCommSemiring)))) :=
  inferInstance

end OAI.CKSMetricGluing
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMetricGluing
open Bundle Manifold Set Bornology
open scoped Bundle Manifold ContDiff
variable {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_2} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_3} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] real_continuousAdd


abbrev InnerField :=
  letI := OAI.CKSMetricGluing.real_smulCommClass
  letI := OAI.CKSMetricGluing.real_continuousConstSMul
  ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

abbrev SmoothMetric := ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x)

def innerSection (q : OAI.CKSMetricGluing.InnerField I (M := M)) :
    M → TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  fun x => ⟨x,q x⟩

end OAI.CKSMetricGluing
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSAngularGeometry
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev I := Fin 2

end OAI.CKSAngularGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSCalculus
open Filter Set
open scoped Topology ContDiff
variable {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]

def D (e : E) (f : E → ℝ) (x : E) : ℝ := fderiv ℝ f x e

end OAI.CKSCalculus
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSRound


abbrev Idx := Fin 3

abbrev Mat := Matrix OAI.CKSRound.Idx OAI.CKSRound.Idx ℝ

structure MetricJet where
  inv : OAI.CKSRound.Mat
  d : OAI.CKSRound.Idx → OAI.CKSRound.Mat
  dd : OAI.CKSRound.Idx → OAI.CKSRound.Idx → OAI.CKSRound.Mat

end OAI.CKSRound
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSRound.MetricJet


def gamma (j : OAI.CKSRound.MetricJet) (a i k : OAI.CKSRound.Idx) : ℝ :=
  (∑ l, j.inv a l * (j.d i k l + j.d k i l - j.d l i k)) / 2

def dInv (j : OAI.CKSRound.MetricJet) (s a b : OAI.CKSRound.Idx) : ℝ :=
  - ∑ i, ∑ k, j.inv a i * j.d s i k * j.inv k b

def dGamma (j : OAI.CKSRound.MetricJet) (s a i k : OAI.CKSRound.Idx) : ℝ :=
  (∑ l, (j.dInv s a l * (j.d i k l + j.d k i l - j.d l i k) +
    j.inv a l * (j.dd s i k l + j.dd s k i l - j.dd s l i k))) / 2

def ricci (j : OAI.CKSRound.MetricJet) (i k : OAI.CKSRound.Idx) : ℝ :=
  (∑ a, (j.dGamma a a i k - j.dGamma k a i a)) +
  ∑ a, ∑ b, (j.gamma a a b * j.gamma b i k - j.gamma a k b * j.gamma b i a)

def scalar (j : OAI.CKSRound.MetricJet) : ℝ := ∑ i, ∑ k, j.inv i k * j.ricci i k

end OAI.CKSRound.MetricJet
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSRound


structure TensorJet where
  val : OAI.CKSRound.Mat
  d : OAI.CKSRound.Idx → OAI.CKSRound.Mat

end OAI.CKSRound
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSRound.MetricJet


def trace (g : OAI.CKSRound.MetricJet) (k : OAI.CKSRound.TensorJet) : ℝ :=
  ∑ a, ∑ b, g.inv a b * k.val a b

def normSq (g : OAI.CKSRound.MetricJet) (k : OAI.CKSRound.TensorJet) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, g.inv a c * g.inv b d * k.val a b * k.val c d

def dTrace (g : OAI.CKSRound.MetricJet) (k : OAI.CKSRound.TensorJet) (i : OAI.CKSRound.Idx) : ℝ :=
  ∑ a, ∑ b, (g.dInv i a b * k.val a b + g.inv a b * k.d i a b)

def tensorDivergence (g : OAI.CKSRound.MetricJet) (k : OAI.CKSRound.TensorJet) (i : OAI.CKSRound.Idx) : ℝ :=
  ∑ a, ∑ b, g.inv a b * (k.d a b i -
    (∑ c, g.gamma c a b * k.val c i) - (∑ c, g.gamma c a i * k.val b c))

def energy (g : OAI.CKSRound.MetricJet) (k : OAI.CKSRound.TensorJet) : ℝ :=
  (g.scalar + g.trace k ^ 2 - g.normSq k) / 2

def momentum (g : OAI.CKSRound.MetricJet) (k : OAI.CKSRound.TensorJet) (i : OAI.CKSRound.Idx) : ℝ :=
  g.tensorDivergence k i - g.dTrace k i

end OAI.CKSRound.MetricJet
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSRealizedRound
open CKSCalculus CKSRound
open scoped Topology ContDiff

abbrev Point := Fin 3 → ℝ

def basis (a : OAI.CKSRound.Idx) : OAI.CKSRealizedRound.Point := Pi.single a 1

end OAI.CKSRealizedRound
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLocalBending
open CKSRound

def momentumSq (j : OAI.CKSRound.MetricJet) (k : OAI.CKSRound.TensorJet) : ℝ :=
  ∑ i, ∑ l, j.inv i l * j.momentum k i * j.momentum k l

def DEC (j : OAI.CKSRound.MetricJet) (k : OAI.CKSRound.TensorJet) : Prop :=
  Real.sqrt (OAI.CKSLocalBending.momentumSq j k) ≤ j.energy k

end OAI.CKSLocalBending
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSAngularGeometry
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev Point := OAI.CKSAngularGeometry.I → ℝ

def basis (a : OAI.CKSAngularGeometry.I) : OAI.CKSAngularGeometry.Point := Pi.single a 1

end OAI.CKSAngularGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSAngularGeometry
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev AmbientMat := Matrix (Fin 3) (Fin 3) ℝ

end OAI.CKSAngularGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSAngularGeometry
open Matrix CKSCalculus
open scoped BigOperators

abbrev PhysicalPoint := Fin 3 → ℝ

end OAI.CKSAngularGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMixedGeometry
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev I := Fin 3

abbrev A := Fin 2

abbrev Point := OAI.CKSMixedGeometry.I → ℝ

def basis (a : OAI.CKSMixedGeometry.I) : OAI.CKSMixedGeometry.Point := Pi.single a 1

end OAI.CKSMixedGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMixedGeometry
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal

local instance pointDimension_neZero : NeZero (3 : ℕ) := inferInstance

def radialFactor (a : OAI.CKSMixedGeometry.I) (y : OAI.CKSMixedGeometry.Point) : ℝ :=
  letI := OAI.CKSMixedGeometry.pointDimension_neZero
  if a = 0 then y 0 else 1

def scaledD (a : OAI.CKSMixedGeometry.I) (f : OAI.CKSMixedGeometry.Point → ℝ) : OAI.CKSMixedGeometry.Point → ℝ :=
  fun y => OAI.CKSMixedGeometry.radialFactor a y * OAI.CKSCalculus.D (OAI.CKSMixedGeometry.basis a) f y

def scaledIter : List OAI.CKSMixedGeometry.I → (OAI.CKSMixedGeometry.Point → ℝ) → OAI.CKSMixedGeometry.Point → ℝ
  | [], f => f
  | a::l,f => OAI.CKSMixedGeometry.scaledD a (scaledIter l f)

end OAI.CKSMixedGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMixedGeometry
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev Angle := OAI.CKSMixedGeometry.A → ℝ

def angularProjection : OAI.CKSMixedGeometry.Point →L[ℝ] OAI.CKSMixedGeometry.Angle :=
  ContinuousLinearMap.pi (fun a => ContinuousLinearMap.proj a.succ)

def ScaledComponentBound (f : OAI.CKSMixedGeometry.Point → ℝ) (j q : ℕ) (B : ℝ) (y : OAI.CKSMixedGeometry.Point) : Prop :=
  letI := OAI.CKSMixedGeometry.pointDimension_neZero
  ∀ l : List OAI.CKSMixedGeometry.I, l.length ≤ j → |scaledIter l f y| ≤ B/(y 0)^q

end OAI.CKSMixedGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedSphere
open Finset

abbrev Ix := Fin 3

end OAI.CKSInducedSphere
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSphericalHarmonics
open MvPolynomial

abbrev Ambient := EuclideanSpace ℝ (Fin 3)

abbrev Sphere := ↥(Metric.sphere (0 : OAI.CKSSphericalHarmonics.Ambient) 1)

end OAI.CKSSphericalHarmonics
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSphericalHarmonics
open MvPolynomial
open MeasureTheory

abbrev surfaceMeasure : Measure OAI.CKSSphericalHarmonics.Sphere := (volume : Measure OAI.CKSSphericalHarmonics.Ambient).toSphere

end OAI.CKSSphericalHarmonics
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSphericalHarmonics
open MvPolynomial
open MeasureTheory
open scoped Pointwise
open scoped Manifold ContDiff Topology
open Set

def SmoothSphere (f : OAI.CKSSphericalHarmonics.Sphere → ℝ) : Prop := ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f

end OAI.CKSSphericalHarmonics
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz


local instance two_atLeastTwo : Nat.AtLeastTwo 2 := inferInstance

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedSphere
open Set Filter Finset
open scoped Topology ContDiff

abbrev E := EuclideanSpace ℝ OAI.CKSInducedSphere.Ix

end OAI.CKSInducedSphere
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedSphere
open Set Filter Finset
open scoped Topology ContDiff
attribute [local instance] CKSLorentz.two_atLeastTwo


def e (i : OAI.CKSInducedSphere.Ix) : OAI.CKSInducedSphere.E := WithLp.toLp 2 (Pi.single i 1)

def pd (i : OAI.CKSInducedSphere.Ix) (F : OAI.CKSInducedSphere.E → ℝ) (x : OAI.CKSInducedSphere.E) : ℝ := fderiv ℝ F x (OAI.CKSInducedSphere.e i)

end OAI.CKSInducedSphere
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

abbrev E := EuclideanSpace ℝ (Fin 3)

abbrev V := ℝ × OAI.CKSLorentz.E

abbrev Sphere := ↥(Metric.sphere (0 : OAI.CKSLorentz.E) 1)

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

local instance pointDimension_neZero : NeZero (3 : ℕ) := inferInstance

def ordinaryLeadingComponent (q : ℕ) (M : OAI.CKSMixedGeometry.Angle → ℝ) (y : OAI.CKSMixedGeometry.Point) : ℝ :=
  letI := OAI.CKSLorentz.pointDimension_neZero
  1/(y 0)^q * M (OAI.CKSMixedGeometry.angularProjection y)

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMixedGeometry
open Set
open scoped ContDiff

structure SourceRemainderOn (j q : ℕ) (V : Set OAI.CKSMixedGeometry.Point) (f : OAI.CKSMixedGeometry.Point → ℝ) : Prop where
  regular : ∀ y ∈ V, ContDiffAt ℝ j f y
  bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ V, OAI.CKSMixedGeometry.ScaledComponentBound f j q B y

end OAI.CKSMixedGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

structure SourceCKSComponents (j qrad : ℕ) (V : Set OAI.CKSMixedGeometry.Point)
    (A : OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.Point → ℝ) (mr : OAI.CKSMixedGeometry.Angle → ℝ) (mg : OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.Angle → ℝ) : Prop where
  radial : OAI.CKSMixedGeometry.SourceRemainderOn j qrad V (fun y => A 0 0 y-OAI.CKSLorentz.ordinaryLeadingComponent 5 mr y)
  mixed : ∀ i k, (i=0 ∧ k≠0) ∨ (i≠0 ∧ k=0) → OAI.CKSMixedGeometry.SourceRemainderOn j 3 V (A i k)
  angular : ∀ i k, i≠0 → k≠0 → OAI.CKSMixedGeometry.SourceRemainderOn j 2 V
    (fun y => A i k y-OAI.CKSLorentz.ordinaryLeadingComponent 1 (mg i k) y)

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice Set

def angularRadialTail (R : ℝ) (W : Set OAI.CKSMixedGeometry.Angle) : Set OAI.CKSMixedGeometry.Point :=
  letI := OAI.CKSLorentz.pointDimension_neZero
  {y | R < y 0 ∧ OAI.CKSMixedGeometry.angularProjection y ∈ W}

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

structure SmoothAngularPatch where
  chart : OpenPartialHomeomorph OAI.CKSLorentz.Sphere OAI.CKSMixedGeometry.Angle
  param_smooth : ContDiffOn ℝ ∞ (fun θ => (chart.symm θ : OAI.CKSLorentz.E)) chart.target
  extension : OAI.CKSLorentz.E → OAI.CKSMixedGeometry.Angle
  domain : Set OAI.CKSLorentz.E
  isOpen_domain : IsOpen domain
  extension_smooth : ContDiffOn ℝ ∞ extension domain
  source_domain : ∀ n ∈ chart.source, (n:OAI.CKSLorentz.E) ∈ domain
  extension_eq : ∀ n ∈ chart.source, extension n = chart n

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz.SmoothAngularPatch
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

def param (P : OAI.CKSLorentz.SmoothAngularPatch) (θ : OAI.CKSMixedGeometry.Angle) : OAI.CKSLorentz.E := P.chart.symm θ

def sphereRegion (P : OAI.CKSLorentz.SmoothAngularPatch) (W : Set OAI.CKSMixedGeometry.Angle) : Set OAI.CKSLorentz.Sphere :=
  P.chart.source ∩ P.chart ⁻¹' W

end OAI.CKSLorentz.SmoothAngularPatch
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

structure CKSTensorPatch where
  patch : OAI.CKSLorentz.SmoothAngularPatch
  region : Set OAI.CKSMixedGeometry.Angle
  open_region : IsOpen region
  region_target : region ⊆ patch.chart.target
  radius : ℝ
  metric : OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.Point → ℝ
  second : OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.Point → ℝ
  mr : OAI.CKSMixedGeometry.Angle → ℝ
  mg : OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.Angle → ℝ
  mK : OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.Angle → ℝ
  mr_smooth : ContDiffOn ℝ ∞ mr region
  mg_smooth : ∀ i k, i≠0 → k≠0 → ContDiffOn ℝ ∞ (mg i k) region
  mK_smooth : ∀ i k, i≠0 → k≠0 → ContDiffOn ℝ ∞ (mK i k) region
  metric_CKS : OAI.CKSLorentz.SourceCKSComponents 3 6 (OAI.CKSLorentz.angularRadialTail radius region) metric mr mg
  second_CKS : OAI.CKSLorentz.SourceCKSComponents 2 5 (OAI.CKSLorentz.angularRadialTail radius region) second (fun _ => 0) mK

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice

local instance real_continuousAdd : ContinuousAdd ℝ := inferInstance

local instance real_continuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance

local instance real_smulCommClass :
    @SMulCommClass ℝ ℝ ℝ Algebra.toSMul
      (@instSMulOfMul ℝ (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ (@CommSemiring.toSemiring ℝ Real.instCommSemiring)))) :=
  inferInstance

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice
attribute [local instance] real_continuousAdd


abbrev SpatialBilinear :=
  letI := OAI.CKSLorentz.real_smulCommClass
  letI := OAI.CKSLorentz.real_continuousConstSMul
  OAI.CKSLorentz.E →L[ℝ] OAI.CKSLorentz.E →L[ℝ] ℝ

abbrev SpatialTensor := OAI.CKSLorentz.E → OAI.CKSLorentz.SpatialBilinear

local instance three_neZero : NeZero 3 := inferInstance

def polarParam (P : OAI.CKSLorentz.SmoothAngularPatch) (y : OAI.CKSMixedGeometry.Point) : OAI.CKSLorentz.E :=
  letI := OAI.CKSLorentz.three_neZero
  y 0 • P.param (OAI.CKSMixedGeometry.angularProjection y)

def polarTensorComponents (P : OAI.CKSLorentz.SmoothAngularPatch) (A : OAI.CKSLorentz.SpatialTensor)
    (i k : OAI.CKSMixedGeometry.I) (y : OAI.CKSMixedGeometry.Point) : ℝ :=
  A (OAI.CKSLorentz.polarParam P y) (fderiv ℝ (OAI.CKSLorentz.polarParam P) y (OAI.CKSMixedGeometry.basis i))
    (fderiv ℝ (OAI.CKSLorentz.polarParam P) y (OAI.CKSMixedGeometry.basis k))

def CKSTensorPatch.Realizes (Q : OAI.CKSLorentz.CKSTensorPatch) (A B : OAI.CKSLorentz.SpatialTensor) : Prop :=
  ∀ y ∈ OAI.CKSLorentz.angularRadialTail Q.radius Q.region, ∀ i k,
    Q.metric i k y = OAI.CKSLorentz.polarTensorComponents Q.patch A i k y ∧
    Q.second i k y = OAI.CKSLorentz.polarTensorComponents Q.patch B i k y

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice CKSCalculus

abbrev AngularMatrix := Matrix (Fin 2) (Fin 2) ℝ

def angularMetricTrace (σ A : OAI.CKSLorentz.AngularMatrix) : ℝ := (σ⁻¹ * A).trace

def angularRoundMetric (φ : OAI.CKSMixedGeometry.Angle → OAI.CKSLorentz.E) (θ : OAI.CKSMixedGeometry.Angle) : OAI.CKSLorentz.AngularMatrix :=
  letI := OAI.CKSLorentz.two_atLeastTwo
  letI : Inner ℝ OAI.CKSLorentz.E :=
    @InnerProductSpace.toInner ℝ OAI.CKSLorentz.E _
      (PiLp.seminormedAddCommGroup 2 (fun _ : Fin 3 => ℝ))
      (PiLp.innerProductSpace (fun _ : Fin 3 => ℝ))
  fun a b => inner ℝ (fderiv ℝ φ θ (OAI.CKSAngularGeometry.basis a))
    (fderiv ℝ φ θ (OAI.CKSAngularGeometry.basis b))

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open scoped RealInnerProductSpace ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure)

def nullDirection (n : OAI.CKSLorentz.Sphere) : OAI.CKSLorentz.V := (1,(n:OAI.CKSLorentz.E))

def rawCharge (M : OAI.CKSLorentz.Sphere → ℝ) : OAI.CKSLorentz.V := ∫ n : OAI.CKSLorentz.Sphere, M n • OAI.CKSLorentz.nullDirection n ∂OAI.CKSSphericalHarmonics.surfaceMeasure

def bondiCharge (M : OAI.CKSLorentz.Sphere → ℝ) : OAI.CKSLorentz.V := (16*Real.pi)⁻¹ • OAI.CKSLorentz.rawCharge M

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry

local instance real_isTopologicalAddGroup : IsTopologicalAddGroup ℝ := inferInstance

local instance spatialDual_isTopologicalAddGroup : IsTopologicalAddGroup (OAI.CKSLorentz.E →L[ℝ] ℝ) :=
  inferInstance

local instance spatialDual_smulCommClass :
    letI := OAI.CKSLorentz.real_smulCommClass
    SMulCommClass ℝ ℝ (OAI.CKSLorentz.E →L[ℝ] ℝ) :=
  inferInstance

local instance spatialDual_continuousConstSMul : ContinuousConstSMul ℝ (OAI.CKSLorentz.E →L[ℝ] ℝ) :=
  inferInstance

local instance spatialDual_isScalarTower : IsScalarTower ℝ ℝ (OAI.CKSLorentz.E →L[ℝ] ℝ) := inferInstance

local instance spatialDual_continuousSMul : ContinuousSMul ℝ (OAI.CKSLorentz.E →L[ℝ] ℝ) := inferInstance

def hyperbolicField (x : OAI.CKSLorentz.E) : OAI.CKSLorentz.SpatialBilinear :=
  letI := OAI.CKSLorentz.real_continuousAdd
  letI := OAI.CKSLorentz.real_continuousConstSMul
  letI := OAI.CKSLorentz.real_smulCommClass
  letI := OAI.CKSLorentz.real_isTopologicalAddGroup
  letI := OAI.CKSLorentz.spatialDual_isTopologicalAddGroup
  letI := OAI.CKSLorentz.spatialDual_smulCommClass
  letI := OAI.CKSLorentz.spatialDual_continuousConstSMul
  letI := OAI.CKSLorentz.spatialDual_isScalarTower
  letI := OAI.CKSLorentz.spatialDual_continuousSMul
  let f : OAI.CKSLorentz.SpatialBilinear := innerSL ℝ
  f - (1/(1+‖x‖^2)) • (f x).smulRight (f x)

def sourceSpatial (A : OAI.CKSLorentz.SpatialTensor) : OAI.CKSLorentz.SpatialTensor := fun x => OAI.CKSLorentz.hyperbolicField x + A x

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open scoped ContDiff
attribute [local instance] CKSSpatialManifold.real_id_isometric real_smulCommClass spatialDual_smulCommClass


local instance hsgNorm : NormedAddCommGroup OAI.CKSLorentz.SpatialBilinear :=
  let dualSpace : NormedSpace ℝ (OAI.CKSLorentz.E →L[ℝ] ℝ) :=
    @ContinuousLinearMap.toNormedSpace ℝ ℝ OAI.CKSLorentz.E ℝ _ _ _ _ _ _ (RingHom.id ℝ)
      OAI.CKSSpatialManifold.real_id_isometric ℝ _ _ OAI.CKSLorentz.real_smulCommClass
  @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ OAI.CKSLorentz.E (OAI.CKSLorentz.E →L[ℝ] ℝ)
    _ _ _ _ _ dualSpace (RingHom.id ℝ) OAI.CKSSpatialManifold.real_id_isometric

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open scoped ContDiff
attribute [local instance] CKSSpatialManifold.real_id_isometric real_smulCommClass spatialDual_smulCommClass
attribute [local instance] OAI.CKSLorentz.hsgNorm


local instance hsgSpace : NormedSpace ℝ OAI.CKSLorentz.SpatialBilinear :=
  let dualSpace : NormedSpace ℝ (OAI.CKSLorentz.E →L[ℝ] ℝ) :=
    @ContinuousLinearMap.toNormedSpace ℝ ℝ OAI.CKSLorentz.E ℝ _ _ _ _ _ _ (RingHom.id ℝ)
      OAI.CKSSpatialManifold.real_id_isometric ℝ _ _ OAI.CKSLorentz.real_smulCommClass
  @ContinuousLinearMap.toNormedSpace ℝ ℝ OAI.CKSLorentz.E (OAI.CKSLorentz.E →L[ℝ] ℝ)
    _ _ _ _ _ dualSpace (RingHom.id ℝ) OAI.CKSSpatialManifold.real_id_isometric
    ℝ _ dualSpace OAI.CKSLorentz.spatialDual_smulCommClass

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSADM
open Finset CKSInducedSphere
open scoped RealInnerProductSpace ContDiff

def normal (x : OAI.CKSInducedSphere.E) (i : OAI.CKSInducedSphere.Ix) : ℝ := x i / ‖x‖

end OAI.CKSADM
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSADM
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere
open scoped Topology ContDiff

def spatialInfinity : Filter OAI.CKSInducedSphere.E := Filter.comap (fun x : OAI.CKSInducedSphere.E => ‖x‖) atTop

def TailRegular (F : OAI.CKSInducedSphere.E → ℝ) : Prop :=
  ∀ᶠ x in OAI.CKSADM.spatialInfinity, ContDiffAt ℝ ∞ F x

def Decay (d : ℝ) (F : OAI.CKSInducedSphere.E → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in OAI.CKSADM.spatialInfinity, |F x| ≤ C*‖x‖^(-d)

def SymbolN : ℕ → ℝ → (OAI.CKSInducedSphere.E → ℝ) → Prop
  | 0, d, F => OAI.CKSADM.Decay d F
  | n+1, d, F => OAI.CKSADM.Decay d F ∧ ∀ j : OAI.CKSInducedSphere.Ix, SymbolN n (d+1) (OAI.CKSInducedSphere.pd j F)

def Symbol (d : ℝ) (F : OAI.CKSInducedSphere.E → ℝ) : Prop :=
  OAI.CKSADM.TailRegular F ∧ ∀ n : ℕ, OAI.CKSADM.SymbolN n d F

end OAI.CKSADM
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSAngularGeometry
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalMetricJet (G : OAI.CKSAngularGeometry.PhysicalPoint → OAI.CKSAngularGeometry.AmbientMat) (x : OAI.CKSAngularGeometry.PhysicalPoint) : OAI.CKSRound.MetricJet where
  inv := (G x)⁻¹
  d := fun a i j => OAI.CKSCalculus.D (OAI.CKSRealizedRound.basis a) (fun y => G y i j) x
  dd := fun a b i j => OAI.CKSCalculus.D (OAI.CKSRealizedRound.basis a) (OAI.CKSCalculus.D (OAI.CKSRealizedRound.basis b) (fun y => G y i j)) x

def physicalTensorJet (K : OAI.CKSAngularGeometry.PhysicalPoint → OAI.CKSAngularGeometry.AmbientMat) (x : OAI.CKSAngularGeometry.PhysicalPoint) : OAI.CKSRound.TensorJet where
  val := K x
  d := fun a i j => OAI.CKSCalculus.D (OAI.CKSRealizedRound.basis a) (fun y => K y i j) x

end OAI.CKSAngularGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSCartesianOuter
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics
open CKSAngularGeometry (PhysicalPoint)
open scoped Topology ContDiff Matrix.Norms.Elementwise

abbrev toPoint : OAI.CKSInducedSphere.E ≃L[ℝ] OAI.CKSAngularGeometry.PhysicalPoint := EuclideanSpace.equiv (Fin 3) ℝ

end OAI.CKSCartesianOuter
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice CKSCalculus

def cksChartMassAspect (φ : OAI.CKSMixedGeometry.Angle → OAI.CKSLorentz.E) (mr : OAI.CKSMixedGeometry.Angle → ℝ)
    (mg mK : OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.I → OAI.CKSMixedGeometry.Angle → ℝ) (θ : OAI.CKSMixedGeometry.Angle) : ℝ :=
  letI := OAI.CKSLorentz.two_atLeastTwo
  OAI.CKSLorentz.angularMetricTrace (OAI.CKSLorentz.angularRoundMetric φ θ)
    (fun a b => mg a.succ b.succ θ + 2*mK a.succ b.succ θ) + 2*mr θ

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularGeometry

def spatialCoefficients (A : OAI.CKSLorentz.SpatialTensor) (y : OAI.CKSAngularGeometry.PhysicalPoint) : OAI.CKSAngularGeometry.AmbientMat :=
  fun i j => A (OAI.CKSCartesianOuter.toPoint.symm y)
    (OAI.CKSCartesianOuter.toPoint.symm (OAI.CKSMixedGeometry.basis i))
    (OAI.CKSCartesianOuter.toPoint.symm (OAI.CKSMixedGeometry.basis j))

def spatialDEC (A B : OAI.CKSLorentz.SpatialTensor) (x : OAI.CKSLorentz.E) : Prop :=
  OAI.CKSLocalBending.DEC (OAI.CKSAngularGeometry.physicalMetricJet (OAI.CKSLorentz.spatialCoefficients A) (OAI.CKSCartesianOuter.toPoint x))
    (OAI.CKSAngularGeometry.physicalTensorJet (OAI.CKSLorentz.spatialCoefficients B) (OAI.CKSCartesianOuter.toPoint x))

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularSlice Set

def CKSTensorPatch.RepresentsMassAspect (Q : OAI.CKSLorentz.CKSTensorPatch) (M : OAI.CKSLorentz.Sphere → ℝ) : Prop :=
  ∀ n ∈ Q.patch.sphereRegion Q.region,
    OAI.CKSLorentz.cksChartMassAspect Q.patch.param Q.mr Q.mg Q.mK (Q.patch.chart n) = M n

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics MeasureTheory

def spatialCartesian (A : OAI.CKSLorentz.SpatialTensor) (x : OAI.CKSLorentz.E) : OAI.CKSAngularGeometry.AmbientMat :=
  OAI.CKSLorentz.spatialCoefficients A (OAI.CKSCartesianOuter.toPoint x)

local instance sixteen_atLeastTwo : Nat.AtLeastTwo 16 := inferInstance

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics MeasureTheory
attribute [local instance] sixteen_atLeastTwo


def spatialADMEnergy (A : OAI.CKSLorentz.SpatialTensor) (r : ℝ) : ℝ :=
  r^2/(16*Real.pi) * ∫ n : OAI.CKSLorentz.Sphere,
    ∑ i : Fin 3, (∑ j : Fin 3,
      (OAI.CKSInducedSphere.pd j (fun y => OAI.CKSLorentz.spatialCartesian A y i j) (r • (n:OAI.CKSLorentz.E)) -
       OAI.CKSInducedSphere.pd i (fun y => OAI.CKSLorentz.spatialCartesian A y j j) (r • (n:OAI.CKSLorentz.E)))) *
      OAI.CKSADM.normal (r • (n:OAI.CKSLorentz.E)) i ∂OAI.CKSSphericalHarmonics.surfaceMeasure

def spatialADMMomentum (A B : OAI.CKSLorentz.SpatialTensor) (r : ℝ) : Fin 3 → ℝ := fun i =>
  r^2/(8*Real.pi) * ∫ n : OAI.CKSLorentz.Sphere,
    ∑ j : Fin 3, (OAI.CKSLorentz.spatialCartesian B (r • (n:OAI.CKSLorentz.E)) i j -
      (∑ a : Fin 3, ∑ b : Fin 3,
        (OAI.CKSLorentz.spatialCartesian A (r • (n:OAI.CKSLorentz.E)))⁻¹ a b * OAI.CKSLorentz.spatialCartesian B (r • (n:OAI.CKSLorentz.E)) a b) *
      OAI.CKSLorentz.spatialCartesian A (r • (n:OAI.CKSLorentz.E)) i j) * OAI.CKSADM.normal (r • (n:OAI.CKSLorentz.E)) j ∂OAI.CKSSphericalHarmonics.surfaceMeasure

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSLorentz
open CKSMixedGeometry CKSAngularGeometry MeasureTheory

def spatialEnergy (A B : OAI.CKSLorentz.SpatialTensor) (x : OAI.CKSLorentz.E) : ℝ :=
  (OAI.CKSAngularGeometry.physicalMetricJet (OAI.CKSLorentz.spatialCoefficients A) (OAI.CKSCartesianOuter.toPoint x)).energy
    (OAI.CKSAngularGeometry.physicalTensorJet (OAI.CKSLorentz.spatialCoefficients B) (OAI.CKSCartesianOuter.toPoint x))

end OAI.CKSLorentz
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSReplacementCompleteness
open Bundle Manifold
open scoped Bundle Manifold ENNReal
variable {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_2} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_3} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

abbrev Metric := ContinuousRiemannianMetric E (fun x : M => TangentSpace I x)

local instance metric_isContinuousRiemannianBundle (g : OAI.CKSReplacementCompleteness.Metric I (M := M)) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) := inferInstance

@[instance_reducible] def metricSpace [T3Space M] (g : OAI.CKSReplacementCompleteness.Metric I (M := M)) : EMetricSpace M :=
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI := OAI.CKSReplacementCompleteness.metric_isContinuousRiemannianBundle I g
  EMetricSpace.ofRiemannianMetric I M

def IsComplete [T3Space M] (g : OAI.CKSReplacementCompleteness.Metric I (M := M)) : Prop :=
  @CompleteSpace M (OAI.CKSReplacementCompleteness.metricSpace I g).toUniformSpace

end OAI.CKSReplacementCompleteness
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSGeometricCuts
open Set Manifold MeasureTheory Bundle CKSReplacementCompleteness
open scoped ENNReal Manifold Bundle ContDiff

abbrev E3 := EuclideanSpace ℝ (Fin 3)

local instance halfSpaceDimension_neZero : NeZero (3 : ℕ) := inferInstance

abbrev H3 := @EuclideanHalfSpace 3 OAI.CKSGeometricCuts.halfSpaceDimension_neZero

abbrev I3 := @modelWithCornersEuclideanHalfSpace 3 OAI.CKSGeometricCuts.halfSpaceDimension_neZero

end OAI.CKSGeometricCuts
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSGeometricCuts
open Set Manifold MeasureTheory Bundle CKSReplacementCompleteness
open scoped ENNReal Manifold Bundle ContDiff
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 1 M]

structure OuterDomain where
  Carrier : Type u
  topology : TopologicalSpace Carrier
  charts : @ChartedSpace OAI.CKSGeometricCuts.H3 _ Carrier topology
  smooth : @IsManifold ℝ _ OAI.CKSGeometricCuts.E3 _ _ OAI.CKSGeometricCuts.H3 _ OAI.CKSGeometricCuts.I3 (∞ : ℕ∞ω) Carrier topology charts
  inclusion : Carrier → M
  embedding : @IsSmoothEmbedding ℝ _ OAI.CKSGeometricCuts.E3 OAI.CKSGeometricCuts.E3 _ _ _ _ OAI.CKSGeometricCuts.H3 OAI.CKSGeometricCuts.H3 _ _ OAI.CKSGeometricCuts.I3 OAI.CKSGeometricCuts.I3
    Carrier M topology charts _ _ ∞ inclusion
  closed : IsClosed (range inclusion)
  connected : IsConnected (range inclusion)
  contains_distant_end : ∃ K : Set M, IsCompact K ∧ Kᶜ ⊆ range inclusion
  interior_into : inclusion '' (@ModelWithCorners.interior ℝ _ OAI.CKSGeometricCuts.E3 _ _ OAI.CKSGeometricCuts.H3 _ OAI.CKSGeometricCuts.I3
    Carrier topology charts) ⊆ OAI.CKSGeometricCuts.I3.interior M
  compact_boundary : IsCompact (inclusion '' (@ModelWithCorners.boundary ℝ _ OAI.CKSGeometricCuts.E3 _ _ OAI.CKSGeometricCuts.H3 _ OAI.CKSGeometricCuts.I3
    Carrier topology charts))

end OAI.CKSGeometricCuts
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSpatialManifold
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] real_id_isometric CKSMetricGluing.real_continuousAdd CKSMetricGluing.real_continuousConstSMul CKSMetricGluing.real_smulCommClass


local instance real_id_compTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance

end OAI.CKSSpatialManifold
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSpatialManifold
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type u_1} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_2} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] real_id_isometric CKSMetricGluing.real_continuousAdd CKSMetricGluing.real_continuousConstSMul CKSMetricGluing.real_smulCommClass


def endInner (f : M → OAI.CKSLorentz.E) (A : OAI.CKSLorentz.SpatialTensor) : OAI.CKSMetricGluing.InnerField I (M := M) := fun x => by
  letI := OAI.CKSSpatialManifold.real_id_isometric
  letI := OAI.CKSSpatialManifold.real_id_compTriple
  letI : NormedAddCommGroup (TangentSpace I x) := by unfold TangentSpace; infer_instance
  letI : NormedSpace ℝ (TangentSpace I x) := by unfold TangentSpace; infer_instance
  let df : TangentSpace I x →L[ℝ] OAI.CKSLorentz.E :=
    (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ,OAI.CKSLorentz.E) f x)
  exact (A (f x)).bilinearComp df df

end OAI.CKSSpatialManifold
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSpatialManifold
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type u_1} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_2} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] CKSLorentz.hsgNorm CKSLorentz.hsgSpace


def PhysicalDECAt (g : OAI.CKSMetricGluing.InnerField I (M := M)) (K : OAI.CKSMetricGluing.InnerField I (M := M)) (x : M) : Prop :=
  ∃ (V : Set M) (f : M → OAI.CKSLorentz.E) (A B : OAI.CKSLorentz.SpatialTensor),
    IsOpen V ∧ x ∈ V ∧ ContMDiffOn I 𝓘(ℝ,OAI.CKSLorentz.E) ∞ f V ∧
    (∀ y ∈ V, Function.Bijective (mfderiv I 𝓘(ℝ,OAI.CKSLorentz.E) f y)) ∧
    (∀ y ∈ V, ContDiffAt ℝ ∞ A (f y) ∧ ContDiffAt ℝ ∞ B (f y)) ∧
    (∀ y ∈ V, (∀ v w, A (f y) v w = A (f y) w v) ∧
      (∀ v : OAI.CKSLorentz.E, v ≠ 0 → 0 < A (f y) v v) ∧
      (∀ v w, B (f y) v w = B (f y) w v)) ∧
    (∀ y ∈ V, g y = OAI.CKSSpatialManifold.endInner I f A y ∧ K y = OAI.CKSSpatialManifold.endInner I f B y) ∧
    OAI.CKSLorentz.spatialDEC A B (f x)

def PhysicalDEC (g : OAI.CKSMetricGluing.InnerField I (M := M)) (K : OAI.CKSMetricGluing.InnerField I (M := M)) : Prop :=
  ∀ x : M, OAI.CKSSpatialManifold.PhysicalDECAt I g K x

end OAI.CKSSpatialManifold
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicGeometry
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal ContDiff Topology NNReal

local instance halfSpaceDimension_neZero : NeZero (3 : ℕ) := inferInstance

abbrev H3 := @EuclideanHalfSpace 3 OAI.CKSIntrinsicGeometry.halfSpaceDimension_neZero

abbrev I3 := @modelWithCornersEuclideanHalfSpace 3 OAI.CKSIntrinsicGeometry.halfSpaceDimension_neZero

end OAI.CKSIntrinsicGeometry
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSBoundarySurface
open Set Manifold Bundle Filter
open scoped ContDiff Topology

abbrev E2 := EuclideanSpace ℝ (Fin 2)

abbrev E3 := EuclideanSpace ℝ (Fin 3)

local instance halfSpaceDimension_neZero : NeZero (3 : ℕ) := inferInstance

abbrev H3 := @EuclideanHalfSpace 3 OAI.CKSBoundarySurface.halfSpaceDimension_neZero

abbrev I2 := 𝓘(ℝ,OAI.CKSBoundarySurface.E2)

abbrev I3 := @modelWithCornersEuclideanHalfSpace 3 OAI.CKSBoundarySurface.halfSpaceDimension_neZero

local instance two_atLeastTwo : Nat.AtLeastTwo 2 := inferInstance

end OAI.CKSBoundarySurface
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSBoundarySurface
open Set Manifold Bundle Filter
open scoped ContDiff Topology
attribute [local instance] two_atLeastTwo


def insertNormalZero (point : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.E3 := WithLp.toLp 2 (Fin.cons 0 point)

def liftPlane : OAI.CKSBoundarySurface.E2 →L[ℝ] OAI.CKSBoundarySurface.E3 :=
  have proof_insertNormalZero_add_0  (first second : OAI.CKSBoundarySurface.E2) :
      OAI.CKSBoundarySurface.insertNormalZero (first + second) = OAI.CKSBoundarySurface.insertNormalZero first + OAI.CKSBoundarySurface.insertNormalZero second := by
    ext index
    cases index using Fin.cases <;> simp [OAI.CKSBoundarySurface.insertNormalZero]
  have proof_insertNormalZero_smul_1  (scalar : ℝ) (point : OAI.CKSBoundarySurface.E2) :
      OAI.CKSBoundarySurface.insertNormalZero (scalar • point) = scalar • OAI.CKSBoundarySurface.insertNormalZero point := by
    ext index
    cases index using Fin.cases <;> simp [OAI.CKSBoundarySurface.insertNormalZero]
  have proof_insertNormalZero_continuous_2  : Continuous OAI.CKSBoundarySurface.insertNormalZero := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro index
    cases index using Fin.cases with
    | zero => exact continuous_const
    | succ index => exact PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) index
  {
    toFun := OAI.CKSBoundarySurface.insertNormalZero
    map_add' := proof_insertNormalZero_add_0
    map_smul' := proof_insertNormalZero_smul_1
    cont := proof_insertNormalZero_continuous_2
  }

def tangentialCoordinates (point : OAI.CKSBoundarySurface.E3) : OAI.CKSBoundarySurface.E2 := WithLp.toLp 2 (fun index => point index.succ)

def dropPlane : OAI.CKSBoundarySurface.E3 →L[ℝ] OAI.CKSBoundarySurface.E2 :=
  have proof_tangentialCoordinates_add_3  (first second : OAI.CKSBoundarySurface.E3) :
      OAI.CKSBoundarySurface.tangentialCoordinates (first + second) =
        OAI.CKSBoundarySurface.tangentialCoordinates first + OAI.CKSBoundarySurface.tangentialCoordinates second := by
    ext index
    simp [OAI.CKSBoundarySurface.tangentialCoordinates]
  have proof_tangentialCoordinates_smul_4  (scalar : ℝ) (point : OAI.CKSBoundarySurface.E3) :
      OAI.CKSBoundarySurface.tangentialCoordinates (scalar • point) = scalar • OAI.CKSBoundarySurface.tangentialCoordinates point := by
    ext index
    simp [OAI.CKSBoundarySurface.tangentialCoordinates]
  have proof_tangentialCoordinates_continuous_5  : Continuous OAI.CKSBoundarySurface.tangentialCoordinates := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    exact continuous_pi fun index => PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) index.succ
  {
    toFun := OAI.CKSBoundarySurface.tangentialCoordinates
    map_add' := proof_tangentialCoordinates_add_3
    map_smul' := proof_tangentialCoordinates_smul_4
    cont := proof_tangentialCoordinates_continuous_5
  }

end OAI.CKSBoundarySurface
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSBoundarySurface
open Set Manifold Bundle Filter
open scoped ContDiff Topology

def liftHalf (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.H3 :=
  have proof_liftPlane_zero_6  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.liftPlane z 0 = 0 := rfl
  have proof_liftPlane_succ_7  (z : OAI.CKSBoundarySurface.E2) (i : Fin 2) : OAI.CKSBoundarySurface.liftPlane z i.succ = z i := rfl
  ⟨OAI.CKSBoundarySurface.liftPlane z, by simp [*]⟩

end OAI.CKSBoundarySurface
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Manifold Bundle Filter
open scoped ContDiff Topology
open CKSBoundarySurface

abbrev Radial := {t : ℝ // 0 ≤ t}

abbrev Sphere := Metric.sphere (0 : OAI.CKSBoundarySurface.E3) 1

abbrev Exterior := OAI.CKSSchwarzschild.Radial × OAI.CKSSchwarzschild.Sphere

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Manifold Bundle Filter
open scoped ContDiff Topology
open CKSBoundarySurface
attribute [local instance] Classical.propDecidable


local instance real_id_invPair : RingHomInvPair (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance

def join : (ℝ × OAI.CKSBoundarySurface.E2) →L[ℝ] OAI.CKSBoundarySurface.E3 :=
  letI := OAI.CKSSchwarzschild.real_id_invPair
  letI := OAI.CKSBoundarySurface.two_atLeastTwo
  let continuousLinearMap : ((ℝ × OAI.CKSBoundarySurface.E2) →ₗ[ℝ] OAI.CKSBoundarySurface.E3) ≃ₗ[ℝ] ((ℝ × OAI.CKSBoundarySurface.E2) →L[ℝ] OAI.CKSBoundarySurface.E3) :=
    LinearMap.toContinuousLinearMap
  continuousLinearMap {
    toFun := fun z => WithLp.toLp 2 (Fin.cons z.1 z.2)
    map_add' := by intro a b; ext i; cases i using Fin.cases <;> simp
    map_smul' := by intro a b; ext i; cases i using Fin.cases <;> simp }

def halfProduct : OAI.CKSSchwarzschild.Radial × OAI.CKSBoundarySurface.E2 ≃ₜ OAI.CKSBoundarySurface.H3 :=
  have proof_join_zero_9  (z : ℝ × OAI.CKSBoundarySurface.E2) : OAI.CKSSchwarzschild.join z 0 = z.1 := rfl
  have proof_join_succ_10  (z : ℝ × OAI.CKSBoundarySurface.E2) (i : Fin 2) : OAI.CKSSchwarzschild.join z i.succ = z.2 i := rfl
  have proof_join_drop_8  (z : OAI.CKSBoundarySurface.E3) : OAI.CKSSchwarzschild.join (z 0,OAI.CKSBoundarySurface.dropPlane z) = z := by
    ext i; cases i using Fin.cases <;> rfl
  have proof_drop_join_11  (z : ℝ × OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.dropPlane (OAI.CKSSchwarzschild.join z) = z.2 := by ext i; rfl
  letI := OAI.CKSBoundarySurface.halfSpaceDimension_neZero
  { toFun z := ⟨OAI.CKSSchwarzschild.join (z.1.val,z.2),z.1.property⟩
    invFun z := (⟨z.val 0,z.property⟩,OAI.CKSBoundarySurface.dropPlane z.val)
    left_inv z := by cases z; simp [*]
    right_inv z := by apply Subtype.ext; exact proof_join_drop_8 _
    continuous_toFun := (OAI.CKSSchwarzschild.join.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _
    continuous_invFun := ((by fun_prop : Continuous (fun z : H3 => z.val 0)).subtype_mk _).prodMk
      (OAI.CKSBoundarySurface.dropPlane.continuous.comp continuous_subtype_val) }

def productChart (s : OAI.CKSSchwarzschild.Sphere) : OpenPartialHomeomorph OAI.CKSSchwarzschild.Exterior OAI.CKSBoundarySurface.H3 :=
  ((OpenPartialHomeomorph.refl OAI.CKSSchwarzschild.Radial).prod (chartAt OAI.CKSBoundarySurface.E2 s)).trans OAI.CKSSchwarzschild.halfProduct.toOpenPartialHomeomorph

instance exteriorChartedSpace : ChartedSpace OAI.CKSBoundarySurface.H3 OAI.CKSSchwarzschild.Exterior :=
  have proof_join_zero_9  (z : ℝ × OAI.CKSBoundarySurface.E2) : OAI.CKSSchwarzschild.join z 0 = z.1 := rfl
  have proof_join_succ_10  (z : ℝ × OAI.CKSBoundarySurface.E2) (i : Fin 2) : OAI.CKSSchwarzschild.join z i.succ = z.2 i := rfl
  have proof_halfProduct_val_12  (z : OAI.CKSSchwarzschild.Radial × OAI.CKSBoundarySurface.E2) : (OAI.CKSSchwarzschild.halfProduct z).val = OAI.CKSSchwarzschild.join (z.1.val,z.2) := rfl
  have proof_halfProduct_symm_fst_13  (z : OAI.CKSBoundarySurface.H3) : (OAI.CKSSchwarzschild.halfProduct.symm z).1.val = z.val 0 := rfl
  have proof_halfProduct_symm_snd_14  (z : OAI.CKSBoundarySurface.H3) : (OAI.CKSSchwarzschild.halfProduct.symm z).2 = OAI.CKSBoundarySurface.dropPlane z.val := rfl
  {
    atlas := range OAI.CKSSchwarzschild.productChart
    chartAt p := OAI.CKSSchwarzschild.productChart p.2
    mem_chart_source p := by simp [*, OAI.CKSSchwarzschild.productChart,mem_chart_source OAI.CKSBoundarySurface.E2 p.2]
    chart_mem_atlas p := mem_range_self _
  }

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Manifold Bundle Filter
open scoped ContDiff Topology
open CKSBoundarySurface
attribute [local instance] halfSpaceDimension_neZero


instance exteriorIsManifold : IsManifold OAI.CKSBoundarySurface.I3 ∞ OAI.CKSSchwarzschild.Exterior :=
  have proof_join_zero_9  (z : ℝ × OAI.CKSBoundarySurface.E2) : OAI.CKSSchwarzschild.join z 0 = z.1 := rfl
  have proof_join_succ_10  (z : ℝ × OAI.CKSBoundarySurface.E2) (i : Fin 2) : OAI.CKSSchwarzschild.join z i.succ = z.2 i := rfl
  have proof_halfProduct_val_12  (z : OAI.CKSSchwarzschild.Radial × OAI.CKSBoundarySurface.E2) : (OAI.CKSSchwarzschild.halfProduct z).val = OAI.CKSSchwarzschild.join (z.1.val,z.2) := rfl
  have proof_halfProduct_symm_fst_13  (z : OAI.CKSBoundarySurface.H3) : (OAI.CKSSchwarzschild.halfProduct.symm z).1.val = z.val 0 := rfl
  have proof_halfProduct_symm_snd_14  (z : OAI.CKSBoundarySurface.H3) : (OAI.CKSSchwarzschild.halfProduct.symm z).2 = OAI.CKSBoundarySurface.dropPlane z.val := rfl
  have proof_productChart_target_17  (s : OAI.CKSSchwarzschild.Sphere) :
      (OAI.CKSSchwarzschild.productChart s).target = (fun z : OAI.CKSBoundarySurface.H3 => OAI.CKSBoundarySurface.dropPlane z.val) ⁻¹' (chartAt OAI.CKSBoundarySurface.E2 s).target := by
    ext p; simp [*, OAI.CKSSchwarzschild.productChart]
  have proof_productChart_source_18  (s : OAI.CKSSchwarzschild.Sphere) :
      (OAI.CKSSchwarzschild.productChart s).source = Prod.snd ⁻¹' (chartAt OAI.CKSBoundarySurface.E2 s).source := by
    ext p; simp [*, OAI.CKSSchwarzschild.productChart]
  have proof_productChart_symm_19  (s : OAI.CKSSchwarzschild.Sphere) (z : OAI.CKSBoundarySurface.H3) :
      (OAI.CKSSchwarzschild.productChart s).symm z = (⟨z.val 0,z.property⟩,(chartAt OAI.CKSBoundarySurface.E2 s).symm (OAI.CKSBoundarySurface.dropPlane z.val)) := rfl
  have proof_transition_source_20  (a b : OAI.CKSSchwarzschild.Sphere) :
      ((OAI.CKSSchwarzschild.productChart a).symm ≫ₕ OAI.CKSSchwarzschild.productChart b).source =
        (fun z : OAI.CKSBoundarySurface.H3 => OAI.CKSBoundarySurface.dropPlane z.val) ⁻¹' ((chartAt OAI.CKSBoundarySurface.E2 a).symm ≫ₕ chartAt OAI.CKSBoundarySurface.E2 b).source := by
    ext z
    simp only [OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
      mem_inter_iff,mem_preimage,proof_productChart_target_17,proof_productChart_source_18,proof_productChart_symm_19]
  have proof_transition_maps_15  (a b : OAI.CKSSchwarzschild.Sphere) :
      MapsTo OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.I3.symm ⁻¹' ((OAI.CKSSchwarzschild.productChart a).symm ≫ₕ OAI.CKSSchwarzschild.productChart b).source ∩ range OAI.CKSBoundarySurface.I3)
        ((extChartAt OAI.CKSBoundarySurface.I2 a).symm ≫ extChartAt OAI.CKSBoundarySurface.I2 b).source := by
    intro z hz
    have he : (OAI.CKSBoundarySurface.I3.symm z).val = z := OAI.CKSBoundarySurface.I3.right_inv hz.2
    have h := hz.1
    rw [proof_transition_source_20] at h
    change OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.I3.symm z).val ∈ ((chartAt OAI.CKSBoundarySurface.E2 a).symm ≫ₕ chartAt OAI.CKSBoundarySurface.E2 b).source at h
    rw [he] at h
    simpa only [OAI.CKSBoundarySurface.I2,extChartAt_model_space_eq_id,mfld_simps] using h
  have proof_transition_formula_16  (a b : OAI.CKSSchwarzschild.Sphere) {z : OAI.CKSBoundarySurface.E3} (hz : z ∈ range OAI.CKSBoundarySurface.I3) :
      OAI.CKSBoundarySurface.I3 (((OAI.CKSSchwarzschild.productChart a).symm ≫ₕ OAI.CKSSchwarzschild.productChart b) (OAI.CKSBoundarySurface.I3.symm z)) =
        OAI.CKSSchwarzschild.join (z 0,((extChartAt OAI.CKSBoundarySurface.I2 a).symm ≫ extChartAt OAI.CKSBoundarySurface.I2 b) (OAI.CKSBoundarySurface.dropPlane z)) := by
    have he : (OAI.CKSBoundarySurface.I3.symm z).val = z := OAI.CKSBoundarySurface.I3.right_inv hz
    change OAI.CKSSchwarzschild.join ((OAI.CKSBoundarySurface.I3.symm z).val 0,
      chartAt OAI.CKSBoundarySurface.E2 b ((chartAt OAI.CKSBoundarySurface.E2 a).symm (OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.I3.symm z).val))) = _
    rw [he]
    rfl
  by
    apply isManifold_of_contDiffOn
    rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
    change ContDiffOn ℝ ∞
      (fun z => OAI.CKSBoundarySurface.I3 (((OAI.CKSSchwarzschild.productChart a).symm ≫ₕ OAI.CKSSchwarzschild.productChart b) (OAI.CKSBoundarySurface.I3.symm z)))
      (OAI.CKSBoundarySurface.I3.symm ⁻¹' ((OAI.CKSSchwarzschild.productChart a).symm ≫ₕ OAI.CKSSchwarzschild.productChart b).source ∩ range OAI.CKSBoundarySurface.I3)
    have hs := (contDiffOn_ext_coord_change (I := OAI.CKSBoundarySurface.I2) (n := ∞) b a).comp
      OAI.CKSBoundarySurface.dropPlane.contDiff.contDiffOn (proof_transition_maps_15 a b)
    have h0 : ContDiff ℝ ∞ (fun z : OAI.CKSBoundarySurface.E3 => z 0) := by fun_prop
    apply (OAI.CKSSchwarzschild.join.contDiff.comp_contDiffOn (h0.contDiffOn.prodMk hs)).congr
    intro z hz
    exact proof_transition_formula_16 a b hz.2

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Filter Manifold Bundle
open scoped ContDiff Topology
open CKSBoundarySurface

def height (p : OAI.CKSSchwarzschild.Exterior) : ℝ := p.1.val

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Filter Manifold Bundle Function
open scoped ContDiff Topology InnerProductSpace
open CKSBoundarySurface


def radius (m : ℝ) (p : OAI.CKSSchwarzschild.Exterior) : ℝ :=
  letI := OAI.CKSLorentz.two_atLeastTwo
  2*m+OAI.CKSSchwarzschild.height p

def directionAmbient (p : OAI.CKSSchwarzschild.Exterior) : OAI.CKSBoundarySurface.E3 := p.2.val

def position (m : ℝ) (p : OAI.CKSSchwarzschild.Exterior) : OAI.CKSBoundarySurface.E3 := OAI.CKSSchwarzschild.radius m p • OAI.CKSSchwarzschild.directionAmbient p

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Filter
open scoped ContDiff Topology

def velocity (m r : ℝ) : ℝ :=
  letI := OAI.CKSLorentz.two_atLeastTwo;
  -1 + (r+1)*Real.smoothTransition (r-2*m-1)

def lapseSquared (m r : ℝ) : ℝ :=
  letI := OAI.CKSLorentz.two_atLeastTwo
  1-2*m/r+(OAI.CKSSchwarzschild.velocity m r)^2

def lapse (m r : ℝ) : ℝ := Real.sqrt (OAI.CKSSchwarzschild.lapseSquared m r)

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Manifold Bundle Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology InnerProductSpace
open CKSBoundarySurface

def euclideanForm : OAI.CKSLorentz.SpatialBilinear := innerSL ℝ

def radialUnit (x : OAI.CKSBoundarySurface.E3) : OAI.CKSBoundarySurface.E3 := ‖x‖⁻¹ • x

local instance real_isScalarTower : IsScalarTower ℝ ℝ ℝ := inferInstance

def radialForm (x : OAI.CKSBoundarySurface.E3) : OAI.CKSLorentz.SpatialBilinear :=
  letI := OAI.CKSSpatialManifold.real_id_compTriple
  letI := OAI.CKSSpatialManifold.real_id_isometric
  letI := OAI.CKSSchwarzschild.real_isScalarTower
  letI := OAI.CKSLorentz.real_smulCommClass
  letI := OAI.CKSLorentz.real_isTopologicalAddGroup
  letI := OAI.CKSLorentz.real_continuousAdd
  letI := OAI.CKSLorentz.real_continuousConstSMul
  let innerForm : OAI.CKSLorentz.SpatialBilinear := innerSL ℝ
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (innerForm (OAI.CKSSchwarzschild.radialUnit x)) (innerForm (OAI.CKSSchwarzschild.radialUnit x))

local instance spatialDual_continuousAdd : ContinuousAdd (OAI.CKSBoundarySurface.E3 →L[ℝ] ℝ) := inferInstance

def cartMetric (m : ℝ) (x : OAI.CKSBoundarySurface.E3) : OAI.CKSLorentz.SpatialBilinear :=
  letI := OAI.CKSLorentz.real_continuousAdd
  letI := OAI.CKSLorentz.real_continuousConstSMul
  letI := OAI.CKSLorentz.real_smulCommClass
  letI := OAI.CKSSchwarzschild.spatialDual_continuousAdd
  letI := OAI.CKSLorentz.spatialDual_smulCommClass
  letI := OAI.CKSLorentz.spatialDual_continuousConstSMul
  OAI.CKSSchwarzschild.euclideanForm + ((OAI.CKSSchwarzschild.lapseSquared m ‖x‖)⁻¹-1) • OAI.CKSSchwarzschild.radialForm x

def cartTensor (m : ℝ) (x : OAI.CKSBoundarySurface.E3) : OAI.CKSLorentz.SpatialBilinear :=
  letI := OAI.CKSLorentz.real_continuousAdd
  letI := OAI.CKSLorentz.real_continuousConstSMul
  letI := OAI.CKSLorentz.real_smulCommClass
  letI := OAI.CKSSchwarzschild.spatialDual_continuousAdd
  letI := OAI.CKSLorentz.spatialDual_smulCommClass
  letI := OAI.CKSLorentz.spatialDual_continuousConstSMul
  (OAI.CKSSchwarzschild.velocity m ‖x‖ / ‖x‖) • OAI.CKSSchwarzschild.euclideanForm +
    (deriv (OAI.CKSSchwarzschild.velocity m) ‖x‖ / OAI.CKSSchwarzschild.lapseSquared m ‖x‖ - OAI.CKSSchwarzschild.velocity m ‖x‖ / ‖x‖) • OAI.CKSSchwarzschild.radialForm x

def metricInner (m : ℝ) : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := OAI.CKSSchwarzschild.Exterior) := OAI.CKSSpatialManifold.endInner OAI.CKSBoundarySurface.I3 (OAI.CKSSchwarzschild.position m) (OAI.CKSSchwarzschild.cartMetric m)

def tensorInner (m : ℝ) : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := OAI.CKSSchwarzschild.Exterior) := OAI.CKSSpatialManifold.endInner OAI.CKSBoundarySurface.I3 (OAI.CKSSchwarzschild.position m) (OAI.CKSSchwarzschild.cartTensor m)

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicConstraints
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped ContDiff Topology

abbrev E := OAI.CKSLorentz.E

local instance halfSpaceDimension_neZero : NeZero (3 : ℕ) := inferInstance

abbrev H := @EuclideanHalfSpace 3 OAI.CKSIntrinsicConstraints.halfSpaceDimension_neZero

abbrev I := @modelWithCornersEuclideanHalfSpace 3 OAI.CKSIntrinsicConstraints.halfSpaceDimension_neZero

end OAI.CKSIntrinsicConstraints
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicConstraints
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped ContDiff Topology
attribute [local instance] halfSpaceDimension_neZero
attribute [local instance] CKSSpatialManifold.real_id_isometric CKSLorentz.real_smulCommClass CKSLorentz.spatialDual_smulCommClass
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def coordinateMomentumNorm (A B : OAI.CKSLorentz.SpatialTensor) (x : OAI.CKSIntrinsicConstraints.E) : ℝ :=
  Real.sqrt (OAI.CKSLocalBending.momentumSq
    (OAI.CKSAngularGeometry.physicalMetricJet (OAI.CKSLorentz.spatialCoefficients A) (OAI.CKSCartesianOuter.toPoint x))
    (OAI.CKSAngularGeometry.physicalTensorJet (OAI.CKSLorentz.spatialCoefficients B) (OAI.CKSCartesianOuter.toPoint x)))

end OAI.CKSIntrinsicConstraints
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicConstraints
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped ContDiff Topology
attribute [local instance] halfSpaceDimension_neZero
attribute [local instance] CKSSpatialManifold.real_id_isometric CKSLorentz.real_smulCommClass CKSLorentz.spatialDual_smulCommClass
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure ConstraintChart (g K : OAI.CKSMetricGluing.InnerField OAI.CKSIntrinsicConstraints.I (M := M)) (x : M) where
  domain : Set M
  coordinate : M → OAI.CKSIntrinsicConstraints.E
  metric : OAI.CKSLorentz.SpatialTensor
  tensor : OAI.CKSLorentz.SpatialTensor
  isOpen : IsOpen domain
  mem : x ∈ domain
  smooth : ContMDiffOn OAI.CKSIntrinsicConstraints.I 𝓘(ℝ,OAI.CKSIntrinsicConstraints.E) ∞ coordinate domain
  fullRank : ∀ y ∈ domain, Function.Bijective (mfderiv OAI.CKSIntrinsicConstraints.I 𝓘(ℝ,OAI.CKSIntrinsicConstraints.E) coordinate y)
  coefficientSmooth :
    letI := OAI.CKSLorentz.real_smulCommClass
    letI := OAI.CKSLorentz.spatialDual_smulCommClass
    ∀ y ∈ domain,
      ContDiffAt ℝ ∞ metric (coordinate y) ∧ ContDiffAt ℝ ∞ tensor (coordinate y)
  positiveSymmetric : ∀ y ∈ domain,
    (∀ v w, metric (coordinate y) v w = metric (coordinate y) w v) ∧
    (∀ v : OAI.CKSIntrinsicConstraints.E, v ≠ 0 → 0 < metric (coordinate y) v v) ∧
    (∀ v w, tensor (coordinate y) v w = tensor (coordinate y) w v)
  represents : ∀ y ∈ domain,
    g y = OAI.CKSSpatialManifold.endInner OAI.CKSIntrinsicConstraints.I coordinate metric y ∧
    K y = OAI.CKSSpatialManifold.endInner OAI.CKSIntrinsicConstraints.I coordinate tensor y

def ConstraintChart.energy {g K : OAI.CKSMetricGluing.InnerField OAI.CKSIntrinsicConstraints.I (M := M)} {x : M}
    (c : OAI.CKSIntrinsicConstraints.ConstraintChart g K x) : ℝ := OAI.CKSLorentz.spatialEnergy c.metric c.tensor (c.coordinate x)

def ConstraintChart.momentumNorm {g K : OAI.CKSMetricGluing.InnerField OAI.CKSIntrinsicConstraints.I (M := M)} {x : M}
    (c : OAI.CKSIntrinsicConstraints.ConstraintChart g K x) : ℝ := OAI.CKSIntrinsicConstraints.coordinateMomentumNorm c.metric c.tensor (c.coordinate x)

end OAI.CKSIntrinsicConstraints
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero


abbrev E := EuclideanSpace ℝ (Fin 3)

abbrev H := @EuclideanHalfSpace 3 OAI.CKSIntrinsicConstraints.halfSpaceDimension_neZero

abbrev I := @modelWithCornersEuclideanHalfSpace 3 OAI.CKSIntrinsicConstraints.halfSpaceDimension_neZero

abbrev basis (i : Fin 3) : OAI.CKSIntrinsicVolume.E := EuclideanSpace.single i 1

local instance model_finiteDimensional : FiniteDimensional ℝ OAI.CKSIntrinsicVolume.E := inferInstance

end OAI.CKSIntrinsicVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
attribute [local instance] model_finiteDimensional


local instance model_borelSpace : BorelSpace OAI.CKSIntrinsicVolume.E := inferInstance

end OAI.CKSIntrinsicVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

abbrev Metric := ContinuousRiemannianMetric OAI.CKSIntrinsicVolume.E (fun x : M => TangentSpace OAI.CKSIntrinsicVolume.I x)

def chartFrame (x : M) (y : OAI.CKSIntrinsicVolume.E) : OAI.CKSIntrinsicVolume.E →L[ℝ] TangentSpace OAI.CKSIntrinsicVolume.I ((extChartAt OAI.CKSIntrinsicVolume.I x).symm y) :=
  mfderivWithin 𝓘(ℝ,OAI.CKSIntrinsicVolume.E) OAI.CKSIntrinsicVolume.I (extChartAt OAI.CKSIntrinsicVolume.I x).symm (range OAI.CKSIntrinsicVolume.I) y

def chartMatrix (g : OAI.CKSIntrinsicVolume.Metric (M := M)) (x : M) (y : OAI.CKSIntrinsicVolume.E) : Matrix (Fin 3) (Fin 3) ℝ :=
  letI := OAI.CKSMetricGluing.real_continuousAdd
  letI := OAI.CKSMetricGluing.real_continuousConstSMul
  letI := OAI.CKSMetricGluing.real_smulCommClass
  let form : TangentSpace OAI.CKSIntrinsicVolume.I ((extChartAt OAI.CKSIntrinsicVolume.I x).symm y) →L[ℝ]
      TangentSpace OAI.CKSIntrinsicVolume.I ((extChartAt OAI.CKSIntrinsicVolume.I x).symm y) →L[ℝ] ℝ :=
    g.inner ((extChartAt OAI.CKSIntrinsicVolume.I x).symm y)
  fun first second => form (OAI.CKSIntrinsicVolume.chartFrame x y (OAI.CKSIntrinsicVolume.basis first)) (OAI.CKSIntrinsicVolume.chartFrame x y (OAI.CKSIntrinsicVolume.basis second))

def chartDensity (g : OAI.CKSIntrinsicVolume.Metric (M := M)) (x : M) (y : OAI.CKSIntrinsicVolume.E) : ℝ :=
  Real.sqrt (OAI.CKSIntrinsicVolume.chartMatrix g x y).det

end OAI.CKSIntrinsicVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
attribute [local instance] model_finiteDimensional model_borelSpace
variable [MeasurableSpace M] [BorelSpace M]

def localVolume (g : OAI.CKSIntrinsicVolume.Metric (M := M)) (x : M) : Measure M :=
  Measure.map (extChartAt OAI.CKSIntrinsicVolume.I x).symm
    ((volume.restrict (extChartAt OAI.CKSIntrinsicVolume.I x).target).withDensity
      (fun y => ENNReal.ofReal (OAI.CKSIntrinsicVolume.chartDensity g x y)))

def IsVolume (g : OAI.CKSIntrinsicVolume.Metric (M := M)) (ν : Measure M) : Prop :=
  ∀ x : M, ν.restrict (extChartAt OAI.CKSIntrinsicVolume.I x).source = OAI.CKSIntrinsicVolume.localVolume g x

end OAI.CKSIntrinsicVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
variable [IsManifold I 1 M]

def riemannianVolume (g : OAI.CKSIntrinsicVolume.Metric (M := M)) : Measure M := Classical.epsilon (fun ν => OAI.CKSIntrinsicVolume.IsVolume g ν)

end OAI.CKSIntrinsicVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSBoundarySurface
open Set Manifold Bundle Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
variable {M : Type u_2} [TopologicalSpace M] [ChartedSpace H3 M]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 halfSpaceDimension_neZero) I3 ∞ M _ _]

abbrev Boundary (M : Type u_2) [TopologicalSpace M] [ChartedSpace OAI.CKSBoundarySurface.H3 M] :=
  @ModelWithCorners.boundary ℝ _ OAI.CKSBoundarySurface.E3 _ _ OAI.CKSBoundarySurface.H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 OAI.CKSBoundarySurface.halfSpaceDimension_neZero) OAI.CKSBoundarySurface.I3 M _ _

end OAI.CKSBoundarySurface
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSBoundarySurface
open Set Manifold Bundle Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H3 M]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 halfSpaceDimension_neZero) I3 ∞ M _ _]

def boundaryInverse (x : OAI.CKSBoundarySurface.Boundary M) (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.Boundary M :=
  have proof_boundary_chart_zero_22 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSIntrinsicGeometry.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSIntrinsicGeometry.I3 1 M]  (x y : M) (hy : y ∈ (extChartAt OAI.CKSIntrinsicGeometry.I3 x).source)
      (hS : y ∈ OAI.CKSIntrinsicGeometry.I3.boundary M) : (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 = 0 := by
    have hychart : y ∈ (chartAt OAI.CKSIntrinsicGeometry.H3 x).source := by simpa using hy
    have hyrange : extChartAt OAI.CKSIntrinsicGeometry.I3 x y ∈ range OAI.CKSIntrinsicGeometry.I3 :=
      (extChartAt_target_subset_range x) ((extChartAt OAI.CKSIntrinsicGeometry.I3 x).map_source hy)
    have hnonneg : 0 ≤ (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 := by
      simpa only [OAI.CKSIntrinsicGeometry.I3, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hyrange
    have hnot : ¬OAI.CKSIntrinsicGeometry.I3.IsInteriorPoint y :=
      (OAI.CKSIntrinsicGeometry.I3.isBoundaryPoint_iff_not_isInteriorPoint y).mp hS
    have hle : (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 ≤ 0 := by
      by_contra h
      have hpos : 0 < (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 := lt_of_not_ge h
      have hint : extChartAt OAI.CKSIntrinsicGeometry.I3 x y ∈ interior (range OAI.CKSIntrinsicGeometry.I3) := by
        simpa only [OAI.CKSIntrinsicGeometry.I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hpos
      apply hnot
      apply (OAI.CKSIntrinsicGeometry.I3.isInteriorPoint_iff_of_mem_atlas one_ne_zero (chart_mem_atlas OAI.CKSIntrinsicGeometry.H3 x) hychart).mpr
      exact (chartAt OAI.CKSIntrinsicGeometry.H3 x).mem_interior_extend_target ((chartAt OAI.CKSIntrinsicGeometry.H3 x).map_source hychart) hint
    exact le_antisymm hle hnonneg
  have proof_liftPlane_zero_6  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.liftPlane z 0 = 0 := rfl
  have proof_liftPlane_succ_7  (z : OAI.CKSBoundarySurface.E2) (i : Fin 2) : OAI.CKSBoundarySurface.liftPlane z i.succ = z i := rfl
  have proof_I3_liftHalf_23  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.I3 (OAI.CKSBoundarySurface.liftHalf z) = OAI.CKSBoundarySurface.liftPlane z := rfl
  have proof_boundary_iff_zero_24 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x y : M) (hy : y ∈ (chartAt OAI.CKSBoundarySurface.H3 x).source) :
      y ∈ OAI.CKSBoundarySurface.I3.boundary M ↔ (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x y)) 0 = 0 := by
    constructor
    · exact proof_boundary_chart_zero_22 x y (by simp [*])
    · intro hz
      apply (OAI.CKSBoundarySurface.I3.isBoundaryPoint_iff_not_isInteriorPoint y).mpr
      intro hi
      have hin := (OAI.CKSBoundarySurface.I3.isInteriorPoint_iff_of_mem_atlas
        (by simp [*] : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas OAI.CKSBoundarySurface.H3 x) hy).mp hi
      have hr := (chartAt OAI.CKSBoundarySurface.H3 x).interior_extend_target_subset_interior_range hin
      have hp : 0 < (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x y)) 0 := by
        simpa only [OAI.CKSBoundarySurface.I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
          OpenPartialHomeomorph.extend_coe, Function.comp_apply] using hr
      rw [hz] at hp
      exact (lt_irrefl 0) hp
  have proof_chart_inverse_boundary_25 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x).target) :
      (chartAt OAI.CKSBoundarySurface.H3 x).symm (OAI.CKSBoundarySurface.liftHalf z) ∈ OAI.CKSBoundarySurface.I3.boundary M := by
    apply (proof_boundary_iff_zero_24 x _ ((chartAt OAI.CKSBoundarySurface.H3 x).map_target hz)).mpr
    rw [(chartAt OAI.CKSBoundarySurface.H3 x).right_inv hz]
    rfl
  have proof_boundaryInverse_mem_21 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).target) :
      (chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z) ∈ OAI.CKSBoundarySurface.Boundary M :=
    proof_chart_inverse_boundary_25 x.val hz
  if hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).target then
    ⟨(chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z),proof_boundaryInverse_mem_21 x hz⟩ else x

def boundaryChart (x : OAI.CKSBoundarySurface.Boundary M) : OpenPartialHomeomorph (OAI.CKSBoundarySurface.Boundary M) OAI.CKSBoundarySurface.E2 :=
  have proof_lift_drop_30  {z : OAI.CKSBoundarySurface.E3} (hz : z 0 = 0) : OAI.CKSBoundarySurface.liftPlane (OAI.CKSBoundarySurface.dropPlane z) = z := by
    ext i
    cases i using Fin.cases with
    | zero => exact hz.symm
    | succ i => rfl
  have proof_boundary_chart_zero_22 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSIntrinsicGeometry.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSIntrinsicGeometry.I3 1 M]  (x y : M) (hy : y ∈ (extChartAt OAI.CKSIntrinsicGeometry.I3 x).source)
      (hS : y ∈ OAI.CKSIntrinsicGeometry.I3.boundary M) : (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 = 0 := by
    have hychart : y ∈ (chartAt OAI.CKSIntrinsicGeometry.H3 x).source := by simpa using hy
    have hyrange : extChartAt OAI.CKSIntrinsicGeometry.I3 x y ∈ range OAI.CKSIntrinsicGeometry.I3 :=
      (extChartAt_target_subset_range x) ((extChartAt OAI.CKSIntrinsicGeometry.I3 x).map_source hy)
    have hnonneg : 0 ≤ (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 := by
      simpa only [OAI.CKSIntrinsicGeometry.I3, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hyrange
    have hnot : ¬OAI.CKSIntrinsicGeometry.I3.IsInteriorPoint y :=
      (OAI.CKSIntrinsicGeometry.I3.isBoundaryPoint_iff_not_isInteriorPoint y).mp hS
    have hle : (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 ≤ 0 := by
      by_contra h
      have hpos : 0 < (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 := lt_of_not_ge h
      have hint : extChartAt OAI.CKSIntrinsicGeometry.I3 x y ∈ interior (range OAI.CKSIntrinsicGeometry.I3) := by
        simpa only [OAI.CKSIntrinsicGeometry.I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hpos
      apply hnot
      apply (OAI.CKSIntrinsicGeometry.I3.isInteriorPoint_iff_of_mem_atlas one_ne_zero (chart_mem_atlas OAI.CKSIntrinsicGeometry.H3 x) hychart).mpr
      exact (chartAt OAI.CKSIntrinsicGeometry.H3 x).mem_interior_extend_target ((chartAt OAI.CKSIntrinsicGeometry.H3 x).map_source hychart) hint
    exact le_antisymm hle hnonneg
  have proof_liftPlane_zero_6  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.liftPlane z 0 = 0 := rfl
  have proof_liftPlane_succ_7  (z : OAI.CKSBoundarySurface.E2) (i : Fin 2) : OAI.CKSBoundarySurface.liftPlane z i.succ = z i := rfl
  have proof_I3_liftHalf_23  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.I3 (OAI.CKSBoundarySurface.liftHalf z) = OAI.CKSBoundarySurface.liftPlane z := rfl
  have proof_boundary_iff_zero_24 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x y : M) (hy : y ∈ (chartAt OAI.CKSBoundarySurface.H3 x).source) :
      y ∈ OAI.CKSBoundarySurface.I3.boundary M ↔ (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x y)) 0 = 0 := by
    constructor
    · exact proof_boundary_chart_zero_22 x y (by simp [*])
    · intro hz
      apply (OAI.CKSBoundarySurface.I3.isBoundaryPoint_iff_not_isInteriorPoint y).mpr
      intro hi
      have hin := (OAI.CKSBoundarySurface.I3.isInteriorPoint_iff_of_mem_atlas
        (by simp [*] : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas OAI.CKSBoundarySurface.H3 x) hy).mp hi
      have hr := (chartAt OAI.CKSBoundarySurface.H3 x).interior_extend_target_subset_interior_range hin
      have hp : 0 < (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x y)) 0 := by
        simpa only [OAI.CKSBoundarySurface.I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
          OpenPartialHomeomorph.extend_coe, Function.comp_apply] using hr
      rw [hz] at hp
      exact (lt_irrefl 0) hp
  have proof_liftHalf_drop_chart_26 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : M) (y : OAI.CKSBoundarySurface.Boundary M) (hy : y.val ∈ (chartAt OAI.CKSBoundarySurface.H3 x).source) :
      OAI.CKSBoundarySurface.liftHalf (OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x y.val))) = chartAt OAI.CKSBoundarySurface.H3 x y.val := by
    apply Subtype.ext
    exact proof_lift_drop_30 ((proof_boundary_iff_zero_24 x y.val hy).mp y.property)
  have proof_chart_inverse_boundary_25 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x).target) :
      (chartAt OAI.CKSBoundarySurface.H3 x).symm (OAI.CKSBoundarySurface.liftHalf z) ∈ OAI.CKSBoundarySurface.I3.boundary M := by
    apply (proof_boundary_iff_zero_24 x _ ((chartAt OAI.CKSBoundarySurface.H3 x).map_target hz)).mpr
    rw [(chartAt OAI.CKSBoundarySurface.H3 x).right_inv hz]
    rfl
  have proof_boundaryInverse_mem_21 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).target) :
      (chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z) ∈ OAI.CKSBoundarySurface.Boundary M :=
    proof_chart_inverse_boundary_25 x.val hz
  have proof_boundaryInverse_val_27 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).target) :
      (OAI.CKSBoundarySurface.boundaryInverse x z).val = (chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z) := by
    simp only [OAI.CKSBoundarySurface.boundaryInverse,dite_eq_left hz]
  have proof_dropPlane_apply_31  (z : OAI.CKSBoundarySurface.E3) (i : Fin 2) : OAI.CKSBoundarySurface.dropPlane z i = z i.succ := rfl
  have proof_drop_lift_28  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.liftPlane z) = z := by ext i; rfl
  have proof_liftHalf_continuous_29  : Continuous OAI.CKSBoundarySurface.liftHalf :=
    OAI.CKSBoundarySurface.liftPlane.continuous.subtype_mk (fun _ => by simp [*])
  {
    toFun y := OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x.val y.val))
    invFun := OAI.CKSBoundarySurface.boundaryInverse x
    source := Subtype.val ⁻¹' (chartAt OAI.CKSBoundarySurface.H3 x.val).source
    target := OAI.CKSBoundarySurface.liftHalf ⁻¹' (chartAt OAI.CKSBoundarySurface.H3 x.val).target
    map_source' := by
      intro y hy
      change OAI.CKSBoundarySurface.liftHalf (OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x.val y.val))) ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).target
      rw [proof_liftHalf_drop_chart_26 x.val y hy]
      exact (chartAt OAI.CKSBoundarySurface.H3 x.val).map_source hy
    map_target' := by
      intro z hz
      change (OAI.CKSBoundarySurface.boundaryInverse x z).val ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).source
      rw [proof_boundaryInverse_val_27 x hz]
      exact (chartAt OAI.CKSBoundarySurface.H3 x.val).map_target hz
    left_inv' := by
      intro y hy
      have h := proof_liftHalf_drop_chart_26 x.val y hy
      apply Subtype.ext
      rw [proof_boundaryInverse_val_27 x (by rw [h]; exact (chartAt OAI.CKSBoundarySurface.H3 x.val).map_source hy),h]
      exact (chartAt OAI.CKSBoundarySurface.H3 x.val).left_inv hy
    right_inv' := by
      intro z hz
      rw [proof_boundaryInverse_val_27 x hz,(chartAt OAI.CKSBoundarySurface.H3 x.val).right_inv hz,proof_I3_liftHalf_23,proof_drop_lift_28]
    open_source := (chartAt OAI.CKSBoundarySurface.H3 x.val).open_source.preimage continuous_subtype_val
    open_target := (chartAt OAI.CKSBoundarySurface.H3 x.val).open_target.preimage proof_liftHalf_continuous_29
    continuousOn_toFun := OAI.CKSBoundarySurface.dropPlane.continuous.comp_continuousOn
      (OAI.CKSBoundarySurface.I3.continuous.comp_continuousOn ((chartAt OAI.CKSBoundarySurface.H3 x.val).continuousOn.comp
        continuous_subtype_val.continuousOn (fun _ h => h)))
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply ((chartAt OAI.CKSBoundarySurface.H3 x.val).continuousOn_symm.comp
        proof_liftHalf_continuous_29.continuousOn (fun _ h => h)).congr
      intro z hz
      exact proof_boundaryInverse_val_27 x hz
  }

instance boundaryChartedSpace : ChartedSpace OAI.CKSBoundarySurface.E2 (OAI.CKSBoundarySurface.Boundary M) where
  atlas := range OAI.CKSBoundarySurface.boundaryChart
  chartAt := OAI.CKSBoundarySurface.boundaryChart
  mem_chart_source x := mem_chart_source OAI.CKSBoundarySurface.H3 x.val
  chart_mem_atlas x := mem_range_self x

end OAI.CKSBoundarySurface
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSBoundarySurface
open Set Manifold Bundle Filter Function
open scoped ContDiff Topology
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M]

instance boundaryIsManifold : IsManifold OAI.CKSBoundarySurface.I2 ∞ (OAI.CKSBoundarySurface.Boundary M) :=
  have proof_lift_mem_ext_target_34 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  [IsManifold OAI.CKSBoundarySurface.I3 ∞ M] (x : M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x).target) :
      OAI.CKSBoundarySurface.liftPlane z ∈ (extChartAt OAI.CKSBoundarySurface.I3 x).target := by
    change OAI.CKSBoundarySurface.liftPlane z ∈ ((chartAt OAI.CKSBoundarySurface.H3 x).extend OAI.CKSBoundarySurface.I3).target
    rw [OpenPartialHomeomorph.extend_target']
    exact ⟨OAI.CKSBoundarySurface.liftHalf z,hz,rfl⟩
  have proof_ext_symm_lift_35 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  [IsManifold OAI.CKSBoundarySurface.I3 ∞ M] (x : M) (z : OAI.CKSBoundarySurface.E2) :
      (extChartAt OAI.CKSBoundarySurface.I3 x).symm (OAI.CKSBoundarySurface.liftPlane z) = (chartAt OAI.CKSBoundarySurface.H3 x).symm (OAI.CKSBoundarySurface.liftHalf z) := by
    change (chartAt OAI.CKSBoundarySurface.H3 x).symm (OAI.CKSBoundarySurface.I3.symm (OAI.CKSBoundarySurface.I3 (OAI.CKSBoundarySurface.liftHalf z))) = _
    rw [OAI.CKSBoundarySurface.I3.left_inv]
  have proof_boundary_chart_zero_22 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSIntrinsicGeometry.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSIntrinsicGeometry.I3 1 M]  (x y : M) (hy : y ∈ (extChartAt OAI.CKSIntrinsicGeometry.I3 x).source)
      (hS : y ∈ OAI.CKSIntrinsicGeometry.I3.boundary M) : (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 = 0 := by
    have hychart : y ∈ (chartAt OAI.CKSIntrinsicGeometry.H3 x).source := by simpa using hy
    have hyrange : extChartAt OAI.CKSIntrinsicGeometry.I3 x y ∈ range OAI.CKSIntrinsicGeometry.I3 :=
      (extChartAt_target_subset_range x) ((extChartAt OAI.CKSIntrinsicGeometry.I3 x).map_source hy)
    have hnonneg : 0 ≤ (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 := by
      simpa only [OAI.CKSIntrinsicGeometry.I3, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hyrange
    have hnot : ¬OAI.CKSIntrinsicGeometry.I3.IsInteriorPoint y :=
      (OAI.CKSIntrinsicGeometry.I3.isBoundaryPoint_iff_not_isInteriorPoint y).mp hS
    have hle : (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 ≤ 0 := by
      by_contra h
      have hpos : 0 < (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 := lt_of_not_ge h
      have hint : extChartAt OAI.CKSIntrinsicGeometry.I3 x y ∈ interior (range OAI.CKSIntrinsicGeometry.I3) := by
        simpa only [OAI.CKSIntrinsicGeometry.I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hpos
      apply hnot
      apply (OAI.CKSIntrinsicGeometry.I3.isInteriorPoint_iff_of_mem_atlas one_ne_zero (chart_mem_atlas OAI.CKSIntrinsicGeometry.H3 x) hychart).mpr
      exact (chartAt OAI.CKSIntrinsicGeometry.H3 x).mem_interior_extend_target ((chartAt OAI.CKSIntrinsicGeometry.H3 x).map_source hychart) hint
    exact le_antisymm hle hnonneg
  have proof_liftPlane_zero_6  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.liftPlane z 0 = 0 := rfl
  have proof_liftPlane_succ_7  (z : OAI.CKSBoundarySurface.E2) (i : Fin 2) : OAI.CKSBoundarySurface.liftPlane z i.succ = z i := rfl
  have proof_I3_liftHalf_23  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.I3 (OAI.CKSBoundarySurface.liftHalf z) = OAI.CKSBoundarySurface.liftPlane z := rfl
  have proof_boundary_iff_zero_24 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x y : M) (hy : y ∈ (chartAt OAI.CKSBoundarySurface.H3 x).source) :
      y ∈ OAI.CKSBoundarySurface.I3.boundary M ↔ (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x y)) 0 = 0 := by
    constructor
    · exact proof_boundary_chart_zero_22 x y (by simp [*])
    · intro hz
      apply (OAI.CKSBoundarySurface.I3.isBoundaryPoint_iff_not_isInteriorPoint y).mpr
      intro hi
      have hin := (OAI.CKSBoundarySurface.I3.isInteriorPoint_iff_of_mem_atlas
        (by simp [*] : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas OAI.CKSBoundarySurface.H3 x) hy).mp hi
      have hr := (chartAt OAI.CKSBoundarySurface.H3 x).interior_extend_target_subset_interior_range hin
      have hp : 0 < (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x y)) 0 := by
        simpa only [OAI.CKSBoundarySurface.I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
          OpenPartialHomeomorph.extend_coe, Function.comp_apply] using hr
      rw [hz] at hp
      exact (lt_irrefl 0) hp
  have proof_chart_inverse_boundary_25 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x).target) :
      (chartAt OAI.CKSBoundarySurface.H3 x).symm (OAI.CKSBoundarySurface.liftHalf z) ∈ OAI.CKSBoundarySurface.I3.boundary M := by
    apply (proof_boundary_iff_zero_24 x _ ((chartAt OAI.CKSBoundarySurface.H3 x).map_target hz)).mpr
    rw [(chartAt OAI.CKSBoundarySurface.H3 x).right_inv hz]
    rfl
  have proof_boundaryInverse_mem_21 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).target) :
      (chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z) ∈ OAI.CKSBoundarySurface.Boundary M :=
    proof_chart_inverse_boundary_25 x.val hz
  have proof_boundaryInverse_val_27 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).target) :
      (OAI.CKSBoundarySurface.boundaryInverse x z).val = (chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z) := by
    simp only [OAI.CKSBoundarySurface.boundaryInverse,dite_eq_left hz]
  have proof_boundaryChart_symm_val_36 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2} (hz : z ∈ (OAI.CKSBoundarySurface.boundaryChart x).target) :
      ((OAI.CKSBoundarySurface.boundaryChart x).symm z).val = (chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z) :=
    proof_boundaryInverse_val_27 x hz
  have proof_transition_lift_maps_32 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x y : OAI.CKSBoundarySurface.Boundary M) :
      MapsTo OAI.CKSBoundarySurface.liftPlane ((OAI.CKSBoundarySurface.boundaryChart x).symm ≫ₕ OAI.CKSBoundarySurface.boundaryChart y).source
        ((extChartAt OAI.CKSBoundarySurface.I3 x.val).symm ≫ extChartAt OAI.CKSBoundarySurface.I3 y.val).source := by
    intro z hz
    change z ∈ (OAI.CKSBoundarySurface.boundaryChart x).target ∧ (OAI.CKSBoundarySurface.boundaryChart x).symm z ∈ (OAI.CKSBoundarySurface.boundaryChart y).source at hz
    refine ⟨proof_lift_mem_ext_target_34 x.val hz.1, ?_⟩
    change (extChartAt OAI.CKSBoundarySurface.I3 x.val).symm (OAI.CKSBoundarySurface.liftPlane z) ∈ (extChartAt OAI.CKSBoundarySurface.I3 y.val).source
    rw [proof_ext_symm_lift_35]
    have h := hz.2
    change ((OAI.CKSBoundarySurface.boundaryChart x).symm z).val ∈ (chartAt OAI.CKSBoundarySurface.H3 y.val).source at h
    rw [proof_boundaryChart_symm_val_36 x hz.1] at h
    simpa only [extChartAt_source] using h
  have proof_transition_formula_33 {M : Type u_1} [instLocal1 : TopologicalSpace.{u_1} M] [instLocal2 : ChartedSpace.{0, u_1} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u_1} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x y : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2}
      (hz : z ∈ ((OAI.CKSBoundarySurface.boundaryChart x).symm ≫ₕ OAI.CKSBoundarySurface.boundaryChart y).source) :
      ((OAI.CKSBoundarySurface.boundaryChart x).symm ≫ₕ OAI.CKSBoundarySurface.boundaryChart y) z =
        OAI.CKSBoundarySurface.dropPlane (((extChartAt OAI.CKSBoundarySurface.I3 x.val).symm ≫ extChartAt OAI.CKSBoundarySurface.I3 y.val) (OAI.CKSBoundarySurface.liftPlane z)) := by
    change OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 y.val ((OAI.CKSBoundarySurface.boundaryChart x).symm z).val)) = _
    rw [proof_boundaryChart_symm_val_36 x hz.1]
    change _ = OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 y.val ((extChartAt OAI.CKSBoundarySurface.I3 x.val).symm (OAI.CKSBoundarySurface.liftPlane z))))
    rw [proof_ext_symm_lift_35]
  by
    apply isManifold_of_contDiffOn
    rintro e e' ⟨x,rfl⟩ ⟨y,rfl⟩
    change ContDiffOn ℝ ∞ (fun z => ((OAI.CKSBoundarySurface.boundaryChart x).symm ≫ₕ OAI.CKSBoundarySurface.boundaryChart y) z)
      (id ⁻¹' ((OAI.CKSBoundarySurface.boundaryChart x).symm ≫ₕ OAI.CKSBoundarySurface.boundaryChart y).source ∩ range id)
    rw [preimage_id,range_id,inter_univ]
    apply (OAI.CKSBoundarySurface.dropPlane.contDiff.comp_contDiffOn ((contDiffOn_ext_coord_change (I := OAI.CKSBoundarySurface.I3) y.val x.val).comp
      OAI.CKSBoundarySurface.liftPlane.contDiff.contDiffOn (proof_transition_lift_maps_32 x y))).congr
    intro z hz
    exact proof_transition_formula_33 x y hz

end OAI.CKSBoundarySurface
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSurfaceVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal

abbrev E := EuclideanSpace ℝ (Fin 2)

abbrev H := OAI.CKSSurfaceVolume.E

abbrev I := 𝓘(ℝ,OAI.CKSSurfaceVolume.E)

abbrev basis (i : Fin 2) : OAI.CKSSurfaceVolume.E := EuclideanSpace.single i 1

end OAI.CKSSurfaceVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSurfaceVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

abbrev Metric := ContinuousRiemannianMetric OAI.CKSSurfaceVolume.E (fun x : M => TangentSpace OAI.CKSSurfaceVolume.I x)

end OAI.CKSSurfaceVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSurfaceVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

local instance real_continuousAdd : ContinuousAdd ℝ := inferInstance

local instance real_continuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance

local instance real_smulCommClass :
    @SMulCommClass ℝ ℝ ℝ Algebra.toSMul
      (@instSMulOfMul ℝ (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ (@CommSemiring.toSemiring ℝ Real.instCommSemiring)))) :=
  inferInstance

end OAI.CKSSurfaceVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSurfaceVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def chartFrame (x : M) (y : OAI.CKSSurfaceVolume.E) : OAI.CKSSurfaceVolume.E →L[ℝ] TangentSpace OAI.CKSSurfaceVolume.I ((extChartAt OAI.CKSSurfaceVolume.I x).symm y) :=
  mfderivWithin 𝓘(ℝ,OAI.CKSSurfaceVolume.E) OAI.CKSSurfaceVolume.I (extChartAt OAI.CKSSurfaceVolume.I x).symm (range OAI.CKSSurfaceVolume.I) y

def chartMatrix (g : OAI.CKSSurfaceVolume.Metric (M := M)) (x : M) (y : OAI.CKSSurfaceVolume.E) : Matrix (Fin 2) (Fin 2) ℝ :=
  letI := OAI.CKSSurfaceVolume.real_continuousAdd
  letI := OAI.CKSSurfaceVolume.real_continuousConstSMul
  letI := OAI.CKSSurfaceVolume.real_smulCommClass
  let inner : TangentSpace OAI.CKSSurfaceVolume.I ((extChartAt OAI.CKSSurfaceVolume.I x).symm y) →L[ℝ]
      TangentSpace OAI.CKSSurfaceVolume.I ((extChartAt OAI.CKSSurfaceVolume.I x).symm y) →L[ℝ] ℝ :=
    g.inner ((extChartAt OAI.CKSSurfaceVolume.I x).symm y)
  fun i j => inner (OAI.CKSSurfaceVolume.chartFrame x y (OAI.CKSSurfaceVolume.basis i))
    (OAI.CKSSurfaceVolume.chartFrame x y (OAI.CKSSurfaceVolume.basis j))

def chartDensity (g : OAI.CKSSurfaceVolume.Metric (M := M)) (x : M) (y : OAI.CKSSurfaceVolume.E) : ℝ :=
  Real.sqrt (OAI.CKSSurfaceVolume.chartMatrix g x y).det

end OAI.CKSSurfaceVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSurfaceVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable [MeasurableSpace M] [BorelSpace M]

def localVolume (g : OAI.CKSSurfaceVolume.Metric (M := M)) (x : M) : Measure M :=
  Measure.map (extChartAt OAI.CKSSurfaceVolume.I x).symm
    ((volume.restrict (extChartAt OAI.CKSSurfaceVolume.I x).target).withDensity
      (fun y => ENNReal.ofReal (OAI.CKSSurfaceVolume.chartDensity g x y)))

def IsVolume (g : OAI.CKSSurfaceVolume.Metric (M := M)) (ν : Measure M) : Prop :=
  ∀ x : M, ν.restrict (extChartAt OAI.CKSSurfaceVolume.I x).source = OAI.CKSSurfaceVolume.localVolume g x

end OAI.CKSSurfaceVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSurfaceVolume
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal

def riemannianVolume {M : Type u_1} [TopologicalSpace M] [ChartedSpace OAI.CKSSurfaceVolume.H M]
    [IsManifold OAI.CKSSurfaceVolume.I 1 M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (g : OAI.CKSSurfaceVolume.Metric (M := M)) : Measure M :=
  Classical.epsilon (fun ν => OAI.CKSSurfaceVolume.IsVolume g ν)

end OAI.CKSSurfaceVolume
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology

abbrev E2 := EuclideanSpace ℝ (Fin 2)

abbrev I2 := 𝓘(ℝ,OAI.CKSInducedArea.E2)

abbrev E3 := EuclideanSpace ℝ (Fin 3)

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]

local instance real_continuousAdd : ContinuousAdd ℝ := inferInstance

local instance real_continuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance

local instance real_id_isometric : RingHomIsometric (RingHom.id ℝ) := inferInstance

local instance real_id_compTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance

local instance real_smulCommClass :
    @SMulCommClass ℝ ℝ ℝ Algebra.toSMul
      (@instSMulOfMul ℝ (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ (@CommSemiring.toSemiring ℝ Real.instCommSemiring)))) :=
  inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type u_3} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric


abbrev Inner2 :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  ∀ x : S, TangentSpace OAI.CKSInducedArea.I2 x →L[ℝ] TangentSpace OAI.CKSInducedArea.I2 x →L[ℝ] ℝ

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type u_1} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type u_2} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric


abbrev Smooth3 := ContMDiffRiemannianMetric I3 ∞ OAI.CKSInducedArea.E3 (fun x : N => TangentSpace I3 x)

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric


abbrev Bil2 :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  OAI.CKSInducedArea.E2 →L[ℝ] OAI.CKSInducedArea.E2 →L[ℝ] ℝ

abbrev Bil3 :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  OAI.CKSInducedArea.E3 →L[ℝ] OAI.CKSInducedArea.E3 →L[ℝ] ℝ

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type u_1} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type u_2} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type u_3} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric


def inducedInner (g : OAI.CKSInducedArea.Smooth3 (I3 := I3) (N := N)) (φ : S → N) : OAI.CKSInducedArea.Inner2 (S := S) :=
  letI := OAI.CKSInducedArea.real_id_isometric
  letI := OAI.CKSInducedArea.real_id_compTriple
  fun x => by
    let : NormedAddCommGroup (TangentSpace OAI.CKSInducedArea.I2 x) := by unfold TangentSpace; infer_instance
    let : NormedSpace ℝ (TangentSpace OAI.CKSInducedArea.I2 x) := by unfold TangentSpace; infer_instance
    let : NormedAddCommGroup (TangentSpace I3 (φ x)) := by unfold TangentSpace; infer_instance
    let : NormedSpace ℝ (TangentSpace I3 (φ x)) := by unfold TangentSpace; infer_instance
    exact (g.inner (φ x)).bilinearComp (mfderiv OAI.CKSInducedArea.I2 I3 φ x) (mfderiv OAI.CKSInducedArea.I2 I3 φ x)

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type u_4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_5} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_6} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local instance tangent_manifold_one : IsManifold I 1 M := inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type u_4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_5} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_6} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one


local instance tangent_vectorBundle : VectorBundle ℝ E (fun x : M => TangentSpace I x) :=
  inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one
attribute [local instance] tangent_vectorBundle


local instance scalar_smulCommClass : SMulCommClass ℝ ℝ ℝ := inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_6} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one
attribute [local instance] tangent_vectorBundle
attribute [local instance] scalar_smulCommClass


local instance scalar_vectorBundle : VectorBundle ℝ ℝ (Bundle.Trivial M ℝ) := inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one
attribute [local instance] tangent_vectorBundle
attribute [local instance] scalar_smulCommClass
attribute [local instance] scalar_vectorBundle


local instance scalar_continuousSMul : ContinuousSMul ℝ ℝ := inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type u_4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_5} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_6} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one
attribute [local instance] tangent_vectorBundle
attribute [local instance] scalar_smulCommClass
attribute [local instance] scalar_vectorBundle
attribute [local instance] scalar_continuousSMul


local instance covector_vectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type u_4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_5} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_6} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one
attribute [local instance] tangent_vectorBundle
attribute [local instance] scalar_smulCommClass
attribute [local instance] scalar_vectorBundle
attribute [local instance] scalar_continuousSMul
attribute [local instance] covector_vectorBundle


local instance covector_topologicalAddGroup (x : M) :
    IsTopologicalAddGroup (TangentSpace I x →L[ℝ] ℝ) := inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type u_4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_5} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_6} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one
attribute [local instance] tangent_vectorBundle
attribute [local instance] scalar_smulCommClass
attribute [local instance] scalar_vectorBundle
attribute [local instance] scalar_continuousSMul
attribute [local instance] covector_vectorBundle
attribute [local instance] covector_topologicalAddGroup


local instance covector_continuousSMul (x : M) :
    ContinuousSMul ℝ (TangentSpace I x →L[ℝ] ℝ) := inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_6} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one
attribute [local instance] tangent_vectorBundle
attribute [local instance] scalar_smulCommClass
attribute [local instance] scalar_vectorBundle
attribute [local instance] scalar_continuousSMul
attribute [local instance] covector_vectorBundle
attribute [local instance] covector_topologicalAddGroup
attribute [local instance] covector_continuousSMul


local instance scalarAtlas : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℝ) := ⟨rfl⟩

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type u_4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_5} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_6} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one
attribute [local instance] tangent_vectorBundle
attribute [local instance] scalar_smulCommClass
attribute [local instance] scalar_vectorBundle
attribute [local instance] scalar_continuousSMul
attribute [local instance] covector_vectorBundle
attribute [local instance] covector_topologicalAddGroup
attribute [local instance] covector_continuousSMul
attribute [local instance] OAI.CKSInducedArea.scalarAtlas


local instance covector_atlas (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] :
    MemTrivializationAtlas
      (e.continuousLinearMap (RingHom.id ℝ) (Bundle.Trivial.trivialization M ℝ)) :=
  inferInstance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
variable {E : Type u_4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_5} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u_6} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] tangent_manifold_one
attribute [local instance] tangent_vectorBundle
attribute [local instance] scalar_smulCommClass
attribute [local instance] scalar_vectorBundle
attribute [local instance] scalar_continuousSMul
attribute [local instance] covector_vectorBundle
attribute [local instance] covector_topologicalAddGroup
attribute [local instance] covector_continuousSMul
attribute [local instance] OAI.CKSInducedArea.scalarAtlas
attribute [local instance] covector_atlas


def bilinearTriv (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] :
    Trivialization (E →L[ℝ] E →L[ℝ] ℝ) (π (E →L[ℝ] E →L[ℝ] ℝ) (fun x : M =>
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  e.continuousLinearMap (RingHom.id ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Bundle.Trivial.trivialization M ℝ))

instance bilinearTriv_atlas (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] : MemTrivializationAtlas (OAI.CKSInducedArea.bilinearTriv I e) := by
  unfold OAI.CKSInducedArea.bilinearTriv
  infer_instance

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric


local instance covector_smulCommClass {Space : Type u_4} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] :
    letI := OAI.CKSInducedArea.real_smulCommClass
    SMulCommClass ℝ ℝ (Space →L[ℝ] ℝ) := by
  infer_instance

local instance bilNorm2 : NormedAddCommGroup OAI.CKSInducedArea.Bil2 :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  ContinuousLinearMap.toNormedAddCommGroup (E := OAI.CKSInducedArea.E2) (F := OAI.CKSInducedArea.E2 →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
attribute [local instance] OAI.CKSInducedArea.bilNorm2


local instance bilSpace2 : NormedSpace ℝ OAI.CKSInducedArea.Bil2 :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  letI := OAI.CKSInducedArea.covector_smulCommClass (Space := OAI.CKSInducedArea.E2)
  ContinuousLinearMap.toNormedSpace

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
attribute [local instance] OAI.CKSInducedArea.bilNorm2
attribute [local instance] OAI.CKSInducedArea.bilSpace2


local instance bilNorm3 : NormedAddCommGroup OAI.CKSInducedArea.Bil3 :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  ContinuousLinearMap.toNormedAddCommGroup (E := OAI.CKSInducedArea.E3) (F := OAI.CKSInducedArea.E3 →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
attribute [local instance] OAI.CKSInducedArea.bilNorm2
attribute [local instance] OAI.CKSInducedArea.bilSpace2
attribute [local instance] OAI.CKSInducedArea.bilNorm3


local instance bilSpace3 : NormedSpace ℝ OAI.CKSInducedArea.Bil3 :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  letI := OAI.CKSInducedArea.covector_smulCommClass (Space := OAI.CKSInducedArea.E3)
  ContinuousLinearMap.toNormedSpace

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
attribute [local instance] OAI.CKSInducedArea.bilNorm2
attribute [local instance] OAI.CKSInducedArea.bilSpace2
attribute [local instance] OAI.CKSInducedArea.bilNorm3
attribute [local instance] OAI.CKSInducedArea.bilSpace3


local instance mixNorm23 : NormedAddCommGroup (OAI.CKSInducedArea.E2 →L[ℝ] OAI.CKSInducedArea.E3 →L[ℝ] ℝ) :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  ContinuousLinearMap.toNormedAddCommGroup (E := OAI.CKSInducedArea.E2) (F := OAI.CKSInducedArea.E3 →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
attribute [local instance] OAI.CKSInducedArea.bilNorm2
attribute [local instance] OAI.CKSInducedArea.bilSpace2
attribute [local instance] OAI.CKSInducedArea.bilNorm3
attribute [local instance] OAI.CKSInducedArea.bilSpace3
attribute [local instance] OAI.CKSInducedArea.mixNorm23


local instance mixSpace23 : NormedSpace ℝ (OAI.CKSInducedArea.E2 →L[ℝ] OAI.CKSInducedArea.E3 →L[ℝ] ℝ) :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  letI := OAI.CKSInducedArea.covector_smulCommClass (Space := OAI.CKSInducedArea.E3)
  ContinuousLinearMap.toNormedSpace

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
attribute [local instance] OAI.CKSInducedArea.bilNorm2
attribute [local instance] OAI.CKSInducedArea.bilSpace2
attribute [local instance] OAI.CKSInducedArea.bilNorm3
attribute [local instance] OAI.CKSInducedArea.bilSpace3
attribute [local instance] OAI.CKSInducedArea.mixNorm23
attribute [local instance] OAI.CKSInducedArea.mixSpace23


local instance mixNorm32 : NormedAddCommGroup (OAI.CKSInducedArea.E3 →L[ℝ] OAI.CKSInducedArea.E2 →L[ℝ] ℝ) :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  ContinuousLinearMap.toNormedAddCommGroup (E := OAI.CKSInducedArea.E3) (F := OAI.CKSInducedArea.E2 →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
attribute [local instance] OAI.CKSInducedArea.bilNorm2
attribute [local instance] OAI.CKSInducedArea.bilSpace2
attribute [local instance] OAI.CKSInducedArea.bilNorm3
attribute [local instance] OAI.CKSInducedArea.bilSpace3
attribute [local instance] OAI.CKSInducedArea.mixNorm23
attribute [local instance] OAI.CKSInducedArea.mixSpace23
attribute [local instance] OAI.CKSInducedArea.mixNorm32


local instance mixSpace32 : NormedSpace ℝ (OAI.CKSInducedArea.E3 →L[ℝ] OAI.CKSInducedArea.E2 →L[ℝ] ℝ) :=
  letI := OAI.CKSInducedArea.real_smulCommClass
  letI := OAI.CKSInducedArea.covector_smulCommClass (Space := OAI.CKSInducedArea.E2)
  ContinuousLinearMap.toNormedSpace

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSInducedArea
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {H3 : Type u_1} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type u_2} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type u_3} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass real_id_isometric
attribute [local instance] OAI.CKSInducedArea.bilNorm2
attribute [local instance] OAI.CKSInducedArea.bilSpace2
attribute [local instance] OAI.CKSInducedArea.bilNorm3
attribute [local instance] OAI.CKSInducedArea.bilSpace3
attribute [local instance] OAI.CKSInducedArea.mixNorm23
attribute [local instance] OAI.CKSInducedArea.mixSpace23
attribute [local instance] OAI.CKSInducedArea.mixNorm32
attribute [local instance] OAI.CKSInducedArea.mixSpace32


def inducedMetric (g : OAI.CKSInducedArea.Smooth3 (I3 := I3) (N := N)) (φ : S → N)
    (hφ : ContMDiff OAI.CKSInducedArea.I2 I3 ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv OAI.CKSInducedArea.I2 I3 φ x)) :
    ContMDiffRiemannianMetric OAI.CKSInducedArea.I2 ∞ OAI.CKSInducedArea.E2 (fun x : S => TangentSpace OAI.CKSInducedArea.I2 x) :=
  have proof_inducedInner_symm_37 {H3 : Type u_1} [instLocal1 : TopologicalSpace.{u_1} H3] {I3 : ModelWithCorners.{0, 0, u_1} ℝ OAI.CKSInducedArea.E3 H3} {N : Type u_2} [instLocal4 : TopologicalSpace.{u_2} N] [instLocal5 : ChartedSpace.{u_1, u_2} H3 N] [instLocal6 : IsManifold.{0, 0, u_1, u_2} I3 (∞ : ℕ∞ω) N] {S : Type u_3} [instLocal8 : TopologicalSpace.{u_3} S] [instLocal9 : ChartedSpace.{0, u_3} OAI.CKSInducedArea.E2 S]  (metric : OAI.CKSInducedArea.Smooth3 (I3 := I3) (N := N)) (immersion : S → N)
      (point : S) (left right : TangentSpace OAI.CKSInducedArea.I2 point) :
      OAI.CKSInducedArea.inducedInner metric immersion point left right = OAI.CKSInducedArea.inducedInner metric immersion point right left :=
    metric.symm (immersion point) _ _
  have proof_inducedInner_pos_38 {H3 : Type u_1} [instLocal1 : TopologicalSpace.{u_1} H3] {I3 : ModelWithCorners.{0, 0, u_1} ℝ OAI.CKSInducedArea.E3 H3} {N : Type u_2} [instLocal4 : TopologicalSpace.{u_2} N] [instLocal5 : ChartedSpace.{u_1, u_2} H3 N] [instLocal6 : IsManifold.{0, 0, u_1, u_2} I3 (∞ : ℕ∞ω) N] {S : Type u_3} [instLocal8 : TopologicalSpace.{u_3} S] [instLocal9 : ChartedSpace.{0, u_3} OAI.CKSInducedArea.E2 S]  (metric : OAI.CKSInducedArea.Smooth3 (I3 := I3) (N := N)) (immersion : S → N)
      (injective : ∀ point, Function.Injective (mfderiv OAI.CKSInducedArea.I2 I3 immersion point))
      (point : S) (vector : TangentSpace OAI.CKSInducedArea.I2 point) (nonzero : vector ≠ 0) :
      0 < OAI.CKSInducedArea.inducedInner metric immersion point vector vector :=
    metric.pos (immersion point) _
      (fun zero => nonzero (injective point (zero.trans (map_zero _).symm)))
  have proof_positive_bilinear_bounded_41  (B : OAI.CKSInducedArea.Bil2) (hB : ∀ v : OAI.CKSInducedArea.E2, v ≠ 0 → 0 < B v v) :
      IsVonNBounded ℝ {v : OAI.CKSInducedArea.E2 | B v v < 1} := by
    have hc : Continuous (fun v : OAI.CKSInducedArea.E2 => B v v) := B.continuous.clm_apply continuous_id
    obtain ⟨a,ha,hm⟩ := (isCompact_sphere (0 : OAI.CKSInducedArea.E2) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.continuousOn
    have haNorm : ‖a‖ = 1 := by simpa [Metric.mem_sphere] using ha
    have ha0 : a ≠ 0 := by intro h; simp [h] at haNorm
    have hp : 0 < B a a := hB a ha0
    have hlow : ∀ v : OAI.CKSInducedArea.E2, B a a * ‖v‖ ^ 2 ≤ B v v := by
      intro v
      by_cases hv : v = 0
      · simp [hv]
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hy : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
      have h := hm (show (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : OAI.CKSInducedArea.E2) 1 by
        simpa [Metric.mem_sphere] using hy)
      have he : B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) = B v v / ‖v‖^2 := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        field_simp
      change B a a ≤ B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) at h
      rw [he] at h
      exact (le_div_iff₀ (sq_pos_of_pos hn)).mp h
    apply (NormedSpace.isVonNBounded_iff ℝ).mpr
    apply (Metric.isBounded_iff_subset_ball (0 : OAI.CKSInducedArea.E2)).mpr
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
  have proof_inducedInner_bounded_39 {H3 : Type u_1} [instLocal1 : TopologicalSpace.{u_1} H3] {I3 : ModelWithCorners.{0, 0, u_1} ℝ OAI.CKSInducedArea.E3 H3} {N : Type u_2} [instLocal4 : TopologicalSpace.{u_2} N] [instLocal5 : ChartedSpace.{u_1, u_2} H3 N] [instLocal6 : IsManifold.{0, 0, u_1, u_2} I3 (∞ : ℕ∞ω) N] {S : Type u_3} [instLocal8 : TopologicalSpace.{u_3} S] [instLocal9 : ChartedSpace.{0, u_3} OAI.CKSInducedArea.E2 S]  (metric : OAI.CKSInducedArea.Smooth3 (I3 := I3) (N := N)) (immersion : S → N)
      (injective : ∀ point, Function.Injective (mfderiv OAI.CKSInducedArea.I2 I3 immersion point)) (point : S) :
      IsVonNBounded ℝ {vector : TangentSpace OAI.CKSInducedArea.I2 point |
        inducedInner metric immersion point vector vector < 1} :=
    proof_positive_bilinear_bounded_41 (OAI.CKSInducedArea.inducedInner metric immersion point)
      (proof_inducedInner_pos_38 metric immersion injective point)
  have proof_bilinearComp_smoothAt_42 {S : Type u_3} [instLocal1 : TopologicalSpace.{u_3} S] [instLocal2 : ChartedSpace.{0, u_3} OAI.CKSInducedArea.E2 S] [instLocal3 : IsManifold.{0, 0, 0, u_3} OAI.CKSInducedArea.I2 (∞ : ℕ∞ω) S]  [IsManifold OAI.CKSInducedArea.I2 ∞ S]
      {B : S → OAI.CKSInducedArea.Bil3} {A : S → OAI.CKSInducedArea.E2 →L[ℝ] OAI.CKSInducedArea.E3} {x : S}
      (hB : ContMDiffAt OAI.CKSInducedArea.I2 𝓘(ℝ,OAI.CKSInducedArea.Bil3) ∞ B x)
      (hA : ContMDiffAt OAI.CKSInducedArea.I2 𝓘(ℝ,OAI.CKSInducedArea.E2 →L[ℝ] OAI.CKSInducedArea.E3) ∞ A x) :
      ContMDiffAt OAI.CKSInducedArea.I2 𝓘(ℝ,OAI.CKSInducedArea.Bil2) ∞ (fun y => (B y).bilinearComp (A y) (A y)) x := by
    have flip1 : ContDiff ℝ ∞ (fun B : OAI.CKSInducedArea.E2 →L[ℝ] OAI.CKSInducedArea.E3 →L[ℝ] ℝ => B.flip) :=
      by
        let L : (OAI.CKSInducedArea.E2 →L[ℝ] OAI.CKSInducedArea.E3 →L[ℝ] ℝ) →L[ℝ] (OAI.CKSInducedArea.E3 →L[ℝ] OAI.CKSInducedArea.E2 →L[ℝ] ℝ) :=
          (ContinuousLinearMap.flipₗᵢ ℝ OAI.CKSInducedArea.E2 OAI.CKSInducedArea.E3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap
        exact L.contDiff
    have flip2 : ContDiff ℝ ∞ (fun B : OAI.CKSInducedArea.Bil2 => B.flip) :=
      by
        let L : OAI.CKSInducedArea.Bil2 →L[ℝ] OAI.CKSInducedArea.Bil2 :=
          (ContinuousLinearMap.flipₗᵢ ℝ OAI.CKSInducedArea.E2 OAI.CKSInducedArea.E2 ℝ).toContinuousLinearEquiv.toContinuousLinearMap
        exact L.contDiff
    exact flip2.comp_contMDiffAt ((flip1.comp_contMDiffAt (hB.clm_comp hA)).clm_comp hA)
  have proof_bilinearTriv_pair_43 {E : Type 0} [instLocal1 : NormedAddCommGroup.{0} E] [instLocal2 : NormedSpace.{0, 0} ℝ E] {H : Type 0} [instLocal4 : TopologicalSpace.{0} H] (I : ModelWithCorners.{0, 0, 0} ℝ E H) {M : Type u_3} [instLocal7 : TopologicalSpace.{u_3} M] [instLocal8 : ChartedSpace.{0, u_3} H M] [instLocal9 : IsManifold.{0, 0, 0, u_3} I (∞ : ℕ∞ω) M]  (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
      [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet)
      (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
      ((OAI.CKSInducedArea.bilinearTriv I e) ⟨x,B⟩).2 v w = B (e.symmL ℝ x v) (e.symmL ℝ x w) := by
    let := OAI.CKSInducedArea.scalarAtlas (M := M)
    unfold OAI.CKSInducedArea.bilinearTriv
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
  have proof_bilinearTriv_pair_44 {E : Type 0} [instLocal1 : NormedAddCommGroup.{0} E] [instLocal2 : NormedSpace.{0, 0} ℝ E] {H : Type u_1} [instLocal4 : TopologicalSpace.{u_1} H] (I : ModelWithCorners.{0, 0, u_1} ℝ E H) {M : Type u_2} [instLocal7 : TopologicalSpace.{u_2} M] [instLocal8 : ChartedSpace.{u_1, u_2} H M] [instLocal9 : IsManifold.{0, 0, u_1, u_2} I (∞ : ℕ∞ω) M]  (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
      [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet)
      (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
      ((OAI.CKSInducedArea.bilinearTriv I e) ⟨x,B⟩).2 v w = B (e.symmL ℝ x v) (e.symmL ℝ x w) := by
    let := OAI.CKSInducedArea.scalarAtlas (M := M)
    unfold OAI.CKSInducedArea.bilinearTriv
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
  have proof_inducedInner_smooth_40 {H3 : Type u_1} [instLocal1 : TopologicalSpace.{u_1} H3] {I3 : ModelWithCorners.{0, 0, u_1} ℝ OAI.CKSInducedArea.E3 H3} {N : Type u_2} [instLocal4 : TopologicalSpace.{u_2} N] [instLocal5 : ChartedSpace.{u_1, u_2} H3 N] [instLocal6 : IsManifold.{0, 0, u_1, u_2} I3 (∞ : ℕ∞ω) N] {S : Type u_3} [instLocal8 : TopologicalSpace.{u_3} S] [instLocal9 : ChartedSpace.{0, u_3} OAI.CKSInducedArea.E2 S] [instLocal10 : IsManifold.{0, 0, 0, u_3} OAI.CKSInducedArea.I2 (∞ : ℕ∞ω) S]  (g : OAI.CKSInducedArea.Smooth3 (I3 := I3) (N := N)) {φ : S → N}
      (hφ : ContMDiff OAI.CKSInducedArea.I2 I3 ∞ φ) :
      ContMDiff OAI.CKSInducedArea.I2 (OAI.CKSInducedArea.I2.prod 𝓘(ℝ,OAI.CKSInducedArea.Bil2)) ∞
        (fun x => TotalSpace.mk' OAI.CKSInducedArea.Bil2 x (OAI.CKSInducedArea.inducedInner g φ x)) := by
    let := OAI.CKSInducedArea.real_id_isometric
    let := OAI.CKSInducedArea.real_smulCommClass
    intro x
    let e := trivializationAt OAI.CKSInducedArea.E2 (TangentSpace OAI.CKSInducedArea.I2) x
    let e' := trivializationAt OAI.CKSInducedArea.E3 (TangentSpace I3) (φ x)
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt OAI.CKSInducedArea.E2 (TangentSpace OAI.CKSInducedArea.I2) x
    have hx' : φ x ∈ e'.baseSet := mem_baseSet_trivializationAt OAI.CKSInducedArea.E3 (TangentSpace I3) (φ x)
    apply (contMDiffAt_section (𝕜 := ℝ) (B := S)
      (E := fun z : S => TangentSpace OAI.CKSInducedArea.I2 z →L[ℝ] TangentSpace OAI.CKSInducedArea.I2 z →L[ℝ] ℝ)
      (IB := OAI.CKSInducedArea.I2) (n := ∞) (F := OAI.CKSInducedArea.Bil2)
      (s := OAI.CKSInducedArea.inducedInner g φ) x).mpr
    change ContMDiffAt OAI.CKSInducedArea.I2 𝓘(ℝ,OAI.CKSInducedArea.Bil2) ∞
      (fun y : S => ((OAI.CKSInducedArea.bilinearTriv OAI.CKSInducedArea.I2 e)
        ⟨y, OAI.CKSInducedArea.inducedInner g φ y⟩).2) x
    have hB := (contMDiffAt_section (𝕜 := ℝ) (B := N)
      (E := fun z : N => TangentSpace I3 z →L[ℝ] TangentSpace I3 z →L[ℝ] ℝ)
      (IB := I3) (n := ∞) (F := OAI.CKSInducedArea.Bil3) (s := g.inner) (φ x)).mp (g.contMDiff (φ x))
    change ContMDiffAt I3 𝓘(ℝ,OAI.CKSInducedArea.Bil3) ∞
      (fun y : N => ((OAI.CKSInducedArea.bilinearTriv I3 e') ⟨y, g.inner y⟩).2) (φ x) at hB
    have hD := (hφ x).mfderiv_const (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp [*])
    apply (proof_bilinearComp_smoothAt_42 (hB.comp x (hφ x)) hD).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx,
      hφ.continuous.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds hx')] with y hy hy'
    ext v w
    rw [proof_bilinearTriv_pair_43 OAI.CKSInducedArea.I2 e hy]
    rw [ContinuousLinearMap.bilinearComp_apply]
    dsimp only [Function.comp_apply]
    rw [proof_bilinearTriv_pair_44 I3 e' hy']
    dsimp [OAI.CKSInducedArea.inducedInner,inTangentCoordinates,ContinuousLinearMap.inCoordinates]
    rw [e'.symmL_continuousLinearMapAt hy', e'.symmL_continuousLinearMapAt hy']
    rfl
  {
    inner := OAI.CKSInducedArea.inducedInner g φ
    symm := proof_inducedInner_symm_37 g φ
    pos := proof_inducedInner_pos_38 g φ hinj
    isVonNBounded := proof_inducedInner_bounded_39 g φ hinj
    contMDiff := proof_inducedInner_smooth_40 g hφ
  }

end OAI.CKSInducedArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSEmbeddingDerivative
open Set Manifold Bundle Filter Function
open scoped ContDiff Topology

abbrev E := EuclideanSpace ℝ (Fin 3)

local instance halfSpaceDimension_neZero : NeZero (3 : ℕ) := inferInstance

abbrev H := @EuclideanHalfSpace 3 OAI.CKSEmbeddingDerivative.halfSpaceDimension_neZero

abbrev I := @modelWithCornersEuclideanHalfSpace 3 OAI.CKSEmbeddingDerivative.halfSpaceDimension_neZero

end OAI.CKSEmbeddingDerivative
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSFullCutArea
open Set Manifold Bundle Function
open scoped ContDiff Topology
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N]

instance domainTopology (D : OAI.CKSGeometricCuts.OuterDomain N) : TopologicalSpace D.Carrier := D.topology

instance domainCharts (D : OAI.CKSGeometricCuts.OuterDomain N) : ChartedSpace OAI.CKSBoundarySurface.H3 D.Carrier := D.charts

instance domainSmooth (D : OAI.CKSGeometricCuts.OuterDomain N) : IsManifold OAI.CKSBoundarySurface.I3 ∞ D.Carrier := D.smooth

abbrev Surface (D : OAI.CKSGeometricCuts.OuterDomain N) := OAI.CKSBoundarySurface.Boundary D.Carrier

def cutInclusion (D : OAI.CKSGeometricCuts.OuterDomain N) : OAI.CKSFullCutArea.Surface D → N := D.inclusion ∘ Subtype.val

end OAI.CKSFullCutArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSFullCutArea
open Set Manifold Bundle Function
open scoped ContDiff Topology
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N]
variable [@IsManifold ℝ _ E3 _ _ H3
  (@instTopologicalSpaceEuclideanHalfSpace 3 CKSBoundarySurface.halfSpaceDimension_neZero) I3 ∞ N _ _]

instance domainSecondCountable [SecondCountableTopology N] (D : OAI.CKSGeometricCuts.OuterDomain N) :
    SecondCountableTopology D.Carrier := D.embedding.isEmbedding.secondCountableTopology

abbrev SmoothMetric :=
  letI := OAI.CKSBoundarySurface.halfSpaceDimension_neZero
  letI := OAI.CKSInducedArea.tangent_vectorBundle OAI.CKSBoundarySurface.I3 (M := N)
  ContMDiffRiemannianMetric OAI.CKSBoundarySurface.I3 ∞ OAI.CKSBoundarySurface.E3 (fun x : N => TangentSpace OAI.CKSBoundarySurface.I3 x)

def cutMetric (g : OAI.CKSFullCutArea.SmoothMetric (N := N)) (D : OAI.CKSGeometricCuts.OuterDomain N) :
    ContMDiffRiemannianMetric OAI.CKSBoundarySurface.I2 ∞ OAI.CKSBoundarySurface.E2 (fun x : OAI.CKSFullCutArea.Surface D => TangentSpace OAI.CKSBoundarySurface.I2 x) :=
  have proof_boundary_chart_zero_49 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSIntrinsicGeometry.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSIntrinsicGeometry.I3 1 M]  (x y : M) (hy : y ∈ (extChartAt OAI.CKSIntrinsicGeometry.I3 x).source)
      (hS : y ∈ OAI.CKSIntrinsicGeometry.I3.boundary M) : (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 = 0 := by
    have hychart : y ∈ (chartAt OAI.CKSIntrinsicGeometry.H3 x).source := by simpa using hy
    have hyrange : extChartAt OAI.CKSIntrinsicGeometry.I3 x y ∈ range OAI.CKSIntrinsicGeometry.I3 :=
      (extChartAt_target_subset_range x) ((extChartAt OAI.CKSIntrinsicGeometry.I3 x).map_source hy)
    have hnonneg : 0 ≤ (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 := by
      simpa only [OAI.CKSIntrinsicGeometry.I3, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hyrange
    have hnot : ¬OAI.CKSIntrinsicGeometry.I3.IsInteriorPoint y :=
      (OAI.CKSIntrinsicGeometry.I3.isBoundaryPoint_iff_not_isInteriorPoint y).mp hS
    have hle : (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 ≤ 0 := by
      by_contra h
      have hpos : 0 < (extChartAt OAI.CKSIntrinsicGeometry.I3 x y) 0 := lt_of_not_ge h
      have hint : extChartAt OAI.CKSIntrinsicGeometry.I3 x y ∈ interior (range OAI.CKSIntrinsicGeometry.I3) := by
        simpa only [OAI.CKSIntrinsicGeometry.I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hpos
      apply hnot
      apply (OAI.CKSIntrinsicGeometry.I3.isInteriorPoint_iff_of_mem_atlas one_ne_zero (chart_mem_atlas OAI.CKSIntrinsicGeometry.H3 x) hychart).mpr
      exact (chartAt OAI.CKSIntrinsicGeometry.H3 x).mem_interior_extend_target ((chartAt OAI.CKSIntrinsicGeometry.H3 x).map_source hychart) hint
    exact le_antisymm hle hnonneg
  have proof_liftPlane_zero_6  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.liftPlane z 0 = 0 := rfl
  have proof_liftPlane_succ_7  (z : OAI.CKSBoundarySurface.E2) (i : Fin 2) : OAI.CKSBoundarySurface.liftPlane z i.succ = z i := rfl
  have proof_I3_liftHalf_23  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.I3 (OAI.CKSBoundarySurface.liftHalf z) = OAI.CKSBoundarySurface.liftPlane z := rfl
  have proof_boundary_iff_zero_50 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x y : M) (hy : y ∈ (chartAt OAI.CKSBoundarySurface.H3 x).source) :
      y ∈ OAI.CKSBoundarySurface.I3.boundary M ↔ (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x y)) 0 = 0 := by
    constructor
    · exact proof_boundary_chart_zero_49 x y (by simp [*])
    · intro hz
      apply (OAI.CKSBoundarySurface.I3.isBoundaryPoint_iff_not_isInteriorPoint y).mpr
      intro hi
      have hin := (OAI.CKSBoundarySurface.I3.isInteriorPoint_iff_of_mem_atlas
        (by simp [*] : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas OAI.CKSBoundarySurface.H3 x) hy).mp hi
      have hr := (chartAt OAI.CKSBoundarySurface.H3 x).interior_extend_target_subset_interior_range hin
      have hp : 0 < (OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x y)) 0 := by
        simpa only [OAI.CKSBoundarySurface.I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
          OpenPartialHomeomorph.extend_coe, Function.comp_apply] using hr
      rw [hz] at hp
      exact (lt_irrefl 0) hp
  have proof_chart_inverse_boundary_51 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x).target) :
      (chartAt OAI.CKSBoundarySurface.H3 x).symm (OAI.CKSBoundarySurface.liftHalf z) ∈ OAI.CKSBoundarySurface.I3.boundary M := by
    apply (proof_boundary_iff_zero_50 x _ ((chartAt OAI.CKSBoundarySurface.H3 x).map_target hz)).mpr
    rw [(chartAt OAI.CKSBoundarySurface.H3 x).right_inv hz]
    rfl
  have proof_boundaryInverse_mem_52 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).target) :
      (chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z) ∈ OAI.CKSBoundarySurface.Boundary M :=
    proof_chart_inverse_boundary_51 x.val hz
  have proof_boundaryInverse_val_53 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2}
      (hz : OAI.CKSBoundarySurface.liftHalf z ∈ (chartAt OAI.CKSBoundarySurface.H3 x.val).target) :
      (OAI.CKSBoundarySurface.boundaryInverse x z).val = (chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z) := by
    simp only [OAI.CKSBoundarySurface.boundaryInverse,dite_eq_left hz]
  have proof_boundaryChart_symm_val_54 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2} (hz : z ∈ (OAI.CKSBoundarySurface.boundaryChart x).target) :
      ((OAI.CKSBoundarySurface.boundaryChart x).symm z).val = (chartAt OAI.CKSBoundarySurface.H3 x.val).symm (OAI.CKSBoundarySurface.liftHalf z) :=
    proof_boundaryInverse_val_53 x hz
  have proof_inclusion_chart_formula_55 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) {z : OAI.CKSBoundarySurface.E2}
      (hz : z ∈ (OAI.CKSBoundarySurface.boundaryChart x).target) :
      writtenInExtChartAt OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 x (Subtype.val : OAI.CKSBoundarySurface.Boundary M → M) z = OAI.CKSBoundarySurface.liftPlane z := by
    change OAI.CKSBoundarySurface.I3 (chartAt OAI.CKSBoundarySurface.H3 x.val (((OAI.CKSBoundarySurface.boundaryChart x).symm z).val)) = _
    rw [proof_boundaryChart_symm_val_54 x hz, (chartAt OAI.CKSBoundarySurface.H3 x.val).right_inv hz]
    rfl
  have proof_inclusion_chart_eventually_56 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) :
      writtenInExtChartAt OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 x (Subtype.val : OAI.CKSBoundarySurface.Boundary M → M) =ᶠ[𝓝 (extChartAt OAI.CKSBoundarySurface.I2 x x)] OAI.CKSBoundarySurface.liftPlane := by
    have ht : (OAI.CKSBoundarySurface.boundaryChart x).target ∈ 𝓝 (extChartAt OAI.CKSBoundarySurface.I2 x x) :=
      (OAI.CKSBoundarySurface.boundaryChart x).open_target.mem_nhds ((OAI.CKSBoundarySurface.boundaryChart x).map_source (mem_chart_source OAI.CKSBoundarySurface.E2 x))
    filter_upwards [ht] with z hz
    exact proof_inclusion_chart_formula_55 x hz
  have proof_inclusion_smooth_57 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  : ContMDiff OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 ∞ (Subtype.val : OAI.CKSBoundarySurface.Boundary M → M) := by
    intro x
    apply contMDiffAt_iff.mpr
    refine ⟨continuous_subtype_val.continuousAt, ?_⟩
    exact ((OAI.CKSBoundarySurface.liftPlane.contDiff.contDiffAt).congr_of_eventuallyEq (proof_inclusion_chart_eventually_56 x)).contDiffWithinAt
  have proof_cutInclusion_smooth_47 {N : Type u} [instLocal1 : TopologicalSpace.{u} N] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 N] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) N]  [IsManifold OAI.CKSBoundarySurface.I3 ∞ N] (D : OAI.CKSGeometricCuts.OuterDomain N) :
      ContMDiff OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 ∞ (OAI.CKSFullCutArea.cutInclusion D) :=
    D.embedding.isImmersion.contMDiff.comp proof_inclusion_smooth_57
  have proof_extended_chart_derivative_injective_58 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSEmbeddingDerivative.H M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSEmbeddingDerivative.I (∞ : ℕ∞ω) M]  [IsManifold OAI.CKSEmbeddingDerivative.I ∞ M] (e : OpenPartialHomeomorph M OAI.CKSEmbeddingDerivative.H)
      (he : e ∈ IsManifold.maximalAtlas OAI.CKSEmbeddingDerivative.I ∞ M) {x : M} (hx : x ∈ e.source) :
      Injective (mfderiv OAI.CKSEmbeddingDerivative.I 𝓘(ℝ,OAI.CKSEmbeddingDerivative.E) (e.extend OAI.CKSEmbeddingDerivative.I) x) := by
    have hed : e.MDifferentiable OAI.CKSEmbeddingDerivative.I OAI.CKSEmbeddingDerivative.I := ⟨
      (contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
    have hcomp := mfderiv_comp x OAI.CKSEmbeddingDerivative.I.mdifferentiableAt ((hed.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx))
    change mfderiv OAI.CKSEmbeddingDerivative.I 𝓘(ℝ,OAI.CKSEmbeddingDerivative.E) (e.extend OAI.CKSEmbeddingDerivative.I) x = _ at hcomp
    rw [OAI.CKSEmbeddingDerivative.I.hasMFDerivAt.mfderiv] at hcomp
    change mfderiv OAI.CKSEmbeddingDerivative.I 𝓘(ℝ,OAI.CKSEmbeddingDerivative.E) (e.extend OAI.CKSEmbeddingDerivative.I) x = mfderiv OAI.CKSEmbeddingDerivative.I OAI.CKSEmbeddingDerivative.I e x at hcomp
    rw [hcomp]
    exact hed.mfderiv_injective hx
  have proof_immersion_derivative_injective_59 {M : Type u} {N : Type u} [instLocal2 : TopologicalSpace.{u} M] [instLocal3 : ChartedSpace.{0, u} OAI.CKSEmbeddingDerivative.H M] [instLocal4 : IsManifold.{0, 0, 0, u} OAI.CKSEmbeddingDerivative.I (∞ : ℕ∞ω) M] [instLocal5 : TopologicalSpace.{u} N] [instLocal6 : ChartedSpace.{0, u} OAI.CKSEmbeddingDerivative.H N] [instLocal7 : IsManifold.{0, 0, 0, u} OAI.CKSEmbeddingDerivative.I (∞ : ℕ∞ω) N]  [IsManifold OAI.CKSEmbeddingDerivative.I ∞ N] {f : M → N} {x : M}
      (h : IsImmersionAt OAI.CKSEmbeddingDerivative.I OAI.CKSEmbeddingDerivative.I ∞ f x) : Injective (mfderiv OAI.CKSEmbeddingDerivative.I OAI.CKSEmbeddingDerivative.I f x) := by
    let A : OAI.CKSEmbeddingDerivative.E →L[ℝ] OAI.CKSEmbeddingDerivative.E := (ContinuousLinearMap.fst ℝ OAI.CKSEmbeddingDerivative.E h.complement).comp
      h.equiv.symm.toContinuousLinearMap
    let L : N → OAI.CKSEmbeddingDerivative.E := A ∘ (h.codChart.extend OAI.CKSEmbeddingDerivative.I)
    have hL : ContMDiffAt OAI.CKSEmbeddingDerivative.I 𝓘(ℝ,OAI.CKSEmbeddingDerivative.E) ∞ L (f x) :=
      A.contMDiff.contMDiffAt.comp _
        (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas h.mem_codChart_source)
    have heq : (L ∘ f) =ᶠ[𝓝 x] h.domChart.extend OAI.CKSEmbeddingDerivative.I := by
      filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
      have hy' : y ∈ (h.domChart.extend OAI.CKSEmbeddingDerivative.I).source := by simpa only [OpenPartialHomeomorph.extend_source] using hy
      have hw := h.writtenInCharts ((h.domChart.extend OAI.CKSEmbeddingDerivative.I).map_source hy')
      dsimp only [Function.comp_apply] at hw
      rw [(h.domChart.extend OAI.CKSEmbeddingDerivative.I).left_inv hy'] at hw
      change A ((h.codChart.extend OAI.CKSEmbeddingDerivative.I) (f y)) = _
      rw [hw]
      simp only [A,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply ]
      rfl
    have hdL := hL.mdifferentiableAt (by simp)
    have hdf := h.contMDiffAt.mdifferentiableAt (by simp)
    have hder := heq.mfderiv_eq (I := OAI.CKSEmbeddingDerivative.I) (I' := 𝓘(ℝ,OAI.CKSEmbeddingDerivative.E))
    rw [mfderiv_comp x hdL hdf] at hder
    change _ = mfderiv OAI.CKSEmbeddingDerivative.I 𝓘(ℝ,OAI.CKSEmbeddingDerivative.E) (h.domChart.extend OAI.CKSEmbeddingDerivative.I) x at hder
    have hinj := proof_extended_chart_derivative_injective_58 h.domChart h.domChart_mem_maximalAtlas
      h.mem_domChart_source
    rw [← hder] at hinj
    have hi' : Injective ((mfderiv OAI.CKSEmbeddingDerivative.I 𝓘(ℝ,OAI.CKSEmbeddingDerivative.E) L (f x)) ∘ (mfderiv OAI.CKSEmbeddingDerivative.I OAI.CKSEmbeddingDerivative.I f x)) := hinj
    exact hi'.of_comp
  have proof_smooth_embedding_derivative_injective_60 {M : Type u} {N : Type u} [instLocal2 : TopologicalSpace.{u} M] [instLocal3 : ChartedSpace.{0, u} OAI.CKSEmbeddingDerivative.H M] [instLocal4 : IsManifold.{0, 0, 0, u} OAI.CKSEmbeddingDerivative.I (∞ : ℕ∞ω) M] [instLocal5 : TopologicalSpace.{u} N] [instLocal6 : ChartedSpace.{0, u} OAI.CKSEmbeddingDerivative.H N] [instLocal7 : IsManifold.{0, 0, 0, u} OAI.CKSEmbeddingDerivative.I (∞ : ℕ∞ω) N]  {f : M → N} (h : IsSmoothEmbedding OAI.CKSEmbeddingDerivative.I OAI.CKSEmbeddingDerivative.I ∞ f) :
      ∀ x, Injective (mfderiv OAI.CKSEmbeddingDerivative.I OAI.CKSEmbeddingDerivative.I f x) := fun x =>
    proof_immersion_derivative_injective_59 (h.isImmersion.isImmersionAt x)
  have proof_inclusion_hasMFDeriv_61 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) :
      HasMFDerivAt OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 (Subtype.val : OAI.CKSBoundarySurface.Boundary M → M) x OAI.CKSBoundarySurface.liftPlane := by
    refine ⟨continuous_subtype_val.continuousAt, ?_⟩
    exact (OAI.CKSBoundarySurface.liftPlane.hasFDerivAt.congr_of_eventuallyEq (proof_inclusion_chart_eventually_56 x)).hasFDerivWithinAt
  have proof_dropPlane_apply_31  (z : OAI.CKSBoundarySurface.E3) (i : Fin 2) : OAI.CKSBoundarySurface.dropPlane z i = z i.succ := rfl
  have proof_drop_lift_28  (z : OAI.CKSBoundarySurface.E2) : OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.liftPlane z) = z := by ext i; rfl
  have proof_inclusion_mfderiv_injective_62 {M : Type u} [instLocal1 : TopologicalSpace.{u} M] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 M] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) M]  (x : OAI.CKSBoundarySurface.Boundary M) :
      Injective (mfderiv OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 (Subtype.val : OAI.CKSBoundarySurface.Boundary M → M) x) := by
    rw [(proof_inclusion_hasMFDeriv_61 x).mfderiv]
    intro a b h
    change OAI.CKSBoundarySurface.liftPlane a = OAI.CKSBoundarySurface.liftPlane b at h
    have hh : OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.liftPlane a) = OAI.CKSBoundarySurface.dropPlane (OAI.CKSBoundarySurface.liftPlane b) := congrArg OAI.CKSBoundarySurface.dropPlane h
    change (a : OAI.CKSBoundarySurface.E2) = (b : OAI.CKSBoundarySurface.E2)
    exact (proof_drop_lift_28 a).symm.trans (hh.trans (proof_drop_lift_28 b))
  have proof_cutInclusion_derivative_injective_48 {N : Type u} [instLocal1 : TopologicalSpace.{u} N] [instLocal2 : ChartedSpace.{0, u} OAI.CKSBoundarySurface.H3 N] [instLocal3 : IsManifold.{0, 0, 0, u} OAI.CKSBoundarySurface.I3 (∞ : ℕ∞ω) N]  [IsManifold OAI.CKSBoundarySurface.I3 ∞ N] (D : OAI.CKSGeometricCuts.OuterDomain N) (x : OAI.CKSFullCutArea.Surface D) :
      Injective (mfderiv OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 (OAI.CKSFullCutArea.cutInclusion D) x) := by
    unfold OAI.CKSFullCutArea.cutInclusion
    rw [mfderiv_comp x ((D.embedding.isImmersion.contMDiff x.val).mdifferentiableAt (by simp [*]))
      ((proof_inclusion_smooth_57 x).mdifferentiableAt (by simp [*]))]
    · change Injective ((mfderiv OAI.CKSBoundarySurface.I3 OAI.CKSBoundarySurface.I3 D.inclusion x.val) ∘
        (mfderiv OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 (Subtype.val : OAI.CKSFullCutArea.Surface D → D.Carrier) x))
      exact (proof_smooth_embedding_derivative_injective_60 D.embedding x.val).comp
        (proof_inclusion_mfderiv_injective_62 x)
  @OAI.CKSInducedArea.inducedMetric OAI.CKSBoundarySurface.H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 OAI.CKSBoundarySurface.halfSpaceDimension_neZero)
    OAI.CKSBoundarySurface.I3 N _ _ _ (OAI.CKSFullCutArea.Surface D) _ _ _ g (OAI.CKSFullCutArea.cutInclusion D) (proof_cutInclusion_smooth_47 D)
    (proof_cutInclusion_derivative_injective_48 D)

end OAI.CKSFullCutArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSFullCutArea
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Topology ENNReal
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 CKSBoundarySurface.halfSpaceDimension_neZero) I3 ∞ N _ _]
  [SecondCountableTopology N]

def area (g : OAI.CKSFullCutArea.SmoothMetric (N := N)) (D : OAI.CKSGeometricCuts.OuterDomain N) : ℝ≥0∞ :=
  letI : MeasurableSpace (OAI.CKSFullCutArea.Surface D) := borel (OAI.CKSFullCutArea.Surface D)
  letI : BorelSpace (OAI.CKSFullCutArea.Surface D) := ⟨rfl⟩
  OAI.CKSSurfaceVolume.riemannianVolume (OAI.CKSFullCutArea.cutMetric g D).toContinuousRiemannianMetric univ

def minEnclosingArea (g : OAI.CKSFullCutArea.SmoothMetric (N := N)) : ℝ≥0∞ :=
  ⨅ D : OAI.CKSGeometricCuts.OuterDomain N, OAI.CKSFullCutArea.area g D

end OAI.CKSFullCutArea
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicConstraints
open Set Manifold Bundle MeasureTheory CKSLorentz CKSMetricGluing
open scoped ContDiff Topology ENNReal
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

local instance eight_atLeastTwo : Nat.AtLeastTwo 8 := inferInstance

end OAI.CKSIntrinsicConstraints
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSIntrinsicConstraints
open Set Manifold Bundle MeasureTheory CKSLorentz CKSMetricGluing
open scoped ContDiff Topology ENNReal
variable {M : Type u_1} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
attribute [local instance] eight_atLeastTwo


def IntegrableConstraints (g : OAI.CKSMetricGluing.SmoothMetric OAI.CKSIntrinsicConstraints.I (M := M)) (K : OAI.CKSMetricGluing.InnerField OAI.CKSIntrinsicConstraints.I (M := M)) : Prop :=
  ∃ μ j : M → ℝ, Continuous μ ∧ Continuous j ∧
    Integrable μ (OAI.CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
    Integrable j (OAI.CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
    (∀ x, 0 ≤ j x ∧ j x ≤ μ x) ∧
    ∀ x (c : OAI.CKSIntrinsicConstraints.ConstraintChart g.inner K x),
      8 * Real.pi * μ x = c.energy ∧ 8 * Real.pi * j x = c.momentumNorm

end OAI.CKSIntrinsicConstraints
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSourceExterior
open Set Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts CKSSphericalHarmonics
open scoped ContDiff Topology
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

local instance id_invPair (Scalar : Type u_1) [Semiring Scalar] :
    RingHomInvPair (RingHom.id Scalar) (RingHom.id Scalar) := inferInstance

local instance source_manifold_one : IsManifold OAI.CKSGeometricCuts.I3 1 N := inferInstance

end OAI.CKSSourceExterior
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSourceExterior
open Set Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts CKSSphericalHarmonics
open scoped ContDiff Topology
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
attribute [local instance] CKSGeometricCuts.halfSpaceDimension_neZero id_invPair source_manifold_one


local instance source_trivialization_isLinear (point : N) :
    (trivializationAt OAI.CKSLorentz.E (TangentSpace OAI.CKSGeometricCuts.I3) point).IsLinear ℝ := inferInstance

end OAI.CKSSourceExterior
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSourceExterior
open Set Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts CKSSphericalHarmonics
open scoped ContDiff Topology
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
attribute [local instance] CKSGeometricCuts.halfSpaceDimension_neZero id_invPair source_manifold_one
attribute [local instance] source_trivialization_isLinear


def Orientable : Prop :=
  ∃ o : ∀ x : N, Orientation ℝ (TangentSpace OAI.CKSGeometricCuts.I3 x) (Fin 3), ∀ x : N,
    let e := trivializationAt OAI.CKSLorentz.E (TangentSpace OAI.CKSGeometricCuts.I3) x
    ∃ V : Set N, IsOpen V ∧ ∃ hx : x ∈ V, ∃ hV : V ⊆ e.baseSet,
      ∀ y (hy : y ∈ V),
        let atPoint : TangentSpace OAI.CKSGeometricCuts.I3 y ≃L[ℝ] OAI.CKSLorentz.E := e.continuousLinearEquivAt ℝ y (hV hy)
        let atBase : TangentSpace OAI.CKSGeometricCuts.I3 x ≃L[ℝ] OAI.CKSLorentz.E := e.continuousLinearEquivAt ℝ x (hV hx)
        Orientation.map (Fin 3) atPoint.toLinearEquiv (o y) =
        Orientation.map (Fin 3) atBase.toLinearEquiv (o x)

structure CoordinateEnd where
  radius : ℝ
  radius_pos : 0 < radius
  domain : Set N
  isOpen : IsOpen domain
  coordinate : N → OAI.CKSLorentz.E
  inverse : OAI.CKSLorentz.E → N
  smooth : ContMDiffOn OAI.CKSGeometricCuts.I3 𝓘(ℝ,OAI.CKSLorentz.E) ∞ coordinate domain
  inverse_smooth : ContMDiffOn 𝓘(ℝ,OAI.CKSLorentz.E) OAI.CKSGeometricCuts.I3 ∞ inverse {y | radius < ‖y‖}
  mapsTo : ∀ x ∈ domain, radius < ‖coordinate x‖
  left_inverse : ∀ x ∈ domain, inverse (coordinate x) = x
  right_inverse : ∀ y, radius < ‖y‖ → inverse y ∈ domain ∧ coordinate (inverse y) = y
  closed_far_side : ∀ r, radius < r → IsClosed {x : N | x ∈ domain ∧ r ≤ ‖coordinate x‖}
  compact_inner_side : ∀ r, radius < r → IsCompact {x : N | x ∉ domain ∨ ‖coordinate x‖ ≤ r}

structure CKSData (g : OAI.CKSMetricGluing.SmoothMetric OAI.CKSGeometricCuts.I3 (M := N)) (K : OAI.CKSMetricGluing.InnerField OAI.CKSGeometricCuts.I3 (M := N)) where
  chart : OAI.CKSSourceExterior.CoordinateEnd (N := N)
  metricPerturbation : OAI.CKSLorentz.SpatialTensor
  tensorPerturbation : OAI.CKSLorentz.SpatialTensor
  metric_smooth : ∀ y, chart.radius < ‖y‖ → ContDiffAt ℝ ∞ metricPerturbation y
  tensor_smooth : ∀ y, chart.radius < ‖y‖ → ContDiffAt ℝ ∞ tensorPerturbation y
  represents : ∀ x ∈ chart.domain,
    g.inner x = OAI.CKSSpatialManifold.endInner OAI.CKSGeometricCuts.I3 chart.coordinate (OAI.CKSLorentz.sourceSpatial metricPerturbation) x ∧
    K x = OAI.CKSSpatialManifold.endInner OAI.CKSGeometricCuts.I3 chart.coordinate (OAI.CKSLorentz.sourceSpatial tensorPerturbation) x
  massAspect : OAI.CKSLorentz.Sphere → ℝ
  aspect_smooth : OAI.CKSSphericalHarmonics.SmoothSphere massAspect
  patches : OAI.CKSLorentz.Sphere → OAI.CKSLorentz.CKSTensorPatch
  covers : ∀ n, n ∈ (patches n).patch.sphereRegion (patches n).region
  realizes : ∀ n, (patches n).Realizes metricPerturbation tensorPerturbation
  aspect_eq : ∀ n, (patches n).RepresentsMassAspect massAspect

end OAI.CKSSourceExterior
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
open CKSBoundarySurface CKSFullCutArea CKSSurfaceVolume

instance exteriorConnected : ConnectedSpace OAI.CKSSchwarzschild.Exterior := by
  have : ConnectedSpace OAI.CKSSchwarzschild.Radial := isConnected_iff_connectedSpace.mp isConnected_Ici
  have : ConnectedSpace OAI.CKSSchwarzschild.Sphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num : 1 < Module.rank ℝ E3) (0 : OAI.CKSBoundarySurface.E3) (by norm_num : (0 : ℝ) ≤ 1))
  infer_instance

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSourceExterior
open Set Manifold Bundle MeasureTheory CKSGeometricCuts CKSMetricGluing
open scoped ContDiff
variable {N : Type u_1} [TopologicalSpace N] [ChartedSpace H3 N]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 CKSGeometricCuts.halfSpaceDimension_neZero) I3 ∞ N _ _]
  [SecondCountableTopology N]

def cutArea (g : @OAI.CKSMetricGluing.SmoothMetric OAI.CKSGeometricCuts.E3 _ _ OAI.CKSGeometricCuts.H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 OAI.CKSGeometricCuts.halfSpaceDimension_neZero)
    OAI.CKSGeometricCuts.I3 N _ _ _) (D : OAI.CKSGeometricCuts.OuterDomain N) : ℝ :=
  (OAI.CKSFullCutArea.area g D).toReal

def minimumEnclosingArea (g : @OAI.CKSMetricGluing.SmoothMetric OAI.CKSGeometricCuts.E3 _ _ OAI.CKSGeometricCuts.H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 OAI.CKSGeometricCuts.halfSpaceDimension_neZero)
    OAI.CKSGeometricCuts.I3 N _ _ _) : ℝ :=
  ⨅ D : OAI.CKSGeometricCuts.OuterDomain N, OAI.CKSSourceExterior.cutArea g D

def constraintsIntegrable (g : OAI.CKSMetricGluing.SmoothMetric OAI.CKSGeometricCuts.I3 (M := N)) (K : OAI.CKSMetricGluing.InnerField OAI.CKSGeometricCuts.I3 (M := N)) : Prop :=
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  OAI.CKSIntrinsicConstraints.IntegrableConstraints g K

end OAI.CKSSourceExterior
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Manifold Bundle Set Filter
open scoped ContDiff Topology InnerProductSpace
open CKSBoundarySurface
variable {V : Type u_1} [NormedAddCommGroup V] [NormedSpace ℝ V]

def covariantPair (g :
    letI := OAI.CKSLorentz.real_continuousAdd
    letI := OAI.CKSLorentz.real_continuousConstSMul
    letI := OAI.CKSLorentz.real_smulCommClass
    V → V →L[ℝ] V →L[ℝ] ℝ) (N : V → V)
    (x a b : V) : ℝ :=
  letI := OAI.CKSLorentz.two_atLeastTwo
  g x (fderiv ℝ N x a) b + 1/2 *
    (fderiv ℝ (fun y => g y (N x) b) x a +
     fderiv ℝ (fun y => g y a b) x (N x) -
     fderiv ℝ (fun y => g y a (N x)) x b)

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
open CKSBoundarySurface

abbrev Spacetime := ℝ × OAI.CKSBoundarySurface.E3

abbrev SpacetimeBilinear :=
  letI := OAI.CKSLorentz.real_continuousAdd
  letI := OAI.CKSLorentz.real_smulCommClass
  letI := OAI.CKSLorentz.real_continuousConstSMul
  OAI.CKSSchwarzschild.Spacetime →L[ℝ] OAI.CKSSchwarzschild.Spacetime →L[ℝ] ℝ

def timeForm : OAI.CKSSchwarzschild.Spacetime →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ OAI.CKSBoundarySurface.E3

def spacePart : OAI.CKSSchwarzschild.Spacetime →L[ℝ] OAI.CKSBoundarySurface.E3 := ContinuousLinearMap.snd ℝ ℝ OAI.CKSBoundarySurface.E3

def radiusForm (x : OAI.CKSBoundarySurface.E3) : OAI.CKSSchwarzschild.Spacetime →L[ℝ] ℝ := (OAI.CKSSchwarzschild.euclideanForm (OAI.CKSSchwarzschild.radialUnit x)).comp OAI.CKSSchwarzschild.spacePart

def schwarzschildH (m r : ℝ) : ℝ :=
  letI := OAI.CKSLorentz.two_atLeastTwo
  1-2*m/r

local instance spacetimeDual_continuousAdd : ContinuousAdd (OAI.CKSSchwarzschild.Spacetime →L[ℝ] ℝ) := inferInstance

local instance spacetimeDual_isTopologicalAddGroup : IsTopologicalAddGroup (OAI.CKSSchwarzschild.Spacetime →L[ℝ] ℝ) :=
  inferInstance

local instance spacetimeDual_smulCommClass : SMulCommClass ℝ ℝ (OAI.CKSSchwarzschild.Spacetime →L[ℝ] ℝ) := inferInstance

local instance spacetimeDual_continuousConstSMul : ContinuousConstSMul ℝ (OAI.CKSSchwarzschild.Spacetime →L[ℝ] ℝ) :=
  inferInstance

local instance spacetimeDual_isScalarTower : IsScalarTower ℝ ℝ (OAI.CKSSchwarzschild.Spacetime →L[ℝ] ℝ) := inferInstance

local instance spacetimeDual_continuousSMul : ContinuousSMul ℝ (OAI.CKSSchwarzschild.Spacetime →L[ℝ] ℝ) := inferInstance

def advancedMetric (m : ℝ) (z : OAI.CKSSchwarzschild.Spacetime) : OAI.CKSSchwarzschild.SpacetimeBilinear :=
  letI := OAI.CKSLorentz.real_continuousAdd
  letI := OAI.CKSLorentz.real_continuousConstSMul
  letI := OAI.CKSLorentz.real_smulCommClass
  letI := OAI.CKSLorentz.real_isTopologicalAddGroup
  letI := OAI.CKSSchwarzschild.spacetimeDual_continuousAdd
  letI := OAI.CKSSchwarzschild.spacetimeDual_isTopologicalAddGroup
  letI := OAI.CKSSchwarzschild.spacetimeDual_smulCommClass
  letI := OAI.CKSSchwarzschild.spacetimeDual_continuousConstSMul
  letI := OAI.CKSSchwarzschild.spacetimeDual_isScalarTower
  letI := OAI.CKSSchwarzschild.spacetimeDual_continuousSMul
  letI := OAI.CKSSpatialManifold.real_id_compTriple
  letI := OAI.CKSSpatialManifold.real_id_isometric
  let spatialMetric : OAI.CKSSchwarzschild.SpacetimeBilinear := OAI.CKSSchwarzschild.euclideanForm.bilinearComp OAI.CKSSchwarzschild.spacePart OAI.CKSSchwarzschild.spacePart
  (-OAI.CKSSchwarzschild.schwarzschildH m ‖z.2‖) • OAI.CKSSchwarzschild.timeForm.smulRight OAI.CKSSchwarzschild.timeForm +
    OAI.CKSSchwarzschild.timeForm.smulRight (OAI.CKSSchwarzschild.radiusForm z.2) + (OAI.CKSSchwarzschild.radiusForm z.2).smulRight OAI.CKSSchwarzschild.timeForm +
    spatialMetric -
    (OAI.CKSSchwarzschild.radiusForm z.2).smulRight (OAI.CKSSchwarzschild.radiusForm z.2)

def advancedSlope (m r : ℝ) : ℝ := (OAI.CKSSchwarzschild.lapse m r*(OAI.CKSSchwarzschild.lapse m r-OAI.CKSSchwarzschild.velocity m r))⁻¹

def advancedTime (m r : ℝ) : ℝ :=
  letI := OAI.CKSLorentz.two_atLeastTwo
  ∫ s in (2*m)..r, OAI.CKSSchwarzschild.advancedSlope m s

def advancedGraph (m : ℝ) (x : OAI.CKSBoundarySurface.E3) : OAI.CKSSchwarzschild.Spacetime := (OAI.CKSSchwarzschild.advancedTime m ‖x‖,x)

def futureNormal (m : ℝ) (z : OAI.CKSSchwarzschild.Spacetime) : OAI.CKSSchwarzschild.Spacetime :=
  ((OAI.CKSSchwarzschild.lapse m ‖z.2‖-OAI.CKSSchwarzschild.velocity m ‖z.2‖)⁻¹,OAI.CKSSchwarzschild.velocity m ‖z.2‖ • OAI.CKSSchwarzschild.radialUnit z.2)

def graphTangent (m : ℝ) (x a : OAI.CKSBoundarySurface.E3) : OAI.CKSSchwarzschild.Spacetime :=
  letI := OAI.CKSLorentz.two_atLeastTwo
  letI : Inner ℝ OAI.CKSBoundarySurface.E3 :=
    @InnerProductSpace.toInner ℝ OAI.CKSBoundarySurface.E3 _
      (PiLp.seminormedAddCommGroup 2 (fun _ : Fin 3 => ℝ))
      (PiLp.innerProductSpace (fun _ : Fin 3 => ℝ))
  (OAI.CKSSchwarzschild.advancedSlope m ‖x‖ * ⟪OAI.CKSSchwarzschild.radialUnit x,a⟫_ℝ,a)

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Filter Manifold Bundle CKSSpatialManifold CKSMetricGluing CKSLorentz
open scoped ContDiff Topology InnerProductSpace
open CKSBoundarySurface

structure HorizonRegularGraph (m : ℝ) : Prop where
  ambient_smooth : ∀ z : OAI.CKSSchwarzschild.Spacetime, z.2 ≠ 0 → ContDiffAt ℝ ∞ (OAI.CKSSchwarzschild.advancedMetric m) z
  ambient_symmetric : ∀ z a b, OAI.CKSSchwarzschild.advancedMetric m z a b = OAI.CKSSchwarzschild.advancedMetric m z b a
  ambient_nondegenerate : ∀ z : OAI.CKSSchwarzschild.Spacetime, z.2 ≠ 0 → ∀ a : OAI.CKSSchwarzschild.Spacetime,
    (∀ b, OAI.CKSSchwarzschild.advancedMetric m z a b = 0) → a = 0
  graph_smooth_across : ∀ x : OAI.CKSBoundarySurface.E3, m < ‖x‖ → ContDiffAt ℝ ∞ (OAI.CKSSchwarzschild.advancedGraph m) x
  graph_injective : Function.Injective (OAI.CKSSchwarzschild.advancedGraph m)
  graph_derivative : ∀ x : OAI.CKSBoundarySurface.E3, m < ‖x‖ → ∀ a,
    fderiv ℝ (OAI.CKSSchwarzschild.advancedGraph m) x a = OAI.CKSSchwarzschild.graphTangent m x a
  horizon_time : OAI.CKSSchwarzschild.advancedTime m (2*m) = 0
  horizon_slope : OAI.CKSSchwarzschild.advancedSlope m (2*m) = 1/2
  induced_metric : ∀ x : OAI.CKSBoundarySurface.E3, 2*m ≤ ‖x‖ → ∀ a b,
    OAI.CKSSchwarzschild.advancedMetric m (OAI.CKSSchwarzschild.advancedGraph m x) (OAI.CKSSchwarzschild.graphTangent m x a) (OAI.CKSSchwarzschild.graphTangent m x b) = OAI.CKSSchwarzschild.cartMetric m x a b
  normal_unit : ∀ x : OAI.CKSBoundarySurface.E3, 2*m ≤ ‖x‖ →
    OAI.CKSSchwarzschild.advancedMetric m (OAI.CKSSchwarzschild.advancedGraph m x) (OAI.CKSSchwarzschild.futureNormal m (OAI.CKSSchwarzschild.advancedGraph m x))
      (OAI.CKSSchwarzschild.futureNormal m (OAI.CKSSchwarzschild.advancedGraph m x)) = -1
  normal_orthogonal : ∀ x : OAI.CKSBoundarySurface.E3, 2*m ≤ ‖x‖ → ∀ a,
    OAI.CKSSchwarzschild.advancedMetric m (OAI.CKSSchwarzschild.advancedGraph m x) (OAI.CKSSchwarzschild.futureNormal m (OAI.CKSSchwarzschild.advancedGraph m x)) (OAI.CKSSchwarzschild.graphTangent m x a) = 0
  future_facing : ∀ x : OAI.CKSBoundarySurface.E3, 2*m ≤ ‖x‖ → 0 < (OAI.CKSSchwarzschild.futureNormal m (OAI.CKSSchwarzschild.advancedGraph m x)).1
  induced_second_form : ∀ x : OAI.CKSBoundarySurface.E3, 2*m ≤ ‖x‖ → ∀ a b,
    OAI.CKSSchwarzschild.covariantPair (OAI.CKSSchwarzschild.advancedMetric m) (OAI.CKSSchwarzschild.futureNormal m) (OAI.CKSSchwarzschild.advancedGraph m x)
      (OAI.CKSSchwarzschild.graphTangent m x a) (OAI.CKSSchwarzschild.graphTangent m x b) = OAI.CKSSchwarzschild.cartTensor m x a b

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
open CKSBoundarySurface
attribute [local instance] CKSInducedArea.real_continuousAdd CKSInducedArea.real_smulCommClass CKSInducedArea.real_continuousConstSMul CKSBoundarySurface.two_atLeastTwo


local instance frameCovectorModule : Module ℝ (OAI.CKSBoundarySurface.E3 →L[ℝ] ℝ) :=
  @ContinuousLinearMap.module ℝ ℝ ℝ _ _ _ OAI.CKSBoundarySurface.E3 _ _ _ ℝ _ _ _ _
    OAI.CKSInducedArea.real_smulCommClass OAI.CKSInducedArea.real_continuousConstSMul
    (RingHom.id ℝ) OAI.CKSInducedArea.real_continuousAdd

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSchwarzschild
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
open CKSBoundarySurface
attribute [local instance] CKSInducedArea.real_continuousAdd CKSInducedArea.real_smulCommClass CKSInducedArea.real_continuousConstSMul CKSBoundarySurface.two_atLeastTwo
attribute [local instance] OAI.CKSSchwarzschild.frameCovectorModule


def christoffelPair (g : OAI.CKSBoundarySurface.E3 → OAI.CKSBoundarySurface.E3 →L[ℝ] OAI.CKSBoundarySurface.E3 →L[ℝ] ℝ) (x a b c : OAI.CKSBoundarySurface.E3) : ℝ :=
  1/2 * (fderiv ℝ (fun z => g z b c) x a +
    fderiv ℝ (fun z => g z a c) x b - fderiv ℝ (fun z => g z a b) x c)

def firstFrame (g : OAI.CKSBoundarySurface.E3 →L[ℝ] OAI.CKSBoundarySurface.E3 →L[ℝ] ℝ) (T : OAI.CKSBoundarySurface.E2 →L[ℝ] OAI.CKSBoundarySurface.E3) : OAI.CKSBoundarySurface.E2 :=
  (Real.sqrt (g (T (EuclideanSpace.single 0 1)) (T (EuclideanSpace.single 0 1))))⁻¹ •
    EuclideanSpace.single 0 1

def secondResidual (g : OAI.CKSBoundarySurface.E3 →L[ℝ] OAI.CKSBoundarySurface.E3 →L[ℝ] ℝ) (T : OAI.CKSBoundarySurface.E2 →L[ℝ] OAI.CKSBoundarySurface.E3) : OAI.CKSBoundarySurface.E2 :=
  EuclideanSpace.single 1 1 -
    (g (T (EuclideanSpace.single 0 1)) (T (EuclideanSpace.single 1 1)) /
      g (T (EuclideanSpace.single 0 1)) (T (EuclideanSpace.single 0 1))) • EuclideanSpace.single 0 1

def secondFrame (g : OAI.CKSBoundarySurface.E3 →L[ℝ] OAI.CKSBoundarySurface.E3 →L[ℝ] ℝ) (T : OAI.CKSBoundarySurface.E2 →L[ℝ] OAI.CKSBoundarySurface.E3) : OAI.CKSBoundarySurface.E2 :=
  (Real.sqrt (g (T (OAI.CKSSchwarzschild.secondResidual g T)) (T (OAI.CKSSchwarzschild.secondResidual g T))))⁻¹ • OAI.CKSSchwarzschild.secondResidual g T

end OAI.CKSSchwarzschild
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSourceExterior
open Manifold CKSGeometricCuts
open scoped ContDiff
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N]

local instance halfSpace_locallyCompact : LocallyCompactSpace OAI.CKSGeometricCuts.H3 := by
  change LocallyCompactSpace {x : EuclideanSpace ℝ (Fin 3) // 0 ≤ x 0}
  have hc : IsClosed {x : EuclideanSpace ℝ (Fin 3) | 0 ≤ x 0} :=
    isClosed_le continuous_const (by fun_prop)
  exact hc.locallyCompactSpace

end OAI.CKSSourceExterior
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSourceExterior
open Manifold CKSGeometricCuts
open scoped ContDiff
variable {N : Type u_1} [TopologicalSpace N] [ChartedSpace H3 N]

local instance manifold_regular [IsManifold OAI.CKSGeometricCuts.I3 ∞ N] [T2Space N] : T3Space N := by
  let := OAI.CKSSourceExterior.halfSpace_locallyCompact
  let : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace OAI.CKSGeometricCuts.H3 N
  infer_instance

end OAI.CKSSourceExterior
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSSourceExterior
open Set Manifold Bundle Filter CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts
open CKSADM (Symbol)
open scoped ContDiff Topology
variable {N : Type u_1} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  [T2Space N] [SecondCountableTopology N] [ConnectedSpace N]
attribute [local instance] manifold_regular




end OAI.CKSSourceExterior
end


