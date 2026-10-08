-- Prove2me | Definitions.Def_PinchedKahler
-- name    : PinchedKahler
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:03.442431+00:00
-- url     : https://prove2.me/theorems/fb0a2cb1-3763-4e92-af7e-d6413f66a0ae
-- statement:
--   Working in ℂ² (base, with unit ball B) and the ambient space ℂ²×ℂ with coordinates (z₁,z₂,w), this block sets up complex-differential-geometric notions and a Hartogs-domain construction. For φ: B→ℝ, the Hartogs domain is {(z,w): |z|<1 and e^{φ(z)}|w|²<1}. The predicate noMinorant(φ) says there is no holomorphic H on B and constant C with Re H(z) ≤ C + 4 log(1/(1−|z|)) + φ(z) on all of B. Using Wirtinger derivatives dz and dbar, a matrix-valued g gives a curvature tensor R = −∂̄_b∂_a g_{cd} + Σ (g⁻¹)_{ek} ∂_a g_{ce} ∂̄_b g_{kd}, and the sectional curvature of real vectors u,v is (R(u,u,v,v) − R(u,v,u,v)) real parts divided by 2 times the real area (|u|²_g|v|²_g − (Re⟨u,v⟩_g)²). IsKahlerMetric on a set M means g is smooth, Hermitian, positive definite at every point, and satisfies the symmetry ∂_i g_{kj} = ∂_k g_{ij}. GeodesicallyComplete means that through every point with every initial velocity there is a smooth curve defined for all real times, staying in M, satisfying the geodesic equation with the Christoffel symbols of g. IsNegativelyPinched(M,g,A,B) means 0<A≤B and all sectional curvatures of linearly independent real pairs lie in [−B,−A]. NoBoundedCoordinates(M) says no bounded holomorphic map F: M→ℂ³ has everywhere nonvanishing Jacobian determinant, and BiholomorphicToBoundedDomain(M) says M is biholomorphic to some open bounded set. MainTheorem is a defined proposition, not an established theorem: it asserts the existence of an open nonempty contractible M⊂ℂ³ with a complete Kähler metric whose sectional curvature is negatively pinched, with NoBoundedCoordinates but not biholomorphic to a bounded domain. For the construction, psi(z) = −log(1−|z|²), the potential is λ·psi(z) − log(1 − e^{φ(z)}|w|²), and the Hartogs metric is its complex Hessian. ChartControl(φ,c,C) bounds the base complex Hessian of φ composed with every centered Möbius-type chart (parameter r in [0,1) and unitary U), at the origin, between c|v|² and C|v|², and ChartJets(φ,C) bounds by C certain first and mixed second derivatives of that Hessian in the same charts. ControlledPotential is the proposition that some smooth φ on B satisfies ChartControl with c=1, ChartJets and noMinorant for a common C. MetricTransfer is the proposition that for all 0<c≤C there is λ₀>0 such that every smooth φ with ChartControl(φ,c,C) and ChartJets(φ,C), and every λ≥λ₀, yields a contractible Hartogs domain whose Hartogs metric is Kähler, geodesically complete and negatively pinched for some A,B.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PinchedKahler.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PinchedKahler.lean; bytes 16..6841
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PinchedHartogs

abbrev Base := EuclideanSpace ℂ (Fin 2)
abbrev Ambient := Base × ℂ
abbrev Target := Fin 3 → ℂ

def ball : Set Base := {z | ‖z‖ < 1}

def hartogs (φ : Base → ℝ) : Set Ambient :=
  {p | p.1 ∈ ball ∧ Real.exp (φ p.1) * ‖p.2‖ ^ 2 < 1}

def noMinorant (φ : Base → ℝ) : Prop :=
  ¬ ∃ (H : Base → ℂ) (C : ℝ), AnalyticOnNhd ℂ H ball ∧
    ∀ z ∈ ball, (H z).re ≤ C + 4 * Real.log (1 / (1 - ‖z‖)) + φ z

def coordVector (j : Fin 3) : Ambient :=
  ![(EuclideanSpace.single 0 1, 0), (EuclideanSpace.single 1 1, 0), (0, 1)] j

def jacobian (F : Ambient → Target) (p : Ambient) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j ↦ (fderiv ℂ F p (coordVector j)) i

open scoped Matrix.Norms.Elementwise

abbrev CMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev CurvatureTensor := Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ

def coordinates (u : Ambient) : Fin 3 → ℂ := ![u.1 0, u.1 1, u.2]

def dz (f : Ambient → ℂ) (p : Ambient) (j : Fin 3) : ℂ :=
  (fderiv ℝ f p (coordVector j) - Complex.I * fderiv ℝ f p (Complex.I • coordVector j)) / 2

def dbar (f : Ambient → ℂ) (p : Ambient) (j : Fin 3) : ℂ :=
  (fderiv ℝ f p (coordVector j) + Complex.I * fderiv ℝ f p (Complex.I • coordVector j)) / 2

def hermitianValue (h : CMatrix) (u v : Ambient) : ℂ :=
  ∑ i, ∑ j, h i j * coordinates u i * star (coordinates v j)

def realArea (h : CMatrix) (u v : Ambient) : ℝ :=
  (hermitianValue h u u).re * (hermitianValue h v v).re - (hermitianValue h u v).re ^ 2

def tensorValue (R : CurvatureTensor) (u v w y : Ambient) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    R a b c d * coordinates u a * star (coordinates v b) * coordinates w c * star (coordinates y d)

def curvature (g : Ambient → CMatrix) (p : Ambient) : CurvatureTensor := fun a b c d ↦
  -dbar (fun q ↦ dz (fun r ↦ g r c d) q a) p b +
    ∑ e, ∑ k, (g p)⁻¹ e k * dz (fun q ↦ g q c e) p a * dbar (fun q ↦ g q k d) p b

def sectional (g : Ambient → CMatrix) (p u v : Ambient) : ℝ :=
  ((tensorValue (curvature g p) u u v v).re - (tensorValue (curvature g p) u v u v).re) /
    (2 * realArea (g p) u v)

def IsKahlerMetric (M : Set Ambient) (g : Ambient → CMatrix) : Prop :=
  ContDiffOn ℝ ∞ g M ∧
  (∀ p ∈ M, ∀ i j, g p i j = star (g p j i)) ∧
  (∀ p ∈ M, ∀ u : Ambient, u ≠ 0 → 0 < (hermitianValue (g p) u u).re) ∧
  (∀ p ∈ M, ∀ i j k, dz (fun q ↦ g q k j) p i = dz (fun q ↦ g q i j) p k)

def christoffel (g : Ambient → CMatrix) (p : Ambient) (k a c : Fin 3) : ℂ :=
  ∑ e, (g p)⁻¹ e k * dz (fun q ↦ g q c e) p a

def GeodesicallyComplete (M : Set Ambient) (g : Ambient → CMatrix) : Prop :=
  ∀ p ∈ M, ∀ v : Ambient, ∃ γ : ℝ → Ambient,
    ContDiff ℝ ∞ γ ∧ (∀ t, γ t ∈ M) ∧ γ 0 = p ∧ deriv γ 0 = v ∧
      ∀ t k, coordinates (deriv (deriv γ) t) k +
        ∑ a, ∑ c, christoffel g (γ t) k a c * coordinates (deriv γ t) a *
          coordinates (deriv γ t) c = 0

def IsNegativelyPinched (M : Set Ambient) (g : Ambient → CMatrix) (A B : ℝ) : Prop :=
  0 < A ∧ A ≤ B ∧ ∀ p ∈ M, ∀ u v : Ambient, LinearIndependent ℝ ![u, v] →
    -B ≤ sectional g p u v ∧ sectional g p u v ≤ -A

def NoBoundedCoordinates (M : Set Ambient) : Prop :=
  ∀ F : Ambient → Target, AnalyticOnNhd ℂ F M →
    (∃ B : ℝ, ∀ p ∈ M, ∀ i, ‖F p i‖ ≤ B) →
      ¬ ∀ p ∈ M, (jacobian F p).det ≠ 0

def BiholomorphicToBoundedDomain (M : Set Ambient) : Prop :=
  ∃ N : Set Ambient, IsOpen N ∧ Bornology.IsBounded N ∧
    ∃ F G : Ambient → Ambient, AnalyticOnNhd ℂ F M ∧ AnalyticOnNhd ℂ G N ∧
      MapsTo F M N ∧ MapsTo G N M ∧ (∀ p ∈ M, G (F p) = p) ∧ (∀ q ∈ N, F (G q) = q)

def MainTheorem : Prop :=
  ∃ (M : Set Ambient) (g : Ambient → CMatrix) (A B : ℝ),
    IsOpen M ∧ M.Nonempty ∧ ContractibleSpace M ∧ IsKahlerMetric M g ∧
      GeodesicallyComplete M g ∧ IsNegativelyPinched M g A B ∧
      NoBoundedCoordinates M ∧ ¬ BiholomorphicToBoundedDomain M

def psi (z : Base) : ℝ := -Real.log (1 - ‖z‖ ^ 2)
def metricPotential (φ : Base → ℝ) (lam : ℝ) (p : Ambient) : ℝ :=
  lam * psi p.1 - Real.log (1 - Real.exp (φ p.1) * ‖p.2‖ ^ 2)

def complexHessian (f : Ambient → ℝ) (p : Ambient) : CMatrix :=
  fun i j ↦ dz (fun q ↦ dbar (fun r ↦ (f r : ℂ)) q j) p i

def hartogsMetric (φ : Base → ℝ) (lam : ℝ) : Ambient → CMatrix :=
  complexHessian (metricPotential φ lam)

def dzBase (f : Base → ℂ) (z : Base) (i : Fin 2) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single i 1) -
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single i 1)) / 2

def dbarBase (f : Base → ℂ) (z : Base) (i : Fin 2) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single i 1) +
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single i 1)) / 2

def baseHessian (φ : Base → ℝ) (z : Base) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ dzBase (fun q ↦ dbarBase (fun r ↦ (φ r : ℂ)) q j) z i

def centeredChart (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base) (ζ : Base) : Base :=
  U (WithLp.toLp 2 ![((r : ℂ) + ζ 0) / (1 + (r : ℂ) * ζ 0),
    ((Real.sqrt (1 - r ^ 2) : ℝ) : ℂ) * ζ 1 / (1 + (r : ℂ) * ζ 0)])

def ChartControl (φ : Base → ℝ) (c C : ℝ) : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base, ∀ v : Base,
    c * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, baseHessian (φ ∘ centeredChart r U) 0 i j * v i * star (v j)).re ∧
    (∑ i, ∑ j, baseHessian (φ ∘ centeredChart r U) 0 i j * v i * star (v j)).re ≤ C * ‖v‖ ^ 2

def ChartJets (φ : Base → ℝ) (C : ℝ) : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base, ∀ i j k l : Fin 2,
    ‖dzBase (fun z ↦ baseHessian (φ ∘ centeredChart r U) z i j) 0 k‖ +
    ‖dbarBase (fun z ↦ baseHessian (φ ∘ centeredChart r U) z i j) 0 l‖ +
    ‖dzBase (fun z ↦ dbarBase (fun q ↦ baseHessian (φ ∘ centeredChart r U) q i j) z l) 0 k‖ ≤ C

def ControlledPotential : Prop :=
  ∃ φ : Base → ℝ, ∃ C : ℝ, ContDiffOn ℝ ∞ φ ball ∧
    ChartControl φ 1 C ∧ ChartJets φ C ∧ noMinorant φ

def MetricTransfer : Prop :=
  ∀ c C : ℝ, 0 < c → c ≤ C → ∃ lam0 : ℝ, 0 < lam0 ∧
    ∀ φ : Base → ℝ, ContDiffOn ℝ ∞ φ ball → ChartControl φ c C → ChartJets φ C →
      ∀ lam : ℝ, lam0 ≤ lam → ContractibleSpace (hartogs φ) ∧
        IsKahlerMetric (hartogs φ) (hartogsMetric φ lam) ∧
        GeodesicallyComplete (hartogs φ) (hartogsMetric φ lam) ∧
        ∃ A B : ℝ, IsNegativelyPinched (hartogs φ) (hartogsMetric φ lam) A B



end PinchedHartogs
end
end OAI


