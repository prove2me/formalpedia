-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35
-- name    : QAlgorithms_Papers_Independent_Support50_P35
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:36:37.281817+00:00
-- url     : https://prove2.me/theorems/b8163661-5e90-490b-877f-526c692d681e
-- title:
--   Definitions for Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction
-- statement:
--   The objects the formalized statements of *Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction* (arXiv:quant-ph/0402055) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FiniteConvexDecomposition`: PDF p.4, Eqs.(2)--(3): every positive finite length, nonnegative weights, unit total weight, prescribed barycenter. No dimension-dependent truncation.
--   - `roofValues`: PDF p.4: the set of all feasible average costs, using actual finite sums.
--   - `lowerRoof`: PDF p.4, Eq.(2). On empty or unbounded-below cost sets, real sInf has its totalized default value; results below use compact continuous data.
--   - `upperRoof`: PDF p.4, Eq.(3). Results below have nonempty, bounded feasible cost sets.
--   - `graphOn`: PDF p.5, Eq.(4): no closure is taken.
--   - `tangentDirections`: PDF pp.6--7: tangent directions, realized as the span of velocities of curves staying in M near zero. For a C1 embedded manifold without boundary this is its ordinary tangent space in the ambient real vector space.
--   - `IsEmbeddedDim`: PDF pp.6--7: a C1 embedded manifold without boundary, in its subspace topology. The inclusion is an immersion in standard boundaryless real models.
--   - `IsNonsingularVariety`: PDF p.3: algebraic, irreducible, nonsingular embedded real variety. Irreducibility uses the prime ideal of all polynomials vanishing on V; nonsingularity requires the Zariski tangent dimension to equal the manifold dimension at every point, rather than a chosen equation list's Jacobian rank.
--   - `normalMap`: PDF p.7: normal functional of a hyperplane.
--   - `Hyperplane`: PDF p.7: a genuine affine hyperplane, with nonzero normal.
--   - `Hyperplane.points`: PDF p.7: the affine set of points, distinguished from its direction space.
--   - `Hyperplane.direction`: PDF p.7: the translated linear space parallel to H.
--   - `IsMTangent`: PDF p.7, Definition 2.5: contact and containment of all tangent directions.
--   - `ContainsInHalfspace`: PDF p.7: the oriented closed halfspace contains all of M. Contact points are supplied separately, so this also expresses membership in the source's Omega.
--   - `cubicGraph`: PDF pp.4,10: the graph of x^3 over the circle, in the true lifted ambient R3.
--   - `circle`: PDF p.4, Figure 1: the base circle and its cubic cost.
--   - `cubicCost`: PDF p.4: cubic-circle cost.
--   - `PairIndex`: PDF pp.11--12: the unordered off-diagonal labels, enumerated once with a<b.
--   - `TracelessIndex`: PDF pp.11--12: diagonal labels a=2,...,D (stored as a-1), and the two off-diagonal families. false is symmetric; true is antisymmetric.
--   - `FullIndex`: PDF p.12: none is the identity label 0; some labels are traceless.
--   - `normOneGellmannGenerator`: PDF pp.11--12, Eqs.(18)--(20): the literal norm-one Gellmann generators.
--   - `gellmann`: PDF p.12, Eq.(23): complete normalized basis, including I/sqrt(D).
--   - `IsHermitianONBasis`: PDF pp.12,15: a complete real Hermitian orthonormal operator basis.
--   - `hermitianReconstruction`: PDF p.15: unscaled reconstruction rho=sum c_alpha mu_alpha.
--   - `hermitianCoordinates`: PDF p.15: unscaled real coordinates tr(rho mu_alpha).
--   - `symmetricConstant`: PDF p.12, Eqs.(21)--(22): symmetric real structure constants.
--   - `antisymmetricConstant`: PDF p.12, Eq.(21): antisymmetric real structure constants.
--   - `wedge`: PDF p.13, Eq.(31): traceless-coordinate wedge product.
--   - `starProduct`: PDF p.13, Eq.(32): traceless-coordinate star product.
--   - `scaledGellmannState`: PDF p.13, Eq.(28): the paper's scaled traceless-coordinate reconstruction.
--   - `pureQuadraticSet`: PDF p.14, Eqs.(38)--(39): corrected real quadratic zero locus. The scalar D-2 is real subtraction, including at D=1.
--   - `adjointAction`: PDF p.13, Eq.(33): the traceless block of the adjoint representation.
--   - `coordinateAngle`: PDF p.14, Eq.(41): ordinary Euclidean angle of nonzero coordinate vectors.
--   - `multiplicationCoefficient`: PDF p.15, Eq.(42): generally complex multiplication coefficients.
--   - `generalPureEquations`: PDF p.15, Eqs.(43)--(45): real quadratic equations. Taking real parts AFTER symmetric contraction loses no equation: the imaginary part cancels.
--   - `generalPureSet`: PDF p.15: the explicitly quadratic real variety in an arbitrary basis.
--   - `basisChange`: PDF pp.15--16, Eq.(46): coordinates in target basis of source basis vectors. Thus target coordinates equal this matrix times source coordinates.
--   - `powerPurityCost`: PDF p.18, Eq.(56): literal factor 2 and real part of the power trace. Density hypotheses ensure the trace itself is real.
--   - `IsMarginalCost`: PDF pp.17--18, Eqs.(53)--(55): the marginal-function hypotheses.
--   - `tensorGellmannBasis`: PDF p.18, Eq.(57): complete norm-one tensor-product Gellmann basis.
--   - `tensorMarginal`: PDF p.18, Eq.(58), corrected: tr(lambda_B0)=sqrt(N), not 1.
--   - `coordinateCost`: PDF p.19: the pure marginal cost pulled back to operator coordinates.
--   - `formationValues`: PDF p.19: actual finite pure-state feasible average costs.
--   - `rankRestrictedValues`: PDF p.19, Eq.(61): rank-restricted feasible costs. The printed reversed bounds are corrected to r<=s<=r^2. Rank is that of rho, not its ambient dimension.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, https://arxiv.org/abs/quant-ph/0402055v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

/-!
# Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction

Source: arXiv:quant-ph/0402055v2 (PDF pages). Only finite-dimensional spaces and
finite decompositions occur here. Accepted paper interfaces are imported solely
for their normalized pure-state predicate and finite arbitrary-real-cost roof.
Corrections to Eqs.(15),(39),(46),(58),(59),(61) are recorded in MODERATION_NOTES.md.
No claim that tangency is sufficient for support or optimality is made.
-/

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.4, Eqs.(2)--(3): every positive finite length, nonnegative weights,
unit total weight, prescribed barycenter. No dimension-dependent truncation. -/
structure FiniteConvexDecomposition {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (V : Set E) (r : E) where
  count : ℕ
  positive : 0 < count
  point : Fin count → E
  member : ∀ j, point j ∈ V
  weight : Fin count → ℝ
  nonnegative : ∀ j, 0 ≤ weight j
  total : ∑ j, weight j = 1
  barycenter : ∑ j, weight j • point j = r

/-- PDF p.4: the set of all feasible average costs, using actual finite sums. -/
def roofValues {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (V : Set E) (f : E → ℝ) (r : E) : Set ℝ :=
  {a | ∃ e : FiniteConvexDecomposition V r, a = ∑ j, e.weight j * f (e.point j)}

/-- PDF p.4, Eq.(2). On empty or unbounded-below cost sets, real sInf has
its totalized default value; results below use compact continuous data. -/
def lowerRoof {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (V : Set E) (f : E → ℝ) (r : E) : ℝ := sInf (roofValues V f r)

/-- PDF p.4, Eq.(3). Results below have nonempty, bounded feasible cost sets. -/
def upperRoof {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (V : Set E) (f : E → ℝ) (r : E) : ℝ := sSup (roofValues V f r)

/-- PDF p.5, Eq.(4): no closure is taken. -/
def graphOn {E : Type*} (V : Set E) (f : E → ℝ) : Set (E × ℝ) :=
  (fun x => (x, f x)) '' V

/-- PDF pp.6--7: tangent directions, realized as the span of velocities of
curves staying in M near zero. For a C1 embedded manifold without boundary
this is its ordinary tangent space in the ambient real vector space. -/
def tangentDirections {n : ℕ} (M : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ {v | ∃ g : ℝ → (Fin n → ℝ),
    g 0 = x ∧ HasDerivAt g v 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ), g t ∈ M}

/-- PDF pp.6--7: a C1 embedded manifold without boundary, in its subspace
topology. The inclusion is an immersion in standard boundaryless real models. -/
def IsEmbeddedDim {n : ℕ} (M : Set (Fin n → ℝ)) (d : ℕ) : Prop :=
  ∃ charts : ChartedSpace (EuclideanSpace ℝ (Fin d)) M,
    letI := charts
    IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin d))) 1 M ∧
      Manifold.IsImmersion (𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
        (𝓘(ℝ, Fin n → ℝ)) 1 (Subtype.val : M → (Fin n → ℝ))

/-- PDF p.3: algebraic, irreducible, nonsingular embedded real variety.
Irreducibility uses the prime ideal of all polynomials vanishing on V;
nonsingularity requires the Zariski tangent dimension to equal the manifold
dimension at every point, rather than a chosen equation list's Jacobian rank. -/
def IsNonsingularVariety {n : ℕ} (V : Set (Fin n → ℝ)) : Prop :=
  V = MvPolynomial.zeroLocus ℝ (MvPolynomial.vanishingIdeal ℝ V) ∧
  (MvPolynomial.vanishingIdeal ℝ V).IsPrime ∧
  ∃ d, IsEmbeddedDim V d ∧ ∀ x ∈ V,
    Module.finrank ℝ (Submodule.span ℝ {v : Fin n → ℝ |
      ∀ p ∈ MvPolynomial.vanishingIdeal ℝ V,
        ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i p) * v i = 0}) = d

/-- PDF p.7: normal functional of a hyperplane. -/
def normalMap {n : ℕ} (a : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, a i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm, mul_assoc]

/-- PDF p.7: a genuine affine hyperplane, with nonzero normal. -/
structure Hyperplane (n : ℕ) where
  normal : Fin n → ℝ
  offset : ℝ
  nonzero : normal ≠ 0

/-- PDF p.7: the affine set of points, distinguished from its direction space. -/
def Hyperplane.points {n : ℕ} (H : Hyperplane n) : Set (Fin n → ℝ) :=
  {x | normalMap H.normal x = H.offset}

/-- PDF p.7: the translated linear space parallel to H. -/
def Hyperplane.direction {n : ℕ} (H : Hyperplane n) : Submodule ℝ (Fin n → ℝ) :=
  (normalMap H.normal).ker

/-- PDF p.7, Definition 2.5: contact and containment of all tangent directions. -/
def IsMTangent {n m : ℕ} (H : Hyperplane n) (M : Set (Fin n → ℝ))
    (x : Fin m → (Fin n → ℝ)) : Prop :=
  (∀ j, x j ∈ M ∩ H.points) ∧ ∀ j, tangentDirections M (x j) ≤ H.direction

/-- PDF p.7: the oriented closed halfspace contains all of M. Contact points
are supplied separately, so this also expresses membership in the source's Omega. -/
def ContainsInHalfspace {n : ℕ} (H : Hyperplane n) (M : Set (Fin n → ℝ)) : Prop :=
  ∀ y ∈ M, normalMap H.normal y ≤ H.offset

/-- Sanity: an ordinary singleton decomposition has positive length and cost f(x). -/
example {E : Type*} [AddCommMonoid E] [Module ℝ E] (x : E) (f : E → ℝ) :
    f x ∈ roofValues ({x} : Set E) f x := by
  refine ⟨⟨1, by decide, fun _ => x, by simp, fun _ => 1,
    by simp, by simp, by simp⟩, ?_⟩
  simp

example {n : ℕ} (a : Fin n → ℝ) : normalMap a 0 = 0 := by simp [normalMap]

example {E : Type*} [AddCommMonoid E] [Module ℝ E] (V : Set E) (f : E → ℝ)
    (r : E) : lowerRoof V f r = sInf (roofValues V f r) := rfl

/-- PDF pp.4,10: the graph of x^3 over the circle, in the true lifted ambient R3. -/
def cubicGraph : Set (Fin 3 → ℝ) :=
  {q | q 0 ^ 2 + q 1 ^ 2 = 1 ∧ q 2 = q 0 ^ 3}

/-- PDF p.4, Figure 1: the base circle and its cubic cost. -/
def circle : Set (Fin 2 → ℝ) := {q | q 0 ^ 2 + q 1 ^ 2 = 1}

/-- PDF p.4: cubic-circle cost. -/
def cubicCost (q : Fin 2 → ℝ) : ℝ := q 0 ^ 3

/-- PDF pp.11--12: the unordered off-diagonal labels, enumerated once with a<b. -/
abbrev PairIndex (D : ℕ) := {p : Fin D × Fin D // p.1 < p.2}

/-- PDF pp.11--12: diagonal labels a=2,...,D (stored as a-1), and the two
off-diagonal families. false is symmetric; true is antisymmetric. -/
abbrev TracelessIndex (D : ℕ) := {a : Fin D // 0 < a.val} ⊕ (PairIndex D × Bool)

/-- PDF p.12: none is the identity label 0; some labels are traceless. -/
abbrev FullIndex (D : ℕ) := Option (TracelessIndex D)

/-- PDF pp.11--12, Eqs.(18)--(20): the literal norm-one Gellmann generators. -/
def normOneGellmannGenerator {D : ℕ} : TracelessIndex D → Matrix (Fin D) (Fin D) ℂ
  | Sum.inl a => fun i j =>
      if i = j then
        ((if i.val < a.val.val then 1 else if i = a.val then -(a.val.val : ℝ) else 0) /
          Real.sqrt (((a.val.val : ℝ) + 1) * a.val.val) : ℝ)
      else 0
  | Sum.inr (p, false) => fun i j =>
      (if (i = p.val.1 ∧ j = p.val.2) ∨ (i = p.val.2 ∧ j = p.val.1) then
        ((Real.sqrt 2)⁻¹ : ℝ) else 0 : ℂ)
  | Sum.inr (p, true) => fun i j =>
      if i = p.val.1 ∧ j = p.val.2 then -Complex.I / (Real.sqrt 2 : ℂ)
      else if i = p.val.2 ∧ j = p.val.1 then Complex.I / (Real.sqrt 2 : ℂ) else 0

/-- PDF p.12, Eq.(23): complete normalized basis, including I/sqrt(D). -/
def gellmann (D : ℕ) : FullIndex D → Matrix (Fin D) (Fin D) ℂ
  | none => (Real.sqrt (D : ℝ) : ℂ)⁻¹ • 1
  | some j => normOneGellmannGenerator j

/-- PDF pp.12,15: a complete real Hermitian orthonormal operator basis. -/
def IsHermitianONBasis {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]
    (mu : K → Matrix I I ℂ) : Prop :=
  (∀ k, (mu k).IsHermitian) ∧
  (∀ j k, (mu j * mu k).trace = if j = k then 1 else 0) ∧
  (∀ A : Matrix I I ℂ, A.IsHermitian → ∃ c : K → ℝ, A = ∑ k, (c k : ℂ) • mu k)

/-- PDF p.15: unscaled reconstruction rho=sum c_alpha mu_alpha. -/
def hermitianReconstruction {I K : Type*} [Fintype K] (mu : K → Matrix I I ℂ) (c : K → ℝ) :
    Matrix I I ℂ := ∑ k, (c k : ℂ) • mu k

/-- PDF p.15: unscaled real coordinates tr(rho mu_alpha). -/
def hermitianCoordinates {I K : Type*} [Fintype I] (mu : K → Matrix I I ℂ)
    (rho : Matrix I I ℂ) : K → ℝ := fun k => (rho * mu k).trace.re

/-- PDF p.12, Eqs.(21)--(22): symmetric real structure constants. -/
def symmetricConstant {D : ℕ} (j k l : TracelessIndex D) : ℝ :=
  (normOneGellmannGenerator j * normOneGellmannGenerator k * normOneGellmannGenerator l).trace.re

/-- PDF p.12, Eq.(21): antisymmetric real structure constants. -/
def antisymmetricConstant {D : ℕ} (j k l : TracelessIndex D) : ℝ :=
  (normOneGellmannGenerator j * normOneGellmannGenerator k * normOneGellmannGenerator l).trace.im

/-- PDF p.13, Eq.(31): traceless-coordinate wedge product. -/
def wedge {D : ℕ} (a b : TracelessIndex D → ℝ) : TracelessIndex D → ℝ :=
  fun l => ∑ j, ∑ k, a j * b k * antisymmetricConstant j k l

/-- PDF p.13, Eq.(32): traceless-coordinate star product. -/
def starProduct {D : ℕ} (a b : TracelessIndex D → ℝ) : TracelessIndex D → ℝ :=
  fun l => ∑ j, ∑ k, a j * b k * symmetricConstant j k l

/-- PDF p.13, Eq.(28): the paper's scaled traceless-coordinate reconstruction. -/
def scaledGellmannState {D : ℕ} (c : TracelessIndex D → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  (D : ℂ)⁻¹ • (1 + ∑ j, (c j : ℂ) • normOneGellmannGenerator j)

/-- PDF p.14, Eqs.(38)--(39): corrected real quadratic zero locus.
The scalar D-2 is real subtraction, including at D=1. -/
def pureQuadraticSet (D : ℕ) : Set (TracelessIndex D → ℝ) :=
  {c | dotProduct c c = (D : ℝ) * ((D : ℝ) - 1) ∧
    starProduct c c = ((D : ℝ) - 2) • c}

/-- PDF p.13, Eq.(33): the traceless block of the adjoint representation. -/
def adjointAction {D : ℕ} (U : Matrix (Fin D) (Fin D) ℂ)
    (a : TracelessIndex D → ℝ) : TracelessIndex D → ℝ :=
  fun j => ∑ k, (normOneGellmannGenerator j * U * normOneGellmannGenerator k * Uᴴ).trace.re * a k

example {I K : Type*} [Fintype K] (mu : K → Matrix I I ℂ) : hermitianReconstruction mu 0 = 0 := by
  simp [hermitianReconstruction]

/-- Sanity: the antisymmetric generator's upper entry is -i/sqrt(2). -/
example : normOneGellmannGenerator (D := 2)
    (Sum.inr (⟨(0, 1), by decide⟩, true)) 0 1 = -Complex.I / (Real.sqrt 2 : ℂ) := by
  simp [normOneGellmannGenerator]

/-- Sanity: the zero coordinate vector reconstructs I/D in the scaled convention. -/
example (D : ℕ) : scaledGellmannState (D := D) 0 =
    (D : ℂ)⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  simp [scaledGellmannState]

example : gellmann 1 none = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [gellmann]

/-- PDF p.14, Eq.(41): ordinary Euclidean angle of nonzero coordinate vectors. -/
def coordinateAngle {K : Type*} [Fintype K] (r s : K → ℝ) : ℝ :=
  Real.arccos (dotProduct r s / (Real.sqrt (dotProduct r r) * Real.sqrt (dotProduct s s)))

/-- PDF p.15, Eq.(42): generally complex multiplication coefficients. -/
def multiplicationCoefficient {I K : Type*} [Fintype I]
    (mu : K → Matrix I I ℂ) (a b c : K) : ℂ := (mu a * mu b * mu c).trace

/-- PDF p.15, Eqs.(43)--(45): real quadratic equations. Taking real parts
AFTER symmetric contraction loses no equation: the imaginary part cancels. -/
def generalPureEquations {I K : Type*} [Fintype I] [Fintype K]
    (mu : K → Matrix I I ℂ) (c : K → ℝ) : Prop :=
  (∑ a, c a * (mu a).trace.re) = 1 ∧ dotProduct c c = 1 ∧
    ∀ g, (∑ a, ∑ b, c a * c b * (multiplicationCoefficient mu a b g).re) = c g

/-- PDF p.15: the explicitly quadratic real variety in an arbitrary basis. -/
def generalPureSet {I K : Type*} [Fintype I] [Fintype K]
    (mu : K → Matrix I I ℂ) : Set (K → ℝ) := {c | generalPureEquations mu c}

/-- PDF pp.15--16, Eq.(46): coordinates in target basis of source basis vectors.
Thus target coordinates equal this matrix times source coordinates. -/
def basisChange {I K L : Type*} [Fintype I]
    (target : L → Matrix I I ℂ) (source : K → Matrix I I ℂ) : Matrix L K ℝ :=
  fun l k => (source k * target l).trace.re

/-- Sanity: basis-change entries are fixed by reconstruction, without a transpose guess. -/
example {I K L : Type*} [Fintype I] (mu : K → Matrix I I ℂ)
    (nu : L → Matrix I I ℂ) (k : K) (l : L) :
    basisChange nu mu l k = (mu k * nu l).trace.re := rfl

/-- PDF p.18, Eq.(56): literal factor 2 and real part of the power trace.
Density hypotheses ensure the trace itself is real. -/
def powerPurityCost {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℕ) (rho : Matrix I I ℂ) : ℝ := 2 * (1 - (rho ^ a).trace.re)

/-- PDF pp.17--18, Eqs.(53)--(55): the marginal-function hypotheses. -/
def IsMarginalCost {I : Type*} [Fintype I] [DecidableEq I]
    (f : Matrix I I ℂ → ℝ) : Prop :=
  ContinuousOn f {rho | IsDensityMatrix rho} ∧
  (∀ rho, IsDensityMatrix rho → ∀ U : Matrix.unitaryGroup I ℂ,
    f ((U : Matrix I I ℂ) * rho * (U : Matrix I I ℂ)ᴴ) = f rho) ∧
  ConcaveOn ℝ {rho | IsDensityMatrix rho} f

example {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    powerPurityCost 2 rho = 2 * (1 - (rho * rho).trace.re) := by
  simp [powerPurityCost, pow_two]

/-- PDF p.18, Eq.(57): complete norm-one tensor-product Gellmann basis. -/
def tensorGellmannBasis (M N : ℕ) (k : FullIndex M × FullIndex N) :
    Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ :=
  Matrix.kronecker (gellmann M k.1) (gellmann N k.2)

/-- PDF p.18, Eq.(58), corrected: tr(lambda_B0)=sqrt(N), not 1. -/
def tensorMarginal {M N : ℕ} (c : FullIndex M × FullIndex N → ℝ) :
    Matrix (Fin M) (Fin M) ℂ :=
  (Real.sqrt (N : ℝ) : ℂ) • ∑ alpha, (c (alpha, none) : ℂ) • gellmann M alpha

/-- Sanity: no spurious marginal is generated by zero operator coordinates. -/
example (M N : ℕ) : tensorMarginal (M := M) (N := N) 0 = 0 := by
  simp [tensorMarginal]

/-- PDF p.19: the pure marginal cost pulled back to operator coordinates. -/
def coordinateCost {M N : ℕ} {K : Type*} [Fintype K]
    (mu : K → Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ)
    (f : Matrix (Fin M) (Fin M) ℂ → ℝ) (c : K → ℝ) : ℝ :=
  f (traceRight (hermitianReconstruction mu c))

/-- PDF p.19: actual finite pure-state feasible average costs. -/
def formationValues {M N : ℕ} (f : Matrix (Fin M) (Fin M) ℂ → ℝ)
    (rho : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) : Set ℝ :=
  {z | ∃ e : QAlgorithms.Papers.Independent.Information100.P03.PureEnsemble (Fin M × Fin N),
    ensembleDensity e.weight e.vector = rho ∧
    z = ∑ j, e.weight j * f (traceRight (pureDensity (e.vector j)))}

/-- PDF p.19, Eq.(61): rank-restricted feasible costs. The printed reversed
bounds are corrected to r<=s<=r^2. Rank is that of rho, not its ambient dimension. -/
def rankRestrictedValues {M N : ℕ} (f : Matrix (Fin M) (Fin M) ℂ → ℝ)
    (rho : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) : Set ℝ :=
  {z | ∃ e : QAlgorithms.Papers.Independent.Information100.P03.PureEnsemble (Fin M × Fin N),
    rho.rank ≤ e.count ∧ e.count ≤ rho.rank ^ 2 ∧
    ensembleDensity e.weight e.vector = rho ∧
    z = ∑ j, e.weight j * f (traceRight (pureDensity (e.vector j)))}

end QAlgorithms.Papers.Independent.Support50.P35


