-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P05
-- name    : QAlgorithms_Papers_Independent_Gap48_P05
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:02:05.920294+00:00
-- url     : https://prove2.me/theorems/bb4682e5-1173-4c47-9cd3-e8b48f86cf51
-- title:
--   Definitions for Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups
-- statement:
--   The objects the formalized statements of *Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups* (arXiv:1505.02659) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BastianiCkOn`: PDF pp. 3--4: the finite-order version of the accepted Bastiani calculus. Conditions above order k are deliberately absent. Order zero is joint continuity of f, with its empty tuple of directions.
--   - `BastianiCkMap`: PDF pp. 3--4: finite-order smoothness in the actual manifold atlas.
--   - `ExponentialLieData`: PDF p. 4: a locally convex smooth group with its actual exponential function. The Lie algebra is the identity tangent space identified with E by chartAt E 1; the last field fixes that identification, rather than allowing an unrelated one-parameter-subgroup parametrization. Hausdorff locally convex model assumptions are carried by theorem binders.
--   - `HasGeneratorValue`: Definition 1.1(b), PDF p. 4: graph of the actual infinitesimal generator, via a punctured real derivative at zero.
--   - `GeneratorDomain`: Definition 1.1(b), PDF p. 4: domain of the actual generator.
--   - `infinitesimalGeneratorValue`: Definition 1.1(b), PDF p. 4: the generator value chosen from its limit graph. Its off-domain value is zero, never used without a domain guard in an operator-domain assertion. In Hausdorff targets the on-domain value is uniquely determined.
--   - `derivedWord`: Definition 1.1, PDF pp. 4--5: ordered products, with the rightmost generator applied first. The empty word acts as the identity.
--   - `WordDomain`: Definition 1.1, PDF pp. 4--5: recursive domains of actual operator compositions. This prevents zero defaults from enlarging D^n.
--   - `DerivedDomain`: Definition 1.1, PDF p. 4: common domain of all words of length n.
--   - `DerivedInfinity`: Definition 1.1, PDF p. 4: the common domain of every finite word.
--   - `derivedTupleValue`: Definition 1.1, PDF p. 5: omega_v^n with its ordered n-tuple.
--   - `SmoothVectors`: Definition 1.1(a), PDF p. 4: smooth vectors of the given action.
--   - `VectorCriterion`: Definition 1.1 and Theorem 1.1(i), PDF pp. 4--7: the finite C^k criterion, expressed in the ambient target topology. The definition also supports order zero, with no positive-order derivative requirement.
--   - `IntegralComplete`: Definition 1.3, PDF p. 5: weak integrals of all continuous curves on [0,1], tested by every continuous K-linear functional. No Banach or Bochner-integrability assumption replaces integral completeness.
--   - `WeakC1Separates`: Definition 1.2, PDF p. 5: weak-star C^1 functionals separate points. The scalar coefficient maps use the actual action; inverse pullback in the contragredient representation gives exactly the same C^1 condition.
--   - `unitaryOperator`: PDF pp. 4,7: a unitary represented as a bounded complex-linear map, with the operator norm on B(H).
--   - `IsSmoothing`: Definition 2.1, PDF p. 7: smoothing means that the entire range is contained in the smooth-vector space, not just in the common generator domain.
--   - `leftAction`: Corollary 1.1(i), PDF p. 7: the actual left action on operators.
--   - `alphaAction`: Corollary 1.1(ii), PDF p. 7: the two-sided action, with inverse in the second variable.
--   - `rightInverseOperatorAction`: Lemma 2.3, PDF p. 10: right multiplication by pi(g) inverse.
--   - `derivedPolynomial`: Theorem 2.1, PDF pp. 10--11: a concrete representative of an element of the complex enveloping algebra is a finite complex linear combination of words in real Lie-algebra elements. All such representatives are used; the representation factors through the usual enveloping relations.
--   - `AdjointDerivedBounded`: Theorem 2.1(v), PDF p. 10: A* d pi(D) bounded on the actual dense space of smooth vectors. Each constant may depend on D and A, not on v.
--   - `DerivedAfterBounded`: Theorem 2.1, final clause, PDF p. 10: boundedness of d pi(D) A on all of H, with a uniform bound for each D. On smoothing ranges all word-domain requirements are fulfilled, so off-domain defaults are irrelevant.
--   - `PMapBounded`: Lemma 2.1, PDF p. 9: boundedness on an operator's given domain, with the norm induced from H; it does not mean a bound in the graph norm.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, https://arxiv.org/abs/1505.02659v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

/-!
Draft statements from Neeb--Salmasian--Zellner, arXiv:1505.02659v2.
The accepted Bastiani calculus is used without imposing a norm on the model.
Every new definition is local to this paper. Compilation and independent
moderation are pending the batch handoff; deferred nodes are listed in HARD.md.
-/

namespace QAlgorithms.Papers.Independent.Gap48.P05

open Set Filter Topology
open QAlgorithms.Papers.Independent.Claimed50.P22
open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

/-- Product charts used for multiplication and the two-sided action. -/
local instance productCharts
    (E F M N : Type*) [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N] : ChartedSpace (E × F) (M × N) :=
  prodChartedSpace E M F N

section FiniteCalculus

variable {E : Type u} {F : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- PDF pp. 3--4: the finite-order version of the accepted Bastiani
calculus. Conditions above order k are deliberately absent. Order zero
is joint continuity of f, with its empty tuple of directions. -/
def BastianiCkOn (k : ℕ) (U : Set E) (f : E → F) : Prop :=
  ∃ d : (n : ℕ) → E → (Fin n → E) → F,
    (∀ x ∈ U, d 0 x (fun i => Fin.elim0 i) = f x) ∧
    (∀ n, n ≤ k → ContinuousOn
      (fun p : E × (Fin n → E) => d n p.1 p.2)
      (U ×ˢ (Set.univ : Set (Fin n → E)))) ∧
    (∀ n, n + 1 ≤ k → ∀ x ∈ U, ∀ (a : Fin n → E) (h : E),
      Tendsto (fun t : ℝ => t⁻¹ • (d n (x + t • h) a - d n x a))
        (𝓝[≠] (0 : ℝ)) (𝓝 (d (n + 1) x (Fin.snoc a h))))

/-- PDF pp. 3--4: finite-order smoothness in the actual manifold atlas. -/
def BastianiCkMap {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    (k : ℕ) (f : M → F) : Prop :=
  ∀ c ∈ atlas E M, BastianiCkOn k c.target (fun x => f (c.symm x))

/-- Sanity: the zero map has a derivative tower at every finite order,
including k=0, over a possibly nonnormable model. -/
example (k : ℕ) (U : Set E) : BastianiCkOn k U (fun _ => (0 : F)) := by
  refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
  · intro x hx
    rfl
  · intro n hn
    exact continuousOn_const
  · intro n hn x hx a h
    simpa only [sub_self, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

end FiniteCalculus

section LieData

variable (E : Type u) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable (G : Type v) [Group G] [TopologicalSpace G] [ChartedSpace E G]

/-- PDF p. 4: a locally convex smooth group with its actual exponential
function. The Lie algebra is the identity tangent space identified with E
by chartAt E 1; the last field fixes that identification, rather than
allowing an unrelated one-parameter-subgroup parametrization. Hausdorff
locally convex model assumptions are carried by theorem binders. -/
structure ExponentialLieData where
  atlasSmooth : BastianiAtlas (E := E) (M := G)
  multiplicationSmooth : DirectionalManifoldSmooth (E := E × E) (F := E)
    (fun p : G × G => p.1 * p.2)
  inversionSmooth : DirectionalManifoldSmooth (E := E) (F := E)
    (fun g : G => g⁻¹)
  exponential : E → G
  exponentialSmooth : DirectionalManifoldSmooth (E := E) (F := E) exponential
  exponentialZero : exponential 0 = 1
  exponentialAdd : ∀ (x : E) (s t : ℝ),
    exponential ((s + t) • x) = exponential (s • x) * exponential (t • x)
  exponentialTangent : ∀ x : E,
    Tendsto (fun t : ℝ => t⁻¹ •
      (chartAt E (1 : G) (exponential (t • x)) - chartAt E (1 : G) 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 x)

/-- Sanity: exponential curves obey the source's one-parameter-group law. -/
example (L : ExponentialLieData E G) (x : E) (s t : ℝ) :
    L.exponential ((s + t) • x) =
      L.exponential (s • x) * L.exponential (t • x) := L.exponentialAdd x s t

end LieData

section DerivedAction

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {G : Type v}
variable {V : Type w} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

/-- Definition 1.1(b), PDF p. 4: graph of the actual infinitesimal
generator, via a punctured real derivative at zero. -/
def HasGeneratorValue (expG : E → G) (action : G → V → V)
    (x : E) (v w : V) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (action (expG (t • x)) v - v))
    (𝓝[≠] (0 : ℝ)) (𝓝 w)

/-- Definition 1.1(b), PDF p. 4: domain of the actual generator. -/
def GeneratorDomain (expG : E → G) (action : G → V → V) (x : E) : Set V :=
  {v | ∃ w, HasGeneratorValue expG action x v w}

/-- Definition 1.1(b), PDF p. 4: the generator value chosen from its
limit graph. Its off-domain value is zero, never used without a domain
guard in an operator-domain assertion. In Hausdorff targets the on-domain
value is uniquely determined. -/
noncomputable def infinitesimalGeneratorValue (expG : E → G) (action : G → V → V)
    (x : E) (v : V) : V := by
  classical
  exact if h : v ∈ GeneratorDomain expG action x then Classical.choose h else 0

/-- Definition 1.1, PDF pp. 4--5: ordered products, with the rightmost
generator applied first. The empty word acts as the identity. -/
noncomputable def derivedWord (expG : E → G) (action : G → V → V) : List E → V → V
  | [], v => v
  | x :: xs, v => infinitesimalGeneratorValue expG action x (derivedWord expG action xs v)

/-- Definition 1.1, PDF pp. 4--5: recursive domains of actual operator
compositions. This prevents zero defaults from enlarging D^n. -/
def WordDomain (expG : E → G) (action : G → V → V) : List E → V → Prop
  | [], _ => True
  | x :: xs, v => WordDomain expG action xs v ∧
      derivedWord expG action xs v ∈ GeneratorDomain expG action x

/-- Definition 1.1, PDF p. 4: common domain of all words of length n. -/
def DerivedDomain (expG : E → G) (action : G → V → V) (n : ℕ) : Set V :=
  {v | ∀ xs : List E, xs.length = n → WordDomain expG action xs v}

/-- Definition 1.1, PDF p. 4: the common domain of every finite word. -/
def DerivedInfinity (expG : E → G) (action : G → V → V) : Set V :=
  {v | ∀ xs : List E, WordDomain expG action xs v}

/-- Definition 1.1, PDF p. 5: omega_v^n with its ordered n-tuple. -/
noncomputable def derivedTupleValue (expG : E → G) (action : G → V → V)
    (n : ℕ) (v : V) (xs : Fin n → E) : V :=
  derivedWord expG action (List.ofFn xs) v

/-- Sanity: no generator is applied in the empty product. -/
example (expG : E → G) (action : G → V → V) (v : V) :
    derivedWord expG action [] v = v ∧ WordDomain expG action [] v := by
  exact ⟨rfl, trivial⟩

/-- Sanity: off-domain generator values are explicitly zero. -/
example (expG : E → G) (action : G → V → V) (x : E) (v : V)
    (h : v ∉ GeneratorDomain expG action x) : infinitesimalGeneratorValue expG action x v = 0 := by
  simp [infinitesimalGeneratorValue, h]

end DerivedAction

section VectorCriteria

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [hETopAdd : IsTopologicalAddGroup E] [hESmul : ContinuousSMul ℝ E]
variable [hELocConv : LocallyConvexSpace ℝ E] [hET2 : T2Space E]
variable {G : Type v} [Group G] [TopologicalSpace G] [hGT2 : T2Space G]
variable [ChartedSpace E G]
variable {V : Type w} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
variable [hVTopAdd : IsTopologicalAddGroup V] [hVSmul : ContinuousSMul ℝ V]
variable [hVLocConv : LocallyConvexSpace ℝ V] [hVT2 : T2Space V]

/-- Definition 1.1(a), PDF p. 4: smooth vectors of the given action. -/
def SmoothVectors (action : G → V → V) : Set V :=
  {v | BastianiSmoothMap (E := E) (fun g => action g v)}

/-- Definition 1.1 and Theorem 1.1(i), PDF pp. 4--7: the finite C^k
criterion, expressed in the ambient target topology. The definition also
supports order zero, with no positive-order derivative requirement. -/
def VectorCriterion (L : ExponentialLieData E G) (action : G → V → V)
    (k : ℕ) (v : V) : Prop :=
  BastianiCkMap (E := E) k (fun g => action g v) ↔
    v ∈ DerivedDomain L.exponential action k ∧
      ∀ n, 0 < n → n ≤ k → Continuous (derivedTupleValue L.exponential action n v)

variable {K : Type z} [RCLike K] [Module K V] [hTower : IsScalarTower ℝ K V]
variable [hKSmul : ContinuousSMul K V]

/-- Definition 1.3, PDF p. 5: weak integrals of all continuous curves
on [0,1], tested by every continuous K-linear functional. No Banach or
Bochner-integrability assumption replaces integral completeness. -/
def IntegralComplete : Prop :=
  ∀ f : ℝ → V, ContinuousOn f (Set.Icc 0 1) →
    ∃ w : V, ∀ a : V →L[K] K, a w = ∫ t in (0 : ℝ)..1, a (f t)

/-- Definition 1.2, PDF p. 5: weak-star C^1 functionals separate points.
The scalar coefficient maps use the actual action; inverse pullback in
the contragredient representation gives exactly the same C^1 condition. -/
def WeakC1Separates (action : G → V → V) : Prop :=
  ∀ v : V, v ≠ 0 → ∃ a : V →L[K] K, a v ≠ 0 ∧
    ∀ w : V, BastianiCkMap (E := E) 1 (fun g => a (action g w))

/-- Sanity: the zero space satisfies integral completeness. -/
example [Subsingleton V] : IntegralComplete (K := K) (V := V) := by
  intro f hf
  refine ⟨0, ?_⟩
  intro a
  have hz : ∀ t : ℝ, a (f t) = 0 := fun t => by
    rw [Subsingleton.elim (f t) 0, map_zero]
  simp only [map_zero, hz, intervalIntegral.integral_zero]

include hETopAdd hESmul hELocConv hET2 hGT2
  hVTopAdd hVSmul hVLocConv hVT2 hTower hKSmul

end VectorCriteria

section HilbertOperators

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [hETopAdd : IsTopologicalAddGroup E] [hESmul : ContinuousSMul ℝ E]
variable [hELocConv : LocallyConvexSpace ℝ E] [hET2 : T2Space E]
variable {G : Type v} [Group G] [TopologicalSpace G] [hGT2 : T2Space G]
variable [ChartedSpace E G]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [hHComplete : CompleteSpace H]

/-- PDF pp. 4,7: a unitary represented as a bounded complex-linear map,
with the operator norm on B(H). -/
def unitaryOperator (pi : G →* (H ≃ₗᵢ[ℂ] H)) (g : G) : H →L[ℂ] H :=
  (pi g).toLinearIsometry.toContinuousLinearMap

/-- Definition 2.1, PDF p. 7: smoothing means that the entire range is
contained in the smooth-vector space, not just in the common generator domain. -/
def IsSmoothing (pi : G →* (H ≃ₗᵢ[ℂ] H)) (A : H →L[ℂ] H) : Prop :=
  ∀ v : H, A v ∈ SmoothVectors (E := E) (fun g v => pi g v)

/-- Corollary 1.1(i), PDF p. 7: the actual left action on operators. -/
def leftAction (pi : G →* (H ≃ₗᵢ[ℂ] H)) (g : G) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (unitaryOperator pi g).comp A

/-- Corollary 1.1(ii), PDF p. 7: the two-sided action, with inverse
in the second variable. -/
def alphaAction (pi : G →* (H ≃ₗᵢ[ℂ] H)) (p : G × G)
    (A : H →L[ℂ] H) : H →L[ℂ] H :=
  ((unitaryOperator pi p.1).comp A).comp (unitaryOperator pi p.2⁻¹)

/-- Lemma 2.3, PDF p. 10: right multiplication by pi(g) inverse. -/
def rightInverseOperatorAction (pi : G →* (H ≃ₗᵢ[ℂ] H)) (g : G) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  A.comp (unitaryOperator pi g⁻¹)

/-- Theorem 2.1, PDF pp. 10--11: a concrete representative of an element
of the complex enveloping algebra is a finite complex linear combination
of words in real Lie-algebra elements. All such representatives are used;
the representation factors through the usual enveloping relations. -/
noncomputable def derivedPolynomial (L : ExponentialLieData E G)
    (pi : G →* (H ≃ₗᵢ[ℂ] H)) (D : List (ℂ × List E)) (v : H) : H :=
  (D.map (fun term => term.1 •
    derivedWord L.exponential (fun g v => pi g v) term.2 v)).sum

/-- Theorem 2.1(v), PDF p. 10: A* d pi(D) bounded on the actual dense
space of smooth vectors. Each constant may depend on D and A, not on v. -/
def AdjointDerivedBounded (L : ExponentialLieData E G)
    (pi : G →* (H ≃ₗᵢ[ℂ] H)) (A : H →L[ℂ] H) : Prop :=
  ∀ D : List (ℂ × List E), ∃ C : ℝ, 0 ≤ C ∧
    ∀ v ∈ SmoothVectors (E := E) (fun g v => pi g v),
      ‖A.adjoint (derivedPolynomial L pi D v)‖ ≤ C * ‖v‖

/-- Theorem 2.1, final clause, PDF p. 10: boundedness of d pi(D) A
on all of H, with a uniform bound for each D. On smoothing ranges all
word-domain requirements are fulfilled, so off-domain defaults are irrelevant. -/
def DerivedAfterBounded (L : ExponentialLieData E G)
    (pi : G →* (H ≃ₗᵢ[ℂ] H)) (A : H →L[ℂ] H) : Prop :=
  ∀ D : List (ℂ × List E), ∃ C : ℝ, 0 ≤ C ∧
    ∀ v : H, ‖derivedPolynomial L pi D (A v)‖ ≤ C * ‖v‖

/-- Sanity: the zero enveloping expression acts as zero. -/
example (L : ExponentialLieData E G) (pi : G →* (H ≃ₗᵢ[ℂ] H)) (v : H) :
    derivedPolynomial L pi [] v = 0 := rfl

/-- Sanity: the range condition for the identity is exactly all vectors
being smooth; no finite-dimensional Hilbert-space assumption is present. -/
example (pi : G →* (H ≃ₗᵢ[ℂ] H)) :
    IsSmoothing (E := E) pi (ContinuousLinearMap.id ℂ H) ↔
      ∀ v : H, v ∈ SmoothVectors (E := E) (fun g v => pi g v) := Iff.rfl

include hETopAdd hESmul hELocConv hET2 hGT2 hHComplete

end HilbertOperators

section PartialOperators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 2.1, PDF p. 9: boundedness on an operator's given domain,
with the norm induced from H; it does not mean a bound in the graph norm. -/
def PMapBounded (B : H →ₗ.[ℂ] H) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ v : B.domain, ‖B v‖ ≤ C * ‖(v : H)‖

/-- Sanity: zero on any domain is bounded, including a nonclosed domain. -/
example (D : Submodule ℂ H) : PMapBounded ((0 : H →ₗ[ℂ] H).toPMap D) := by
  refine ⟨0, le_rfl, ?_⟩
  intro v
  change ‖(0 : H)‖ ≤ 0 * ‖(v : H)‖
  simp

end PartialOperators

end QAlgorithms.Papers.Independent.Gap48.P05


