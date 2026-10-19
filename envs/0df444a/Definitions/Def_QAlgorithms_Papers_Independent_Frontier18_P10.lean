-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10
-- name    : QAlgorithms_Papers_Independent_Frontier18_P10
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:01:41.619987+00:00
-- url     : https://prove2.me/theorems/71ee1e5b-3e52-4c24-a3b5-3ec9550b7d1e
-- title:
--   Definitions for Generalized compactness in linear spaces and its applications
-- statement:
--   The objects the formalized statements of *Generalized compactness in linear spaces and its applications* (arXiv:1002.3610) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsPettisBarycenter`: §2.1, PDF p.3, (1): scalar characterization of the Pettis integral of inclusion. Scalar integrability is explicit, so no default-zero integral can serve as a barycenter. In the source-admissible class this point exists uniquely.
--   - `pettisBarycenter`: §2.1, PDF pp.3–4: the actual Pettis barycenter, selected from its scalar characterization, not a freely supplied map. The outside-domain default zero is never used on source-admissible sets. It permits the definition without assuming a probability measure exists on an empty domain.
--   - `MuCompact`: Definition 1, PDF p.4: compact inverse images under the Pettis barycenter. The target is the closed convex hull, including when A is nonconvex.
--   - `PointwiseMuCompact`: Definition 2, PDF p.7: every fiber over the closed convex hull is compact.
--   - `BoundedContinuousOn`: §2.1, PDF p.3: bounded continuous real-valued test functions on A. Values outside A are immaterial; every function on A has an ambient extension.
--   - `convexHullFunction`: §2.1, PDF p.3: the greatest convex minorant, with extended values. This supremum is in EReal, so empty or unbounded collections are not totalized real suprema. It is not the lower semicontinuous convex envelope.
--   - `closedConvexHullFunction`: §2.1, PDF p.3: the greatest lower semicontinuous convex minorant, with lower semicontinuity in the subspace topology of A.
--   - `StableConvexSet`: Theorem 1(i), PDF p.14: openness of midpoint mixing into A. Using the relative image avoids a chosen proof that a midpoint belongs to A.
--   - `BarycenterOpen`: Theorem 1(ii)–(iii), PDF p.14: openness of b:M(B)→A, in the weak probability topology and the target subspace topology. On the stated domains b takes values in A; no ambient-open-image condition is imposed.
--   - `StrongCEProperty`: Theorem 1(iv), PDF p.14: the strong CE-property.
--   - `CEProperty`: Theorem 1(v), PDF p.14: the CE-property tests bounded continuous concave functions.
--   - `NonnegativeConcaveOn`: Proposition 2, PDF pp.4–5: extended nonnegative concavity, with zero weights annihilating infinity also at the endpoints.
--   - `CoerciveConcaveFamily`: Proposition 2, PDF pp.4–5: relatively compact sublevels and one finite bound on each compact K. Neither finite-valuedness nor lsc is imposed.
--   - `CountableTightness`: Proposition 1, PDF p.4: finite and countable normalized decompositions. Finite ensembles are represented by zero padding. Vector convergence is a HasSum assertion, not an unchecked totalized vector tsum.
--   - `FiniteEnsemble`: §2.1, PDF pp.3–4: finite ensemble, including the impossible zero-length normalized ensemble rather than assigning its mean an artificial value.
--   - `finiteMean`: §2.1, PDF p.4: the barycenter of a finite ensemble.
--   - `finiteCost`: Corollary 2, PDF p.8: finite weighted real cost, embedded into EReal.
--   - `ChoquetLE`: Choquet order, PDF p.7: integration against P(A), increasing in spread.
--   - `AffineOnSet`: Proposition 3, PDF p.5: affine equality on the source set only.
--   - `GeneralizedMuCompact`: §5, PDF pp.20–21: generalized µ-compactness, using finite convex combinations and mass at least 1−epsilon inside one compact set. This definition also applies to unbounded closed convex sets and uses no all-measures barycenter.
--   - `IsPointedCone`: Lemma 3, PDF p.21: a cone based at zero, containing no affine line.
--   - `GeneralBarycenterSpace`: §2.1 standing class, PDF p.3 and footnote 1: closed and locally-convex (von Neumann) bounded, with complete, separable, metrizable closed convex hull in the induced additive uniformity. No normability of the ambient space is assumed.
--   - `positiveLpUnitPart`: Propositions 9 and 15, PDF pp.10,13: positive closed unit part in countably infinite real l^p, with its norm topology.
--   - `subprobabilitySimplex`: Proposition 13, PDF p.12: the subprobability simplex in the l^p norm topology. The nonnegative coordinate sum is in ENNReal; a nonsummable sequence cannot enter through a default-zero real tsum.
--   - `countableProbabilitySimplex`: Corollary 3, PDF p.10: distributions have total mass one, not at most one.
--   - `normDefect`: Example 1, PDF p.13: the explicit norm-subscript-p cost.
--   - `finiteMeasureCoordinates`: Propositions 10 and Corollary 4, PDF p.11: coordinates of a finite nonnegative Borel measure against bounded continuous real test functions. Boundedness and finite mass ensure these integrals exist.
--   - `weakMeasureSpace`: PDF p.11: the linear ambient realization of finite signed measures, with weak topology inherited from real integration coordinates. Taking the linear span, rather than the whole coordinate product, keeps actual measures as the ambient objects and does not add Stone–Cech boundary functionals.
--   - `weakFiniteMeasure`: PDF p.11: actual finite Borel measure embedded in its weak linear ambient.
--   - `weakProbabilityMeasure`: Corollary 4, PDF p.11: normalized probability in the same ambient.
--   - `weakProbabilitySet`: Corollary 4, PDF p.11: all Borel probabilities, with their genuine weak linear structure and topology, represented in the signed-measure ambient.
--   - `diracPoint`: Remark 2, PDF p.6: the nonconvex set of single-atomic probability laws.
--   - `LiftedSubnetProperty`: Lemma 6, PDF p.24: the subnet condition uses eventual cofinality of its index map to Nat. The directed index type need not be countable, and no continuity or surjectivity of phi is assumed.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, https://arxiv.org/abs/1002.3610v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P25

/-!
# Generalized compactness in linear spaces

Protasov–Shirokov, arXiv:1002.3610v3. All numbered source results below are
statements only. The accepted P25 definitions of extended convexity and
extended integration are reused; its Banach barycenter is not substituted
for the present locally convex Pettis barycenter. Deferred nodes are recorded
in the paper unit's HARD.md and GAPS.json. Compilation is pending batch handoff.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

/-- §2.1, PDF p.3: every probability law uses the Borel sigma algebra. -/
local instance paperMeasurable (X : Type*) [TopologicalSpace X] : MeasurableSpace X :=
  borel X

local instance paperBorel (X : Type*) [TopologicalSpace X] : BorelSpace X :=
  ⟨rfl⟩

section Definitions

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- §2.1, PDF p.3, (1): scalar characterization of the Pettis integral of
inclusion. Scalar integrability is explicit, so no default-zero integral can
serve as a barycenter. In the source-admissible class this point exists uniquely. -/
def IsPettisBarycenter (A : Set E) (mu : ProbabilityMeasure A) (x : E) : Prop :=
  ∀ l : E →L[ℝ] ℝ,
    Integrable (fun y : A => l (y : E)) (mu : Measure A) ∧
    l x = ∫ y : A, l (y : E) ∂(mu : Measure A)

/-- §2.1, PDF pp.3–4: the actual Pettis barycenter, selected from its scalar
characterization, not a freely supplied map. The outside-domain default zero
is never used on source-admissible sets. It permits the definition without
assuming a probability measure exists on an empty domain. -/
def pettisBarycenter (A : Set E) (mu : ProbabilityMeasure A) : E := by
  classical
  exact
    if h : ∃ x : E, IsPettisBarycenter A mu x then Classical.choose h else 0

/-- Definition 1, PDF p.4: compact inverse images under the Pettis barycenter.
The target is the closed convex hull, including when A is nonconvex. -/
def MuCompact (A : Set E) : Prop :=
  ∀ K : Set E, K ⊆ closedConvexHull ℝ A → IsCompact K →
    IsCompact {mu : ProbabilityMeasure A | pettisBarycenter A mu ∈ K}

/-- Definition 2, PDF p.7: every fiber over the closed convex hull is compact. -/
def PointwiseMuCompact (A : Set E) : Prop :=
  ∀ x ∈ closedConvexHull ℝ A,
    IsCompact {mu : ProbabilityMeasure A | pettisBarycenter A mu = x}

/-- §2.1, PDF p.3: bounded continuous real-valued test functions on A.
Values outside A are immaterial; every function on A has an ambient extension. -/
def BoundedContinuousOn (A : Set E) (f : E → ℝ) : Prop :=
  ContinuousOn f A ∧ ∃ M : ℝ, ∀ x ∈ A, |f x| ≤ M

/-- §2.1, PDF p.3: the greatest convex minorant, with extended values.
This supremum is in EReal, so empty or unbounded collections are not totalized
real suprema. It is not the lower semicontinuous convex envelope. -/
def convexHullFunction (A : Set E) (f : E → EReal) (x : E) : EReal :=
  sSup {r | ∃ g : E → EReal, extendedConvexOn A g ∧
    (∀ y ∈ A, g y ≤ f y) ∧ r = g x}

/-- §2.1, PDF p.3: the greatest lower semicontinuous convex minorant,
with lower semicontinuity in the subspace topology of A. -/
def closedConvexHullFunction (A : Set E) (f : E → EReal) (x : E) : EReal :=
  sSup {r | ∃ g : E → EReal, extendedConvexOn A g ∧
    LowerSemicontinuous (fun y : A => g y) ∧
    (∀ y ∈ A, g y ≤ f y) ∧ r = g x}

/-- Theorem 1(i), PDF p.14: openness of midpoint mixing into A. Using the
relative image avoids a chosen proof that a midpoint belongs to A. -/
def StableConvexSet (A : Set E) : Prop :=
  ∀ U : Set (A × A), IsOpen U →
    IsOpen {z : A | ∃ p ∈ U,
      (z : E) = (1 / 2 : ℝ) • (p.1 : E) + (1 / 2 : ℝ) • (p.2 : E)}

/-- Theorem 1(ii)–(iii), PDF p.14: openness of b:M(B)→A, in the weak
probability topology and the target subspace topology. On the stated domains
b takes values in A; no ambient-open-image condition is imposed. -/
def BarycenterOpen (A B : Set E) : Prop :=
  ∀ U : Set (ProbabilityMeasure B), IsOpen U →
    IsOpen {x : A | ∃ mu ∈ U, pettisBarycenter B mu = (x : E)}

/-- Theorem 1(iv), PDF p.14: the strong CE-property. -/
def StrongCEProperty (A : Set E) : Prop :=
  ∀ f : E → ℝ, BoundedContinuousOn A f →
    Continuous (fun x : A => convexHullFunction A (fun y => (f y : EReal)) x)

/-- Theorem 1(v), PDF p.14: the CE-property tests bounded continuous concave functions. -/
def CEProperty (A : Set E) : Prop :=
  ∀ f : E → ℝ, BoundedContinuousOn A f → ConcaveOn ℝ A f →
    Continuous (fun x : A => convexHullFunction A (fun y => (f y : EReal)) x)

/-- Proposition 2, PDF pp.4–5: extended nonnegative concavity, with zero
weights annihilating infinity also at the endpoints. -/
def NonnegativeConcaveOn (A : Set E) (f : E → ℝ≥0∞) : Prop :=
  Convex ℝ A ∧ ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ,
    0 ≤ a → 0 ≤ b → a + b = 1 →
    ENNReal.ofReal a * f x + ENNReal.ofReal b * f y ≤ f (a • x + b • y)

/-- Proposition 2, PDF pp.4–5: relatively compact sublevels and one finite
bound on each compact K. Neither finite-valuedness nor lsc is imposed. -/
def CoerciveConcaveFamily (A : Set E) (F : Set (E → ℝ≥0∞)) : Prop :=
  (∀ f ∈ F, NonnegativeConcaveOn A f ∧
    ∀ c : ℝ, 0 < c → IsCompact (closure {x ∈ A | f x ≤ ENNReal.ofReal c})) ∧
  ∀ K : Set E, K ⊆ A → IsCompact K →
    ∃ f ∈ F, ∃ C : ℝ, ∀ x ∈ K, f x ≤ ENNReal.ofReal C

/-- Proposition 1, PDF p.4: finite and countable normalized decompositions.
Finite ensembles are represented by zero padding. Vector convergence is a
HasSum assertion, not an unchecked totalized vector tsum. -/
def CountableTightness (A : Set E) : Prop := by
  classical
  exact
    ∀ K : Set E, K ⊆ A → IsCompact K → ∀ epsilon : ℝ, 0 < epsilon →
      ∃ L : Set E, L ⊆ A ∧ IsCompact L ∧
        ∀ x ∈ K, ∀ (weight : ℕ → ℝ) (point : ℕ → E),
          (∀ i, 0 ≤ weight i) → HasSum weight 1 → (∀ i, point i ∈ A) →
          HasSum (fun i => weight i • point i) x →
          (∑' i, if point i ∉ L then ENNReal.ofReal (weight i) else 0) <
            ENNReal.ofReal epsilon

/-- §2.1, PDF pp.3–4: finite ensemble, including the impossible zero-length
normalized ensemble rather than assigning its mean an artificial value. -/
structure FiniteEnsemble (A : Set E) where
  size : ℕ
  weight : Fin size → ℝ
  point : Fin size → E
  nonnegative : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1
  mem : ∀ i, point i ∈ A

/-- §2.1, PDF p.4: the barycenter of a finite ensemble. -/
def finiteMean {A : Set E} (e : FiniteEnsemble A) : E :=
  ∑ i, e.weight i • e.point i

/-- Corollary 2, PDF p.8: finite weighted real cost, embedded into EReal. -/
def finiteCost {A : Set E} (f : E → ℝ) (e : FiniteEnsemble A) : EReal :=
  ((∑ i, e.weight i * f (e.point i) : ℝ) : EReal)

/-- Choquet order, PDF p.7: integration against P(A), increasing in spread. -/
def ChoquetLE (A : Set E) (mu nu : ProbabilityMeasure A) : Prop :=
  ∀ f : E → ℝ, BoundedContinuousOn A f → ConvexOn ℝ A f →
    (∫ x : A, f x ∂(mu : Measure A)) ≤ ∫ x : A, f x ∂(nu : Measure A)

/-- Proposition 3, PDF p.5: affine equality on the source set only. -/
def AffineOnSet {F : Type*} [AddCommGroup F] [Module ℝ F]
    (A : Set E) (phi : E → F) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ,
    0 ≤ a → 0 ≤ b → a + b = 1 →
    phi (a • x + b • y) = a • phi x + b • phi y

/-- §5, PDF pp.20–21: generalized µ-compactness, using finite convex
combinations and mass at least 1−epsilon inside one compact set. This definition
also applies to unbounded closed convex sets and uses no all-measures barycenter. -/
def GeneralizedMuCompact (A : Set E) : Prop := by
  classical
  exact
    Convex ℝ A ∧ IsClosed A ∧
      ∀ K : Set E, K ⊆ A → IsCompact K → ∀ epsilon : ℝ, 0 < epsilon →
        ∃ L : Set E, L ⊆ A ∧ IsCompact L ∧
          ∀ e : FiniteEnsemble A, finiteMean e ∈ K →
            1 - epsilon ≤ ∑ i, if e.point i ∈ L then e.weight i else 0

/-- Lemma 3, PDF p.21: a cone based at zero, containing no affine line. -/
def IsPointedCone (C : Set E) : Prop :=
  (0 : E) ∈ C ∧ Convex ℝ C ∧
    (∀ a : ℝ, 0 ≤ a → ∀ x ∈ C, a • x ∈ C) ∧
    ∀ x ∈ C, -x ∈ C → x = 0

example (A : Set E) (hA : Convex ℝ A) :
    NonnegativeConcaveOn A (fun _ => 0) := by
  refine ⟨hA, ?_⟩
  intro x hx y hy a b ha hb hab
  simp

example [T2Space E] (A : Set E) (x : A) :
    IsPettisBarycenter A (⟨Measure.dirac x, inferInstance⟩ : ProbabilityMeasure A) x := by
  intro l
  simp [integrable_dirac]

example (A : Set E) (x : E) (hx : x ∈ A) :
    finiteMean (⟨1, fun _ => 1, fun _ => x, by simp, by simp,
      fun _ => hx⟩ : FiniteEnsemble A) = x := by
  simp [finiteMean]

example (A : Set E) (mu : ProbabilityMeasure A) : ChoquetLE A mu mu := by
  intro f hf hc
  exact le_rfl

example : GeneralizedMuCompact (∅ : Set E) := by
  refine ⟨convex_empty, isClosed_empty, ?_⟩
  intro K hK hcompact epsilon hepsilon
  refine ⟨∅, Subset.rfl, isCompact_empty, ?_⟩
  intro e he
  exact False.elim (hK he)

end Definitions

/-- §2.1 standing class, PDF p.3 and footnote 1: closed and locally-convex
(von Neumann) bounded, with complete, separable, metrizable closed convex hull
in the induced additive uniformity. No normability of the ambient space is assumed. -/
def GeneralBarycenterSpace {E : Type*} [UniformSpace E] [AddCommGroup E]
    [Module ℝ E] (A : Set E) : Prop :=
  IsClosed A ∧ Bornology.IsVonNBounded ℝ A ∧
    IsComplete (closedConvexHull ℝ A) ∧ IsSeparable (closedConvexHull ℝ A) ∧
    MetrizableSpace (closedConvexHull ℝ A)

section LocallyConvexResults

variable {E : Type u} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
    [hgroup : IsUniformAddGroup E] [hsmul : ContinuousSMul ℝ E]
    [hlc : LocallyConvexSpace ℝ E] [hhaus : T2Space E]

include hgroup hsmul hlc hhaus

end LocallyConvexResults

section HilbertResults

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [hcomplete : CompleteSpace H]

include hcomplete

end HilbertResults

section LpResults

/-- Propositions 9 and 15, PDF pp.10,13: positive closed unit part in
countably infinite real l^p, with its norm topology. -/
def positiveLpUnitPart (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (lp (fun _ : ℕ => ℝ) p) :=
  {x | (∀ i, 0 ≤ x i) ∧ ‖x‖ ≤ 1}

/-- Proposition 13, PDF p.12: the subprobability simplex in the l^p norm
topology. The nonnegative coordinate sum is in ENNReal; a nonsummable sequence
cannot enter through a default-zero real tsum. -/
def subprobabilitySimplex (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Set (lp (fun _ : ℕ => ℝ) p) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑' i, ENNReal.ofReal (x i)) ≤ 1}

/-- Corollary 3, PDF p.10: distributions have total mass one, not at most one. -/
def countableProbabilitySimplex : Set (lp (fun _ : ℕ => ℝ) 1) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑' i, ENNReal.ofReal (x i)) = 1}

/-- Example 1, PDF p.13: the explicit norm-subscript-p cost. -/
def normDefect (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : lp (fun _ : ℕ => ℝ) p) : ℝ :=
  1 - ‖x‖

example (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (0 : lp (fun _ : ℕ => ℝ) p) ∈ subprobabilitySimplex p := by
  simp [subprobabilitySimplex]

example (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    normDefect p (0 : lp (fun _ : ℕ => ℝ) p) = 1 := by
  simp [normDefect]

end LpResults

section WeakMeasures

variable {X : Type u} [TopologicalSpace X]

/-- Propositions 10 and Corollary 4, PDF p.11: coordinates of a finite
nonnegative Borel measure against bounded continuous real test functions.
Boundedness and finite mass ensure these integrals exist. -/
def finiteMeasureCoordinates (mu : FiniteMeasure X) : (BoundedContinuousFunction X ℝ) → ℝ :=
  fun f => ∫ x, f x ∂(mu : Measure X)

/-- PDF p.11: the linear ambient realization of finite signed measures,
with weak topology inherited from real integration coordinates. Taking the
linear span, rather than the whole coordinate product, keeps actual measures
as the ambient objects and does not add Stone–Cech boundary functionals. -/
def weakMeasureSpace (X : Type u) [TopologicalSpace X] :
    Submodule ℝ ((BoundedContinuousFunction X ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (finiteMeasureCoordinates (X := X)))

/-- PDF p.11: actual finite Borel measure embedded in its weak linear ambient. -/
def weakFiniteMeasure (mu : FiniteMeasure X) : weakMeasureSpace X :=
  ⟨finiteMeasureCoordinates mu, Submodule.subset_span (Set.mem_range_self mu)⟩

/-- Corollary 4, PDF p.11: normalized probability in the same ambient. -/
def weakProbabilityMeasure (mu : ProbabilityMeasure X) : weakMeasureSpace X :=
  weakFiniteMeasure mu.toFiniteMeasure

/-- Corollary 4, PDF p.11: all Borel probabilities, with their genuine weak
linear structure and topology, represented in the signed-measure ambient. -/
def weakProbabilitySet (X : Type u) [TopologicalSpace X] : Set (weakMeasureSpace X) :=
  Set.range (weakProbabilityMeasure (X := X))

/-- Remark 2, PDF p.6: the nonconvex set of single-atomic probability laws. -/
def diracPoint (x : X) : weakMeasureSpace X :=
  weakProbabilityMeasure (⟨Measure.dirac x, inferInstance⟩ : ProbabilityMeasure X)

example [T2Space X] (x : X) (f : BoundedContinuousFunction X ℝ) :
    finiteMeasureCoordinates (⟨Measure.dirac x, inferInstance⟩ : FiniteMeasure X) f = f x := by
  simp [finiteMeasureCoordinates]

example (mu : FiniteMeasure X) :
    (weakFiniteMeasure mu).val = finiteMeasureCoordinates mu := rfl

example (x : X) : diracPoint x ∈ weakProbabilitySet X := by
  exact ⟨⟨Measure.dirac x, inferInstance⟩, rfl⟩

end WeakMeasures

/-- Lemma 6, PDF p.24: the subnet condition uses eventual cofinality of
its index map to Nat. The directed index type need not be countable, and no
continuity or surjectivity of phi is assumed. -/
def LiftedSubnetProperty {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] (phi : X → Y) : Prop :=
  ∀ x0 : X, ∀ y : ℕ → Y, Tendsto y atTop (𝓝 (phi x0)) →
    ∃ (D : Type (max u v)) (order : Preorder D),
      letI : Preorder D := order
      ∃ (_ : Nonempty D) (_ : IsDirectedOrder D) (index : D → ℕ) (x : D → X),
        Tendsto index atTop atTop ∧ Tendsto x atTop (𝓝 x0) ∧
        ∀ d, phi (x d) = y (index d)

example {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    [IsEmpty X] (phi : X → Y) : LiftedSubnetProperty phi := by
  intro x0
  exact isEmptyElim x0

end QAlgorithms.Papers.Independent.Frontier18.P10


