-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25
-- name    : QAlgorithms_Papers_Independent_Next46_P25
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:57:29.504384+00:00
-- url     : https://prove2.me/theorems/acfc4aa3-fdee-4c98-b511-40888be8c7dd
-- title:
--   Definitions for On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups
-- statement:
--   The objects the formalized statements of *On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups* (arXiv:1002.4792) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `StronglyContinuous`: Definition 4.1, PDF p.14: continuity in the Lie algebra variable for each fixed vector; this does not require continuous individual operators.
--   - `wordAction`: Lemma 4.4, PDF p.15: ordered application, with the last variable acting first on the vector. The empty word acts as the identity.
--   - `SeparatelyContinuous`: Separate continuity for a finite product, including the empty product; Proposition 4.3 and Lemma 4.4, PDF p.15.
--   - `envelopingWord`: Definition 3.2, PDF p.9: the ordered word in the actual real universal enveloping algebra; the zeroth word is 1.
--   - `ContinuousFunctional`: Definition 3.2(a), PDF p.9: continuity of every word-multilinear map, without putting an artificial norm topology on U(g).
--   - `symmetrizedWord`: Definition 3.1(b), PDF p.8: symmetrization averages over all n! permutations, with the factor also present at n = 0.
--   - `symmetricSeminorm`: Definition 3.1(a), PDF p.8: an extended nonnegative seminorm. A p-unit ball can be unbounded, in which case this supremum is infinity.
--   - `FiniteSymmetricSeries`: Equations (4)--(5), PDF pp.9--10: finiteness of the nonnegative factorial-weighted series. This is never the default real sum of a nonsummable sequence. Only positive t occurs in radius definitions.
--   - `AnalyticFunctional`: Definition 3.2(b), PDF p.9: vector-series convergence on one zero-neighborhood, together with continuity of all word maps.
--   - `functionalRadius`: Definition 3.5, PDF p.10: the radius, including 0 for no positive radius and infinity for an entire functional.
--   - `PAnalytic`: Definition 3.5's operative union, PDF p.10. Printed: p-analytic means R < infinity. Changed: use R > 0, including infinity, as in the printed union of the fixed-positive-radius subspaces. Why: finite radius excludes zero and entire maps, contradicting that union.
--   - `AtRadius`: Definition 3.5, PDF p.10: the fixed-radius subspace, retaining the same p and r under both regular actions.
--   - `Submultiplicative`: Equation (1), PDF pp.7--8: submultiplicativity for the Lie bracket.
--   - `CompatibleBanachLieNorm`: Proposition 3.4's Banach specialization, PDF pp.8--10: a chosen norm expressed as a definite continuous seminorm inducing the given topology. Completeness uses the given compatible additive uniformity.
--   - `leftRegular`: Lemma 3.3, PDF p.9: left regular action, including its minus sign.
--   - `rightRegular`: Lemma 3.3, PDF p.9: right regular action, with no minus sign.
--   - `SubmultiplicativelyGenerated`: Remark 3.8(a), PDF pp.13--14: the continuous submultiplicative seminorms generate the topology. Finite maxima of such seminorms are again submultiplicative, giving this equivalent cofinal-ball formulation.
--   - `OperatorAnalytic`: Definition 4.7, PDF p.16: positive individual radius with ABSOLUTE norm summability. No convergence inside an incomplete invariant domain is required.
--   - `SimultaneouslyAnalytic`: Definition 4.9, PDF p.16: absolute norm summability for every x in ONE zero-neighborhood, which may depend on v. Strong continuity is a hypothesis on the representation wherever this is used.
--   - `ContinuousLieBracket`: Remark 6.13, PDF p.25: a continuous bilinear Lie bracket on a seminormed vector space. The additive and scalar operations are those of the given space, avoiding independent additive structures on a quotient. Definiteness and completeness are stated separately where required.
-- source:
--   On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups, arXiv:1002.4792v2, https://arxiv.org/abs/1002.4792v2

import Mathlib

/-!
Statements from K.-H. Neeb, arXiv:1002.4792v2.
Definitions here belong only to this paper. Deferred nodes and the unimplemented
locally convex analytic manifold/GNS interfaces are listed in HARD.md and GAPS.json.
Compilation is pending the batch mechanical handoff.
-/

noncomputable section

open Set Filter Topology
open scoped Classical ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Definition 4.1, PDF p.14: continuity in the Lie algebra variable for
    each fixed vector; this does not require continuous individual operators. -/
def StronglyContinuous {g : Type u} {V : Type v}
    [TopologicalSpace g] [TopologicalSpace V] (rho : g → V → V) : Prop :=
  ∀ v : V, Continuous (fun x : g => rho x v)

/-- Definition 4.1, PDF p.14: the zero action is strongly continuous. -/
example {g : Type u} {V : Type v} [TopologicalSpace g] [TopologicalSpace V]
    [Zero V] : StronglyContinuous (fun (_ : g) (_ : V) => (0 : V)) := by
  intro v
  exact continuous_const

/-- Lemma 4.4, PDF p.15: ordered application, with the last variable acting
    first on the vector. The empty word acts as the identity. -/
def wordAction {g : Type u} {V : Type v} (rho : g → V → V)
    (v : V) (n : ℕ) (xs : Fin n → g) : V :=
  (List.ofFn xs).foldr (fun x w => rho x w) v

/-- The zeroth word is the original vector, including for v = 0. -/
example {g : Type u} {V : Type v} (rho : g → V → V) (v : V)
    (xs : Fin 0 → g) : wordAction rho v 0 xs = v := by
  simp [wordAction]

/-- Separate continuity for a finite product, including the empty product;
    Proposition 4.3 and Lemma 4.4, PDF p.15. -/
def SeparatelyContinuous {k : ℕ} {F : Fin k → Type u} {V : Type v}
    [∀ i, TopologicalSpace (F i)] [TopologicalSpace V]
    (f : ((i : Fin k) → F i) → V) : Prop :=
  ∀ (xs : (i : Fin k) → F i) (i : Fin k),
    Continuous (fun y : F i => f (Function.update xs i y))

/-- Separate continuity has no coordinate conditions at k = 0. -/
example {F : Fin 0 → Type u} {V : Type v}
    [∀ i, TopologicalSpace (F i)] [TopologicalSpace V]
    (f : ((i : Fin 0) → F i) → V) : SeparatelyContinuous f := by
  intro xs i
  exact Fin.elim0 i

section Functionals

variable {g : Type u} [LieRing g] [LieAlgebra ℝ g]
variable [gUniform : UniformSpace g] [gAdd : IsUniformAddGroup g] [gHaus : T2Space g]
variable [gScalar : ContinuousSMul ℝ g] [gLC : LocallyConvexSpace ℝ g]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 3.2, PDF p.9: the ordered word in the actual real universal
    enveloping algebra; the zeroth word is 1. -/
def envelopingWord (n : ℕ) (xs : Fin n → g) : UniversalEnvelopingAlgebra ℝ g :=
  (List.ofFn (fun i => UniversalEnvelopingAlgebra.ι ℝ (xs i))).prod

/-- The empty word is the unit, so beta_0 = beta(1). -/
example (xs : Fin 0 → g) : envelopingWord 0 xs = 1 := by
  simp [envelopingWord]

/-- Definition 3.2(a), PDF p.9: continuity of every word-multilinear map,
    without putting an artificial norm topology on U(g). -/
def ContinuousFunctional (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E) : Prop :=
  ∀ n : ℕ, Continuous (fun xs : Fin n → g => beta (envelopingWord n xs))

/-- Definition 3.1(b), PDF p.8: symmetrization averages over all n!
    permutations, with the factor also present at n = 0. -/
def symmetrizedWord (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E)
    (n : ℕ) (xs : Fin n → g) : E :=
  (1 / (n.factorial : ℝ)) •
    ∑ sigma : Equiv.Perm (Fin n), beta (envelopingWord n (fun i => xs (sigma i)))

/-- Definition 3.1(a), PDF p.8: an extended nonnegative seminorm.
    A p-unit ball can be unbounded, in which case this supremum is infinity. -/
def symmetricSeminorm (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E)
    (p : Seminorm ℝ g) (n : ℕ) : ℝ≥0∞ :=
  ⨆ (xs : Fin n → g) (_ : ∀ i, p (xs i) ≤ 1),
    ENNReal.ofReal ‖symmetrizedWord beta n xs‖

/-- Equations (4)--(5), PDF pp.9--10: finiteness of the nonnegative
    factorial-weighted series. This is never the default real sum of a
    nonsummable sequence. Only positive t occurs in radius definitions. -/
def FiniteSymmetricSeries (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E)
    (p : Seminorm ℝ g) (t : ℝ) : Prop :=
  (∑' n : ℕ, symmetricSeminorm beta p n *
    ENNReal.ofReal (t ^ n / (n.factorial : ℝ))) < ⊤

/-- Definition 3.2(b), PDF p.9: vector-series convergence on one
    zero-neighborhood, together with continuity of all word maps. -/
def AnalyticFunctional (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E) : Prop :=
  ContinuousFunctional beta ∧ ∃ U : Set g, U ∈ 𝓝 (0 : g) ∧
    ∀ x ∈ U, Summable (fun n : ℕ => (1 / (n.factorial : ℝ)) •
      beta ((UniversalEnvelopingAlgebra.ι ℝ x) ^ n))

/-- The zero functional is analytic even when the target is incomplete;
    there is no nonzero or normalization hypothesis. -/
example : AnalyticFunctional (0 : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E) := by
  constructor
  · intro n
    simpa only [LinearMap.zero_apply] using
      (continuous_const : Continuous (fun _ : Fin n → g => (0 : E)))
  · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    intro x hx
    simp only [LinearMap.zero_apply, smul_zero]
    exact summable_zero

/-- Definition 3.5, PDF p.10: the radius, including 0 for no positive
    radius and infinity for an entire functional. -/
def functionalRadius (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E)
    (p : Seminorm ℝ g) : ℝ≥0∞ :=
  sSup {s | ∃ t : ℝ, 0 < t ∧ s = ENNReal.ofReal t ∧ FiniteSymmetricSeries beta p t}

/-- Definition 3.5's operative union, PDF p.10.
    Printed: p-analytic means R < infinity. Changed: use R > 0, including
    infinity, as in the printed union of the fixed-positive-radius subspaces.
    Why: finite radius excludes zero and entire maps, contradicting that union. -/
def PAnalytic (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E)
    (p : Seminorm ℝ g) : Prop :=
  AnalyticFunctional beta ∧ 0 < functionalRadius beta p

/-- Definition 3.5, PDF p.10: the fixed-radius subspace, retaining the same
    p and r under both regular actions. -/
def AtRadius (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E)
    (p : Seminorm ℝ g) (r : ℝ) : Prop :=
  AnalyticFunctional beta ∧ ENNReal.ofReal r ≤ functionalRadius beta p

/-- Equation (1), PDF pp.7--8: submultiplicativity for the Lie bracket. -/
def Submultiplicative (p : Seminorm ℝ g) : Prop :=
  ∀ x y : g, p ⁅x, y⁆ ≤ p x * p y

/-- Proposition 3.4's Banach specialization, PDF pp.8--10: a chosen norm
    expressed as a definite continuous seminorm inducing the given topology.
    Completeness uses the given compatible additive uniformity. -/
def CompatibleBanachLieNorm (p : Seminorm ℝ g) : Prop :=
  Continuous p ∧ (∀ x : g, p x = 0 → x = 0) ∧
    (∀ U : Set g, U ∈ 𝓝 (0 : g) →
      ∃ epsilon : ℝ, 0 < epsilon ∧ {x | p x < epsilon} ⊆ U) ∧
    CompleteSpace g ∧ Submultiplicative p

/-- Lemma 3.3, PDF p.9: left regular action, including its minus sign. -/
def leftRegular (x : g) (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E) :
    UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E :=
  -(beta.comp (LinearMap.mulLeft ℝ (UniversalEnvelopingAlgebra.ι ℝ x)))

/-- Lemma 3.3, PDF p.9: right regular action, with no minus sign. -/
def rightRegular (x : g) (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E) :
    UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E :=
  beta.comp (LinearMap.mulRight ℝ (UniversalEnvelopingAlgebra.ι ℝ x))

/-- Left regular action evaluated at the unit has the source's minus sign. -/
example (x : g) (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E) :
    leftRegular x beta 1 = -beta (UniversalEnvelopingAlgebra.ι ℝ x) := by
  simp [leftRegular]

/-- Remark 3.8(a), PDF pp.13--14: the continuous submultiplicative
    seminorms generate the topology. Finite maxima of such seminorms are
    again submultiplicative, giving this equivalent cofinal-ball formulation. -/
def SubmultiplicativelyGenerated : Prop :=
  ∀ U : Set g, U ∈ 𝓝 (0 : g) →
    ∃ p : Seminorm ℝ g, Continuous p ∧ Submultiplicative p ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧ {x | p x < epsilon} ⊆ U

include gAdd gHaus gScalar gLC

end Functionals

/-- Definition 4.7, PDF p.16: positive individual radius with ABSOLUTE
    norm summability. No convergence inside an incomplete invariant domain
    is required. -/
def OperatorAnalytic {K : Type u} [RCLike K] {V : Type v}
    [NormedAddCommGroup V] [NormedSpace K V] (A : Module.End K V) (v : V) : Prop :=
  ∃ t : ℝ, 0 < t ∧ Summable (fun n : ℕ =>
    ‖(A ^ n) v‖ * t ^ n / (n.factorial : ℝ))

/-- Definition 4.9, PDF p.16: absolute norm summability for every x
    in ONE zero-neighborhood, which may depend on v. Strong continuity
    is a hypothesis on the representation wherever this is used. -/
def SimultaneouslyAnalytic {K : Type u} [RCLike K]
    {g : Type v} [TopologicalSpace g] [Zero g]
    {V : Type w} [NormedAddCommGroup V] [NormedSpace K V]
    (rho : g → Module.End K V) (v : V) : Prop :=
  ∃ U : Set g, U ∈ 𝓝 (0 : g) ∧ ∀ x ∈ U,
    Summable (fun n : ℕ => ‖(rho x ^ n) v‖ / (n.factorial : ℝ))

/-- Zero is operator analytic, with no normalization condition on vectors. -/
example {K : Type u} [RCLike K] {V : Type v}
    [NormedAddCommGroup V] [NormedSpace K V] (A : Module.End K V) :
    OperatorAnalytic A 0 := by
  refine ⟨1, zero_lt_one, ?_⟩
  simp only [map_zero, norm_zero, zero_mul, zero_div]
  exact summable_zero

/-- Remark 6.13, PDF p.25: a continuous bilinear Lie bracket on a
    seminormed vector space. The additive and scalar operations are those of
    the given space, avoiding independent additive structures on a quotient.
    Definiteness and completeness are stated separately where required. -/
structure ContinuousLieBracket (K : Type u) [RCLike K] (g : Type v)
    [SeminormedAddCommGroup g] [NormedSpace K g] where
  bracket : g →L[K] g →L[K] g
  skew : ∀ x y, bracket x y = -bracket y x
  jacobi : ∀ x y z,
    bracket x (bracket y z) + bracket y (bracket z x) + bracket z (bracket x y) = 0

/-- The zero bracket admits zero-dimensional and arbitrary abelian spaces. -/
example (K : Type u) [RCLike K] (g : Type v)
    [SeminormedAddCommGroup g] [NormedSpace K g] :
    Nonempty (ContinuousLieBracket K g) := by
  exact ⟨⟨0, by simp, by simp⟩⟩

end QAlgorithms.Papers.Independent.Next46.P25


