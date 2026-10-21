-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15
-- name    : QAlgorithms_Papers_Independent_Next46_P15
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:14:49.247488+00:00
-- url     : https://prove2.me/theorems/8daa5aa6-3e99-4b47-90e1-90458fbb9572
-- title:
--   Definitions for Towards a Lie theory for locally convex groups
-- statement:
--   The objects the formalized statements of *Towards a Lie theory for locally convex groups* (arXiv:1501.06269) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HasDirectionalDerivative`: Definition I.2.1(a), PDF p.12: the directional difference-quotient limit. Only real nonzero increments tend to zero.
--   - `directionalDerivative`: Definition I.2.1(a), PDF p.12: the directional derivative, selected from its actual limit. Every use below is guarded by existence of the relevant limits. Values away from the open domain have no mathematical significance.
--   - `iteratedDirectional`: Definition I.2.1(a), PDF p.12: iterated derivatives in the printed order D_(h_n) ... D_(h_1). Order zero is the original function.
--   - `IsMBC1On`: Definition I.2.1(a), PDF p.12: continuous differentiability as defined before continuity of f is established in Proposition I.2.3(iii).
--   - `IsMBCFiniteOn`: Definition I.2.1(a), PDF p.12: finite-order Michal--Bastiani C^n. Existence of all iterated limits is imposed separately from joint continuity. At order zero this is precisely continuity on U.
--   - `IsMBSmoothOn`: The existing, audited all-orders tower is the smoothness convention of Definition I.2.1(a), PDF p.12. This abbreviation does not change that predicate.
--   - `RepresentsWeakIntegral`: Definition I.1.4, PDF p.11: a represented weak integral on [0,1]. Only scalar-valued integrals occur. Scalar integrability is explicit, and the representing vector is a conclusion rather than an extra completeness hypothesis.
--   - `IsMBSmoothBetween`: Definition I.3.1, PDF p.15: smooth maps tested in both source and target charts, on the actual overlap domain. Continuity ensures these domains are open.
--   - `HasZeroFiberDifferentials`: Definitions I.3.3 and Proposition I.3.4, PDF pp.15--16: every fiber map T_p(f) is zero, expressed in all tangent charts. The base component remains f; this predicate never identifies T(f) with a constant point of the total bundle.
--   - `IsNormableLC`: Remark I.3.9, PDF p.17: normability expressed by a separating seminorm whose balls form the original zero-neighborhood basis. No norm is imposed on E.
--   - `cotangentExample`: Remark I.3.9, PDF p.17: the actual polynomial map, not a freely chosen local diffeomorphism.
--   - `quadraticScalarInverse`: Remark I.3.9, PDF p.17: the inverse of s↦s+s² on (-1/2,infinity).
--   - `cotangentExampleInverse`: Remark I.3.9, PDF p.17: the actual inverse on alpha(y)>-1/4.
--   - `cotangentExamplePullback`: Remark I.3.9, PDF p.17: lambda composed with the actual differential. This algebraic continuous functional can be considered with any vector topology on the dual; no continuity with respect to that topology is assumed.
--   - `compactDualTopology`: Definition I.5.1 and Remark I.5.4, PDF pp.19--20: compact-open topology on the continuous dual, induced from the genuine continuous-map space.
-- source:
--   Towards a Lie theory for locally convex groups, arXiv:1501.06269v1, https://arxiv.org/abs/1501.06269v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

/-!
Statements from K.-H. Neeb, arXiv:1501.06269v1.
Real directional calculus includes the underlying real spaces of complex models.
All spaces below are Hausdorff; no normability or completeness is imposed.
The accepted smooth derivative-tower predicate is reused from Claimed50.P22.
Finite-order derivatives and represented weak integrals are defined independently.
Deferred nodes and the precise missing interfaces are recorded in this unit's GAPS.json.
Compilation is pending the mechanical batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P15

open Set Filter Topology
open scoped BigOperators

universe u v w z

section DirectionalCalculus

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable {F : Type v} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Definition I.2.1(a), PDF p.12: the directional difference-quotient limit.
Only real nonzero increments tend to zero. -/
def HasDirectionalDerivative (f : E → F) (x h : E) (y : F) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (f (x + t • h) - f x))
    (𝓝[≠] (0 : ℝ)) (𝓝 y)

/-- Definition I.2.1(a), PDF p.12: the directional derivative, selected from
its actual limit. Every use below is guarded by existence of the relevant limits.
Values away from the open domain have no mathematical significance. -/
def directionalDerivative (f : E → F) (x h : E) : F :=
  Classical.epsilon (HasDirectionalDerivative f x h)

/-- Definition I.2.1(a), PDF p.12: iterated derivatives in the printed order
D_(h_n) ... D_(h_1). Order zero is the original function. -/
def iteratedDirectional (f : E → F) : (n : ℕ) → E → (Fin n → E) → F
  | 0, x, _ => f x
  | n + 1, x, h =>
      directionalDerivative
        (fun y => iteratedDirectional f n y (fun i => h i.castSucc))
        x (h (Fin.last n))

/-- Definition I.2.1(a), PDF p.12: continuous differentiability as defined
before continuity of f is established in Proposition I.2.3(iii). -/
def IsMBC1On (U : Set E) (f : E → F) : Prop :=
  (∀ x ∈ U, ∀ h : E,
    HasDirectionalDerivative f x h (directionalDerivative f x h)) ∧
  ContinuousOn (fun p : E × E => directionalDerivative f p.1 p.2)
    (U ×ˢ (Set.univ : Set E))

/-- Definition I.2.1(a), PDF p.12: finite-order Michal--Bastiani C^n.
Existence of all iterated limits is imposed separately from joint continuity.
At order zero this is precisely continuity on U. -/
def IsMBCFiniteOn (U : Set E) (f : E → F) (n : ℕ) : Prop :=
  (∀ j : ℕ, j < n → ∀ x ∈ U, ∀ (a : Fin j → E) (h : E),
    HasDirectionalDerivative (fun y => iteratedDirectional f j y a) x h
      (iteratedDirectional f (j + 1) x (Fin.snoc a h))) ∧
  (∀ j : ℕ, j ≤ n →
    ContinuousOn (fun p : E × (Fin j → E) => iteratedDirectional f j p.1 p.2)
      (U ×ˢ (Set.univ : Set (Fin j → E))))

/-- The existing, audited all-orders tower is the smoothness convention of
Definition I.2.1(a), PDF p.12. This abbreviation does not change that predicate. -/
abbrev IsMBSmoothOn (U : Set E) (f : E → F) : Prop :=
  QAlgorithms.Papers.Independent.Claimed50.P22.BastianiSmoothOn U f

/-- Sanity: the zero directional difference quotient has limit zero. -/
example (x h : E) : HasDirectionalDerivative (fun _ : E => (0 : F)) x h 0 := by
  simpa only [HasDirectionalDerivative, sub_self, smul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

/-- Sanity: the zeroth derivative retains the function, including empty tuples. -/
example (f : E → F) (x : E) (a : Fin 0 → E) :
    iteratedDirectional f 0 x a = f x := rfl

end DirectionalCalculus

section WeakIntegrals

variable {F : Type v} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Definition I.1.4, PDF p.11: a represented weak integral on [0,1].
Only scalar-valued integrals occur. Scalar integrability is explicit, and the
representing vector is a conclusion rather than an extra completeness hypothesis. -/
def RepresentsWeakIntegral (curve : ℝ → F) (value : F) : Prop :=
  ContinuousOn curve (Set.Icc (0 : ℝ) 1) ∧
  ∀ ell : F →L[ℝ] ℝ,
    IntervalIntegrable (fun t => ell (curve t)) MeasureTheory.volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ell (curve t)) = ell value

/-- Sanity: the zero curve has the represented weak integral zero. -/
example : RepresentsWeakIntegral (fun _ : ℝ => (0 : F)) 0 := by
  refine ⟨continuousOn_const, ?_⟩
  intro ell
  simp only [map_zero]
  exact ⟨intervalIntegrable_const, by simp⟩

end WeakIntegrals

section Manifolds

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable {F : Type v} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
variable {N : Type z} [TopologicalSpace N] [ChartedSpace F N]

/-- Definition I.3.1, PDF p.15: smooth maps tested in both source and target
charts, on the actual overlap domain. Continuity ensures these domains are open. -/
def IsMBSmoothBetween (f : M → N) : Prop :=
  Continuous f ∧ ∀ c ∈ atlas E M, ∀ d ∈ atlas F N,
    IsMBSmoothOn
      (c.target ∩ (fun x => f (c.symm x)) ⁻¹' d.source)
      (fun x => d (f (c.symm x)))

/-- Definitions I.3.3 and Proposition I.3.4, PDF pp.15--16: every fiber
map T_p(f) is zero, expressed in all tangent charts. The base component remains f;
this predicate never identifies T(f) with a constant point of the total bundle. -/
def HasZeroFiberDifferentials (f : M → N) : Prop :=
  ∀ c ∈ atlas E M, ∀ d ∈ atlas F N, ∀ p ∈ c.source,
    f p ∈ d.source → ∀ h : E,
      directionalDerivative (fun x => d (f (c.symm x))) (c p) h = 0

end Manifolds

section Counterexamples

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Remark I.3.9, PDF p.17: normability expressed by a separating seminorm
whose balls form the original zero-neighborhood basis. No norm is imposed on E. -/
def IsNormableLC (E : Type u) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ p : Seminorm ℝ E,
    (∀ x : E, p x = 0 → x = 0) ∧
    ∀ U : Set E, U ∈ 𝓝 (0 : E) ↔
      ∃ epsilon : ℝ, 0 < epsilon ∧ {x : E | p x < epsilon} ⊆ U

/-- Remark I.3.9, PDF p.17: the actual polynomial map, not a freely chosen
local diffeomorphism. -/
def cotangentExample (alpha : E →L[ℝ] ℝ) (x : E) : E :=
  (1 + alpha x) • x

/-- Remark I.3.9, PDF p.17: the inverse of s↦s+s² on (-1/2,infinity). -/
def quadraticScalarInverse (s : ℝ) : ℝ :=
  (Real.sqrt (1 + 4 * s) - 1) / 2

/-- Remark I.3.9, PDF p.17: the actual inverse on alpha(y)>-1/4. -/
def cotangentExampleInverse (alpha : E →L[ℝ] ℝ) (y : E) : E :=
  (1 + quadraticScalarInverse (alpha y))⁻¹ • y

/-- Remark I.3.9, PDF p.17: lambda composed with the actual differential.
This algebraic continuous functional can be considered with any vector topology
on the dual; no continuity with respect to that topology is assumed. -/
def cotangentExamplePullback (alpha : E →L[ℝ] ℝ)
    (x : E) (ell : E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (1 + alpha x) • ell + ell x • alpha

/-- Definition I.5.1 and Remark I.5.4, PDF pp.19--20: compact-open topology
on the continuous dual, induced from the genuine continuous-map space. -/
def compactDualTopology (E : Type u) [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] : TopologicalSpace (E →L[ℝ] ℝ) :=
  TopologicalSpace.induced
    (fun ell : E →L[ℝ] ℝ => (⟨fun x => ell x, ell.continuous⟩ : C(E, ℝ)))
    inferInstance

/-- Sanity: the chosen polynomial fixes the origin. -/
example (alpha : E →L[ℝ] ℝ) : cotangentExample alpha 0 = 0 := by
  simp [cotangentExample]

/-- Sanity: the inverse branch takes zero to zero. -/
example : quadraticScalarInverse 0 = 0 := by
  norm_num [quadraticScalarInverse]

/-- Sanity: the pullback at the origin is the original covector. -/
example (alpha ell : E →L[ℝ] ℝ) : cotangentExamplePullback alpha 0 ell = ell := by
  simp [cotangentExamplePullback]

end Counterexamples

end QAlgorithms.Papers.Independent.Next46.P15


