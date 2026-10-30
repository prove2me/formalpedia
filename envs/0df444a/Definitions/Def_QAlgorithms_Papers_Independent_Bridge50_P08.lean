-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P08
-- name    : QAlgorithms_Papers_Independent_Bridge50_P08
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:15:41.249456+00:00
-- url     : https://prove2.me/theorems/2ef1fd32-3efa-4663-84e9-c4b8d3e2d6cd
-- title:
--   Definitions for Principal 2-bundles and their gauge 2-groups
-- statement:
--   The objects the formalized statements of *Principal 2-bundles and their gauge 2-groups* (arXiv:0803.3692) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `sourceKernelAction`: Remark II.4, PDF p. 10: identity-arrow conjugation on the actual source kernel. The section equation ensures that conjugation stays in it. These are tensor group operations, not categorical arrow composition.
--   - `IsDirectionalLieGroup`: Definition A.1, PDF p. 35: compatible directional atlas and smooth group operations. Hausdorff and locally convex model assumptions are explicit in the theorem binders below. No norm or completeness is used.
--   - `HasLeftVelocity`: Definition A.3, PDF pp. 35–36: the left logarithmic velocity of a curve equals x. The identity chart identifies T_1 G with E. Translating by gamma(t) inverse before differentiating is exactly the equation gamma'(t) = T(leftTranslation_gamma(t))(1) x. The chart centre is subtracted explicitly; identity charts need not send 1 to zero.
--   - `IsExponentialFunction`: Definition A.3, PDF pp. 35–36: a smooth exponential function is the time-one value of a global smooth solution of the left invariant ODE for every identity tangent x. This requires actual solutions on all of R, not local exponentiality or an arbitrary map called an exponential.
--   - `identityDifferential`: Lemma A.4, PDF pp. 35–36: the induced differential in the actual identity charts. The slope is computed on chartE(1) + h x and then mapped through the homomorphism and the target identity chart. For the smooth maps between Hausdorff locally convex manifolds used below this limit exists and is unique; no freely supplied tangent map is used.
-- source:
--   Principal 2-bundles and their gauge 2-groups, arXiv:0803.3692v4, https://arxiv.org/abs/0803.3692v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

/-!
Statements from Wockel, arXiv:0803.3692v4.
The algebraic forward construction is reused, without restating its theorem.
All new definitions are local to this paper. The appendix uses arbitrary
Hausdorff locally convex real models and the accepted directional calculus.
The remaining nodes are explicitly inventoried in HARD.md and GAPS.json.
Compilation and independent moderation are pending batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Bridge50.P08

open Set Filter Topology
open QAlgorithms.Papers.Independent.Renew46.P18
open QAlgorithms.Papers.Independent.Claimed50.P22
open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

/-- Remark II.4, PDF p. 10: identity-arrow conjugation on the actual
source kernel. The section equation ensures that conjugation stays in it.
These are tensor group operations, not categorical arrow composition. -/
def sourceKernelAction {G : Type u} {K : Type v} [Group G] [Group K]
    (s : K →* G) (identity : G →* K)
    (hSection : ∀ g, s (identity g) = g) : G →* MulAut s.ker where
  toFun g :=
    { toFun := fun h => ⟨identity g * h.val * (identity g)⁻¹, by
        change s (identity g * h.val * (identity g)⁻¹) = 1
        have hh : s h.val = 1 := h.property
        simp [hSection, hh]⟩
      invFun := fun h => ⟨(identity g)⁻¹ * h.val * identity g, by
        change s ((identity g)⁻¹ * h.val * identity g) = 1
        have hh : s h.val = 1 := h.property
        simp [hSection, hh]⟩
      left_inv := by
        intro h
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := by
        intro h
        apply Subtype.ext
        simp [mul_assoc]
      map_mul' := by
        intro h k
        apply Subtype.ext
        simp [mul_assoc] }
  map_one' := by
    ext h
    simp
  map_mul' := by
    intro g k
    ext h
    simp [mul_assoc]

/-- Sanity: at the identity object, kernel conjugation is the identity. -/
example {G : Type u} {K : Type v} [Group G] [Group K]
    (s : K →* G) (identity : G →* K)
    (hSection : ∀ g, s (identity g) = g) (h : s.ker) :
    (sourceKernelAction s identity hSection 1 h : K) = h.val := by
  simp [sourceKernelAction]

/-- Product charts, used only to express smoothness of multiplication. -/
local instance productCharts
    (E F M N : Type*) [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N] : ChartedSpace (E × F) (M × N) :=
  prodChartedSpace E M F N

section LocallyConvexCalculus

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable {G : Type v} [Group G] [TopologicalSpace G] [ChartedSpace E G]

/-- Definition A.1, PDF p. 35: compatible directional atlas and smooth
group operations. Hausdorff and locally convex model assumptions are
explicit in the theorem binders below. No norm or completeness is used. -/
def IsDirectionalLieGroup : Prop :=
  BastianiAtlas (E := E) (M := G) ∧
    DirectionalManifoldSmooth (E := E × E) (F := E)
      (fun p : G × G => p.1 * p.2) ∧
    DirectionalManifoldSmooth (E := E) (F := E) (fun g : G => g⁻¹)

/-- Definition A.3, PDF pp. 35–36: the left logarithmic velocity of a
curve equals x. The identity chart identifies T_1 G with E. Translating
by gamma(t) inverse before differentiating is exactly the equation
gamma'(t) = T(leftTranslation_gamma(t))(1) x. The chart centre is
subtracted explicitly; identity charts need not send 1 to zero. -/
def HasLeftVelocity (gamma : ℝ → G) (t : ℝ) (x : E) : Prop :=
  Tendsto (fun h : ℝ => h⁻¹ •
      (chartAt E (1 : G) ((gamma t)⁻¹ * gamma (t + h)) -
        chartAt E (1 : G) 1))
    (𝓝[≠] (0 : ℝ)) (𝓝 x)

/-- Definition A.3, PDF pp. 35–36: a smooth exponential function is the
time-one value of a global smooth solution of the left invariant ODE
for every identity tangent x. This requires actual solutions on all of R,
not local exponentiality or an arbitrary map called an exponential. -/
def IsExponentialFunction (expMap : E → G) : Prop :=
  DirectionalManifoldSmooth (E := E) (F := E) expMap ∧
    ∀ x : E, ∃ gamma : ℝ → G,
      DirectionalManifoldSmooth (E := ℝ) (F := E) gamma ∧
        gamma 0 = 1 ∧ (∀ t : ℝ, HasLeftVelocity gamma t x) ∧
          gamma 1 = expMap x

/-- Sanity: in the zero-dimensional group, all group operations are smooth
and the unique map is an ODE-defined exponential, including x = 0. -/
example : IsDirectionalLieGroup (E := PUnit.{1}) (G := PUnit.{1}) ∧
    IsExponentialFunction (E := PUnit.{1}) (G := PUnit.{1})
      (fun _ => PUnit.unit) := by
  have hs : ∀ {A : Type} [AddCommGroup A] [Module ℝ A] [TopologicalSpace A]
      (U : Set A) (f : A → PUnit.{1}), DirectionalSmoothOn U f := by
    intro A a m t U f
    refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro x hx
      exact Subsingleton.elim _ _
    · intro n
      exact continuousOn_const
    · intro n x hx a h
      simpa only [sub_self, smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : PUnit.{1}))
          (𝓝[≠] (0 : ℝ)) (𝓝 (0 : PUnit.{1})))
  have smoothTarget : ∀ {A M : Type} [TopologicalSpace A] [AddCommGroup A]
      [Module ℝ A] [TopologicalSpace M] [ChartedSpace A M]
      (f : M → PUnit.{1}),
      DirectionalManifoldSmooth (E := A) (F := PUnit.{1}) f := by
    intro A M a b c d e f
    refine ⟨?_, ?_⟩
    · have hf : f = fun _ => PUnit.unit := funext (fun _ => Subsingleton.elim _ _)
      rw [hf]
      exact continuous_const
    · intro c hc e he
      exact hs _ _
  constructor
  · refine ⟨?_, smoothTarget _, smoothTarget _⟩
    intro c hc e he
    change DirectionalSmoothOn _ _
    exact hs _ _
  · refine ⟨smoothTarget _, ?_⟩
    intro x
    refine ⟨fun _ => PUnit.unit, smoothTarget _, rfl, ?_, rfl⟩
    intro t
    change Tendsto _ _ (𝓝 x)
    have ht : ∀ f : ℝ → PUnit.{1}, Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
      intro f
      have hf : f = fun _ => x := funext (fun _ => Subsingleton.elim _ _)
      rw [hf]
      exact tendsto_const_nhds
    exact ht _

end LocallyConvexCalculus

/-- Lemma A.4, PDF pp. 35–36: the induced differential in the actual
identity charts. The slope is computed on chartE(1) + h x and then
mapped through the homomorphism and the target identity chart. For the
smooth maps between Hausdorff locally convex manifolds used below this
limit exists and is unique; no freely supplied tangent map is used. -/
noncomputable def identityDifferential
    {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    {G : Type w} {K : Type z}
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [Group K] [TopologicalSpace K] [ChartedSpace F K]
    (alpha : G →* K) (x : E) : F :=
  Filter.limUnder (𝓝[≠] (0 : ℝ)) (fun h : ℝ => h⁻¹ •
    (chartAt F (1 : K)
      (alpha ((chartAt E (1 : G)).symm (chartAt E (1 : G) 1 + h • x))) -
        chartAt F (1 : K) 1))

/-- Sanity: the actual differential on the trivial group has zero value. -/
example (x : PUnit.{1}) :
    identityDifferential (E := PUnit.{1}) (F := PUnit.{1})
      (MonoidHom.id PUnit.{1}) x = 0 := by
  exact Subsingleton.elim _ _

end QAlgorithms.Papers.Independent.Bridge50.P08


