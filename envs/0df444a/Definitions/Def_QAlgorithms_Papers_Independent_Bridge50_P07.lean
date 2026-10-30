-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P07
-- name    : QAlgorithms_Papers_Independent_Bridge50_P07
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:14:22.91925+00:00
-- url     : https://prove2.me/theorems/836cd7fd-315c-4565-b679-085be8d952fc
-- title:
--   Definitions for A Smooth Model for the String Group
-- statement:
--   The objects the formalized statements of *A Smooth Model for the String Group* (arXiv:1104.4288) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CompatibleChart`: Appendix A, PDF p. 25: an additional chart belongs to the smooth structure when its transitions with the supplied atlas are Bastiani smooth in both directions. The chart is an actual open partial homeomorphism.
--   - `BastianiSubmersion`: Appendix A, PDF p. 25: a submersion is locally a projection onto a topological direct summand in compatible smooth charts. A continuous linear right inverse specifies the direct summand. No global surjectivity is imposed, and the splitting and charts may depend on the source point.
--   - `HasSubmanifoldCharts`: Appendix A, PDF pp. 25--26: the local submanifold criterion for a subset with closed local model. In an ambient compatible chart it is an affine slice of a closed vector subspace with its induced topology. No complement for that subspace is assumed. On the fibers used below the closedness follows from the Hausdorff target, so this criterion expresses the induced embedded smooth submanifold structure, including empty fibers.
-- source:
--   A Smooth Model for the String Group, arXiv:1104.4288v4, https://arxiv.org/abs/1104.4288v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

/-!
Draft statements from Nikolaus--Sachse--Wockel, arXiv:1104.4288v4.
Only Corollary A.4 is stated. Other assigned nodes are explicitly deferred
in the unit's HARD.md and GAPS.json. The accepted directional calculus
uses arbitrary locally convex models. No frozen definition is modified.
Compilation and independent moderation are pending batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Bridge50.P07

open Set
open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

section LocalGeometry

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable {M : Type w} {N : Type z}
variable [TopologicalSpace M] [TopologicalSpace N]
variable [ChartedSpace E M] [ChartedSpace F N]

/-- Appendix A, PDF p. 25: an additional chart belongs to the smooth
structure when its transitions with the supplied atlas are Bastiani smooth
in both directions. The chart is an actual open partial homeomorphism. -/
def CompatibleChart (c : OpenPartialHomeomorph M E) : Prop :=
  ∀ a ∈ atlas E M,
    DirectionalSmoothOn (a.symm.trans c).source (a.symm.trans c) ∧
      DirectionalSmoothOn (c.symm.trans a).source (c.symm.trans a)

/-- Appendix A, PDF p. 25: a submersion is locally a projection onto a
topological direct summand in compatible smooth charts. A continuous linear
right inverse specifies the direct summand. No global surjectivity is
imposed, and the splitting and charts may depend on the source point. -/
def BastianiSubmersion (f : M → N) : Prop :=
  DirectionalManifoldSmooth (E := E) (F := F) f ∧
    ∀ x : M,
      ∃ c : OpenPartialHomeomorph M E,
      ∃ d : OpenPartialHomeomorph N F,
      ∃ p : E →L[ℝ] F, ∃ j : F →L[ℝ] E,
        CompatibleChart c ∧ CompatibleChart d ∧
          x ∈ c.source ∧ f x ∈ d.source ∧
          p.comp j = ContinuousLinearMap.id ℝ F ∧
          ∀ y ∈ c.source, f y ∈ d.source ∧ d (f y) = p (c y)

/-- Appendix A, PDF pp. 25--26: the local submanifold criterion for a
subset with closed local model. In an ambient compatible chart it is an
affine slice of a closed vector subspace with its induced topology. No
complement for that subspace is assumed. On the fibers used below the
closedness follows from the Hausdorff target, so this criterion expresses
the induced embedded smooth submanifold structure, including empty fibers. -/
def HasSubmanifoldCharts (S : Set M) : Prop :=
  ∀ x ∈ S, ∃ c : OpenPartialHomeomorph M E,
    CompatibleChart c ∧ x ∈ c.source ∧
      ∃ V : Submodule ℝ E, IsClosed (V : Set E) ∧
        ∀ y ∈ c.source, y ∈ S ↔ c y - c x ∈ V

/-- Sanity: an empty subset satisfies the submanifold criterion; no point
or chart is demanded for a fiber outside the image. -/
example : HasSubmanifoldCharts (E := E) (∅ : Set M) := by
  intro x hx
  exact False.elim hx

/-- Sanity: local projection data retains genuine smoothness, rather than
merely the surjectivity of a derivative. -/
example (f : M → N) (hf : BastianiSubmersion (E := E) (F := F) f) :
    DirectionalManifoldSmooth (E := E) (F := F) f := hf.1

/-- Sanity: the ordinary coordinate projection has a genuine continuous
linear right inverse, so the split-projection condition admits the standard
nonempty positive-dimensional example. -/
example : (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.inl ℝ ℝ ℝ) = ContinuousLinearMap.id ℝ ℝ := by
  ext x
  rfl

end LocalGeometry

end QAlgorithms.Papers.Independent.Bridge50.P07


