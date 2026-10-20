-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_SphereCompletion
-- name    : OAI_Analysis_SphereIsometry_SphereCompletion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:02:19.295226+00:00
-- url     : https://prove2.me/theorems/46cc98f8-eb34-45a7-b182-148b5dd7b771
-- title:
--   Completing unit spheres and sphere isometries
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $E,F$ be real normed spaces with completions $\widehat E,\widehat F$.
--
--   1. **Sphere embedding.** The unit sphere of $E$ embeds isometrically and densely into the unit sphere of $\widehat E$, by normalizing nearby vectors. So the metric completion of $S_E$ is identified with $S_{\widehat E}$.
--   2. **Completed isometry.** A bijective isometry $f:S_E\to S_F$ and its inverse extend to a bijective isometry $\hat f:S_{\widehat E}\to S_{\widehat F}$.
--   3. **Defects.** For every $q$,
--   $$
--   \delta^{\hat f}_q(x,y)=\delta^f_q(x,y)\quad\text{on old points},
--   $$
--   the defect is continuous in $(x,y)$, and every defect bound passes to $\hat f$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/SphereCompletion.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/SphereCompletion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TingleySphereIsometry mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_TingleySphereIsometry
import Definitions.Def_OAI_Analysis_SphereIsometry_Basic
import Definitions.Def_OAI_Analysis_SphereIsometry_UnitRepresentatives
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraRealLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraNormed
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraSphere
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectSequence

namespace OAI

/-!
# Unit spheres and completion

The unit sphere of a normed space is dense in the unit sphere of its ambient
completion. This identifies its metric completion with that completed sphere.
An actual sphere isometry and its inverse therefore extend to the completed
spheres, with exact preservation of the ambient fixed-radius defect.

No completeness of the original spaces, compactness, or separability is used.
-/

noncomputable section

open UniformSpace

namespace Tingley

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A unit sphere is complete when its ambient normed space is complete. -/
instance UnitSphere.instCompleteSpace [CompleteSpace E] : CompleteSpace (UnitSphere E) :=
  (isClosed_eq continuous_norm continuous_const).completeSpace_coe

/-- The canonical ambient completion embedding restricted to the unit sphere. -/
def sphereCoe (E : Type u) [NormedAddCommGroup E] :
    UnitSphere E → UnitSphere (Completion E) := fun x =>
  ⟨(x : E), by simpa only [Completion.norm_coe] using x.property⟩

omit [NormedSpace ℝ E] in
@[simp] theorem sphereCoe_val (x : UnitSphere E) :
    (sphereCoe E x : Completion E) = ((x : E) : Completion E) := rfl

theorem sphereCoe_isometry (E : Type u) [NormedAddCommGroup E] :
    Isometry (sphereCoe E) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist ((x : E) : Completion E) ((y : E) : Completion E) =
    dist (x : E) (y : E)
  exact Completion.dist_eq (x : E) (y : E)

 theorem norm_normalize_sub (x : E) (hx : x ≠ 0) :
    ‖(normalize x hx : E) - x‖ = |1 - ‖x‖| := by
  calc
    _ = ‖(1 - ‖x‖) • (normalize x hx : E)‖ := by
      congr 1
      rw [sub_smul, one_smul, norm_smul_normalize]
    _ = |1 - ‖x‖| := by
      rw [norm_smul, Real.norm_eq_abs, UnitSphere.norm_coe, mul_one]

/-- Normalizing close old vectors proves density in the completed unit sphere. -/
theorem sphereCoe_denseRange (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    DenseRange (sphereCoe E) := by
  refine Metric.denseRange_iff.mpr ?_
  intro z ε hε
  have hδ : 0 < min (1 : ℝ) (ε / 2) := lt_min zero_lt_one (by linarith)
  obtain ⟨x, hdx⟩ :=
    (Completion.denseRange_coe : DenseRange ((↑) : E → Completion E)).exists_dist_lt
      (z : Completion E) hδ
  have habs : |1 - ‖x‖| ≤ dist (z : Completion E) (x : Completion E) := by
    simpa only [UnitSphere.norm_coe, Completion.norm_coe, dist_eq_norm] using
      abs_norm_sub_norm_le (z : Completion E) (x : Completion E)
  have hnorm : 0 < ‖x‖ := by
    have ha := (le_abs_self (1 - ‖x‖)).trans habs
    have hb := hdx.trans_le (min_le_left (1 : ℝ) (ε / 2))
    linarith
  have hx : x ≠ 0 := norm_pos_iff.mp hnorm
  have hrad : dist (x : Completion E) ((normalize x hx : E) : Completion E) =
      |1 - ‖x‖| := by
    rw [dist_comm, Completion.dist_eq, dist_eq_norm, norm_normalize_sub]
  have hsmall := hdx.trans_le (min_le_right (1 : ℝ) (ε / 2))
  refine ⟨normalize x hx, ?_⟩
  change dist (z : Completion E) ((normalize x hx : E) : Completion E) < ε
  calc
    _ ≤ dist (z : Completion E) (x : Completion E) +
        dist (x : Completion E) ((normalize x hx : E) : Completion E) :=
      dist_triangle _ _ _
    _ = dist (z : Completion E) (x : Completion E) + |1 - ‖x‖| := by rw [hrad]
    _ ≤ 2 * dist (z : Completion E) (x : Completion E) := by linarith
    _ < ε := by linarith

 def sphereCompletionMap (E : Type u) [NormedAddCommGroup E] :
    Completion (UnitSphere E) → UnitSphere (Completion E) :=
  Completion.extension (sphereCoe E)

 theorem sphereCompletionMap_isometry (E : Type u) [NormedAddCommGroup E] :
    Isometry (sphereCompletionMap E) :=
  (sphereCoe_isometry E).completion_extension

omit [NormedSpace ℝ E] in
 theorem sphereCompletionMap_coe (x : UnitSphere E) :
    sphereCompletionMap E (x : Completion (UnitSphere E)) = sphereCoe E x :=
  Completion.extension_coe (sphereCoe_isometry E).uniformContinuous x

 theorem sphereCompletionMap_surjective
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Function.Surjective (sphereCompletionMap E) := by
  have hclosed : IsClosed (Set.range (sphereCompletionMap E)) :=
    (sphereCompletionMap_isometry E).isClosedEmbedding.isClosed_range
  exact isClosed_property (sphereCoe_denseRange E) hclosed fun x =>
    ⟨(x : Completion (UnitSphere E)), sphereCompletionMap_coe x⟩

/-- The metric completion of the old sphere is the sphere of the ambient completion. -/
def sphereCompletionEquiv (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Completion (UnitSphere E) ≃ᵢ UnitSphere (Completion E) :=
  { Equiv.ofBijective (sphereCompletionMap E)
      ⟨(sphereCompletionMap_isometry E).injective, sphereCompletionMap_surjective E⟩ with
    isometry_toFun := sphereCompletionMap_isometry E }

@[simp] theorem sphereCompletionEquiv_coe (x : UnitSphere E) :
    sphereCompletionEquiv E (x : Completion (UnitSphere E)) = sphereCoe E x :=
  sphereCompletionMap_coe x

@[simp] theorem sphereCompletionEquiv_symm_coe (x : UnitSphere E) :
    (sphereCompletionEquiv E).symm (sphereCoe E x) =
      (x : Completion (UnitSphere E)) := by
  apply (sphereCompletionEquiv E).injective
  simp only [IsometryEquiv.apply_symm_apply, sphereCompletionEquiv_coe]

 def sphereIsometryCompletion (f : UnitSphere E ≃ᵢ UnitSphere F) :
    Completion (UnitSphere E) ≃ᵢ Completion (UnitSphere F) where
  toFun := Completion.map f
  invFun := Completion.map f.symm
  left_inv x := by
    have h := congr_fun
      (Completion.map_comp f.symm.isometry.uniformContinuous f.isometry.uniformContinuous) x
    rw [f.symm_comp_self, Completion.map_id] at h
    exact h
  right_inv y := by
    have h := congr_fun
      (Completion.map_comp f.isometry.uniformContinuous f.symm.isometry.uniformContinuous) y
    rw [f.self_comp_symm, Completion.map_id] at h
    exact h
  isometry_toFun := f.isometry.completion_map

/-- Extend the actual sphere isometry and its inverse through the sphere completions. -/
def completedSphereEquiv (f : UnitSphere E ≃ᵢ UnitSphere F) :
    UnitSphere (Completion E) ≃ᵢ UnitSphere (Completion F) :=
  ((sphereCompletionEquiv E).symm.trans (sphereIsometryCompletion f)).trans
    (sphereCompletionEquiv F)

@[simp] theorem completedSphereEquiv_coe (f : UnitSphere E ≃ᵢ UnitSphere F)
    (x : UnitSphere E) :
    completedSphereEquiv f (sphereCoe E x) = sphereCoe F (f x) := by
  change sphereCompletionEquiv F
    (Completion.map f ((sphereCompletionEquiv E).symm (sphereCoe E x))) = sphereCoe F (f x)
  rw [sphereCompletionEquiv_symm_coe, Completion.map_coe f.isometry.uniformContinuous,
    sphereCompletionEquiv_coe]

@[simp] theorem completedSphereEquiv_symm (f : UnitSphere E ≃ᵢ UnitSphere F) :
    (completedSphereEquiv f).symm = completedSphereEquiv f.symm := by
  apply IsometryEquiv.ext
  intro y
  rfl

/-- The canonical ambient embedding preserves all real scalar difference norms. -/
theorem norm_completion_sub_smul (x y : E) (q : ℝ) :
    ‖(x : Completion E) - q • (y : Completion E)‖ = ‖x - q • y‖ := by
  rw [← Completion.coe_smul, ← Completion.coe_sub, Completion.norm_coe]

/-- The defect on embedded old points is preserved for every real scalar. -/
@[simp] theorem signedDefect_completedSphereEquiv_coe
    (f : UnitSphere E ≃ᵢ UnitSphere F) (q : ℝ) (x y : UnitSphere E) :
    signedDefect (completedSphereEquiv f) q (sphereCoe E x) (sphereCoe E y) =
      signedDefect f q x y := by
  unfold signedDefect
  rw [completedSphereEquiv_coe, completedSphereEquiv_coe]
  simp only [sphereCoe_val, norm_completion_sub_smul]

/-- The fixed-radius signed defect is continuous on pairs of unit points. -/
theorem continuous_signedDefect_pair (f : UnitSphere E ≃ᵢ UnitSphere F) (q : ℝ) :
    Continuous (fun p : UnitSphere E × UnitSphere E => signedDefect f q p.1 p.2) := by
  have hx : Continuous (fun p : UnitSphere E × UnitSphere E => (p.1 : E)) :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun p : UnitSphere E × UnitSphere E => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have hfx : Continuous (fun p : UnitSphere E × UnitSphere E => (f p.1 : F)) :=
    continuous_subtype_val.comp (f.continuous.comp continuous_fst)
  have hfy : Continuous (fun p : UnitSphere E × UnitSphere E => (f p.2 : F)) :=
    continuous_subtype_val.comp (f.continuous.comp continuous_snd)
  exact (hfx.sub (hfy.const_smul q)).norm.sub (hx.sub (hy.const_smul q)).norm

/-- Every fixed-radius bound passes to all pairs in the completed spheres. -/
theorem HasDefectBound.completedSphereEquiv {f : UnitSphere E ≃ᵢ UnitSphere F} {M : ℝ}
    (h : HasDefectBound f M) : HasDefectBound (completedSphereEquiv f) M := by
  intro q hq x y
  have hclosed : IsClosed {p : UnitSphere (Completion E) × UnitSphere (Completion E) |
      |signedDefect (Tingley.completedSphereEquiv f) q p.1 p.2| ≤ M} :=
    isClosed_le (continuous_signedDefect_pair (Tingley.completedSphereEquiv f) q).abs continuous_const
  exact isClosed_property2
    (p := fun a b : UnitSphere (Completion E) =>
      |signedDefect (Tingley.completedSphereEquiv f) q a b| ≤ M)
    (sphereCoe_denseRange E) hclosed
    (fun a b => by simpa only [signedDefect_completedSphereEquiv_coe] using h q hq a b) x y

end Tingley

end

end OAI


