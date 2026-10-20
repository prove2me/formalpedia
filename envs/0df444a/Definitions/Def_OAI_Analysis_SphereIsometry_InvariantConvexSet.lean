-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_InvariantConvexSet
-- name    : OAI_Analysis_SphereIsometry_InvariantConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:10:47.693413+00:00
-- url     : https://prove2.me/theorems/a0c2ffce-729f-46fc-b7fd-a465b8e33b64
-- title:
--   Closed convex invariant sets from positive prefix growth
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $G:X\to X$ and $E\subseteq X$.
--
--   1. **Recursive sequence.** Start from $v_0$ and append $G(\mu_n)$, where $\mu_n$ is the positive stage mean of the prefix built so far.
--   2. **Positive prefix growth.** Whenever the convex hull of $p_0,\dots,p_n$ lies in $E$ and $w$ is a strictly positive probability vector, the convex hull of $p_0,\dots,p_n,G(\sum_iw_ip_i)$ still lies in $E$.
--   3. **Recursive convex set.**
--   $$
--   C=\overline{\mathrm{conv}}\{v_0,v_1,\dots\} .
--   $$
--   Under positive prefix growth with $v_0\in E$, $E$ closed and bounded, and $G$ continuous on $E$, the set $C$ is a nonempty closed bounded convex subset of $E$ with $G(C)\subseteq C$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/InvariantConvexSet.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/InvariantConvexSet.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_SphereCompletion
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectAttainment
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialContact
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMap
import Definitions.Def_OAI_Analysis_SphereIsometry_Supports
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveConvexFace
import Definitions.Def_OAI_Analysis_SphereIsometry_ExtremalPropagation
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveScheduling

namespace OAI

/-!
A closed invariant convex set from proved finite-prefix growth. The input
growth theorem is instantiated by the geometric common-support argument;
the recursion, positive scheduling, density and invariance are proved here.
-/

noncomputable section

open scoped BigOperators
open Set

namespace Tingley

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Ordinary finite-prefix recursion; no admissibility proof enters the data. -/
def recursivePrefix (G : X → X) (v₀ : X) : (n : ℕ) → (Fin (n+1) → X)
  | 0 => fun _ => v₀
  | n+1 => Fin.snoc (α := fun _ : Fin (n+2) => X) (recursivePrefix G v₀ n)
      (G (∑ i, positiveStageWeights n i • recursivePrefix G v₀ n i))

def recursiveVector (G : X → X) (v₀ : X) (n : ℕ) : X :=
  recursivePrefix G v₀ n (Fin.last n)

@[simp] theorem recursiveVector_zero (G : X → X) (v₀ : X) :
    recursiveVector G v₀ 0 = v₀ := rfl

theorem recursivePrefix_eq_vector (G : X → X) (v₀ : X)
    (n : ℕ) (i : Fin (n+1)) :
    recursivePrefix G v₀ n i = recursiveVector G v₀ i.val := by
  induction n with
  | zero =>
      have hi : i.val = 0 := by omega
      simp [recursivePrefix]
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa only [recursivePrefix, Fin.snoc_castSucc, Fin.val_castSucc] using ih j

theorem recursiveVector_succ (G : X → X) (v₀ : X) (n : ℕ) :
    recursiveVector G v₀ (n+1) = G (stageMean (recursiveVector G v₀) n) := by
  unfold recursiveVector
  rw [recursivePrefix, Fin.snoc_last]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [recursivePrefix_eq_vector]
  rfl

/-- The geometric one-step conclusion for the invariant convex set. -/
def PositivePrefixGrowth (G : X → X) (E : Set X) : Prop :=
  ∀ (n : ℕ) (p : Fin (n+1) → X) (w : Fin (n+1) → ℝ),
    convexHull ℝ (Set.range p) ⊆ E →
    (∀ i, 0 < w i) → (∑ i, w i = 1) →
    convexHull ℝ (Set.range
      (Fin.snoc (α := fun _ : Fin (n+2) => X) p (G (∑ i, w i • p i)))) ⊆ E

theorem recursivePrefix_hull_subset (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    convexHull ℝ (Set.range (recursivePrefix G v₀ n)) ⊆ E := by
  induction n with
  | zero =>
      have hr : Set.range (recursivePrefix G v₀ 0) = {v₀} := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩; rfl
        · intro hx
          exact ⟨0, hx.symm⟩
      rw [hr, convexHull_singleton]
      exact Set.singleton_subset_iff.mpr hv₀
  | succ n ih =>
      exact hstep n (recursivePrefix G v₀ n) (positiveStageWeights n) ih
        (positiveStageWeights_pos n) (positiveStageWeights_sum n)

theorem recursiveVector_prefix_hull_subset (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    convexHull ℝ (Set.range (fun i : Fin (n+1) => recursiveVector G v₀ i.val)) ⊆ E := by
  have he : (fun i : Fin (n+1) => recursiveVector G v₀ i.val) =
      recursivePrefix G v₀ n := by
    funext i
    exact (recursivePrefix_eq_vector G v₀ n i).symm
  rw [he]
  exact recursivePrefix_hull_subset G E v₀ hv₀ hstep n

theorem recursiveVector_mem (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    recursiveVector G v₀ n ∈ E :=
  recursivePrefix_hull_subset G E v₀ hv₀ hstep n
    (subset_convexHull ℝ _ ⟨Fin.last n, rfl⟩)

/-- The closed convex hull of the one actual recursively constructed sequence. -/
def recursiveConvexSet (G : X → X) (v₀ : X) : Set X :=
  closure (convexHull ℝ (Set.range (recursiveVector G v₀)))

theorem recursiveConvexSet_subset (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hE : IsClosed E) (hstep : PositivePrefixGrowth G E) :
    recursiveConvexSet G v₀ ⊆ E := by
  apply closure_minimal _ hE
  exact convexHull_range_subset_of_prefixes _ E
    (recursiveVector_prefix_hull_subset G E v₀ hv₀ hstep)

theorem recursiveConvexSet_nonempty (G : X → X) (v₀ : X) :
    (recursiveConvexSet G v₀).Nonempty := by
  refine ⟨recursiveVector G v₀ 0, subset_closure ?_⟩
  exact subset_convexHull ℝ _ ⟨0, rfl⟩

theorem isClosed_recursiveConvexSet (G : X → X) (v₀ : X) :
    IsClosed (recursiveConvexSet G v₀) := isClosed_closure

theorem convex_recursiveConvexSet (G : X → X) (v₀ : X) :
    Convex ℝ (recursiveConvexSet G v₀) := (convex_convexHull ℝ _).closure

theorem recursiveConvexSet_invariant (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hE : IsClosed E) (hunit : ∀ x ∈ E, ‖x‖ = 1)
    (hG : ContinuousOn G E) (hstep : PositivePrefixGrowth G E) :
    Set.MapsTo G (recursiveConvexSet G v₀) (recursiveConvexSet G v₀) := by
  let v := recursiveVector G v₀
  have hv : ∀ n, ‖v n‖ ≤ (1 : ℝ) :=
    fun n => (hunit _ (recursiveVector_mem G E v₀ hv₀ hstep n)).le
  have hdense : closure (Set.range (stageMean v)) = recursiveConvexSet G v₀ :=
    closure_range_stageMean_eq v 1 (by norm_num) hv
  have himage : Set.MapsTo G (Set.range (stageMean v)) (recursiveConvexSet G v₀) := by
    rintro x ⟨n, rfl⟩
    rw [← recursiveVector_succ G v₀ n]
    exact subset_closure (subset_convexHull ℝ _ ⟨n+1, rfl⟩)
  have hcont : ContinuousOn G (closure (Set.range (stageMean v))) := by
    rw [hdense]
    exact hG.mono (recursiveConvexSet_subset G E v₀ hv₀ hE hstep)
  have h := himage.closure_of_continuousOn hcont
  rw [hdense, (isClosed_recursiveConvexSet G v₀).closure_eq] at h
  exact h

/-- No density or invariant-set premise: both are obtained from the positive recursion. -/
theorem exists_invariant_closed_convex (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hE : IsClosed E) (hunit : ∀ x ∈ E, ‖x‖ = 1)
    (hG : ContinuousOn G E) (hstep : PositivePrefixGrowth G E) :
    ∃ C : Set X, C.Nonempty ∧ IsClosed C ∧ Bornology.IsBounded C ∧
      Convex ℝ C ∧ C ⊆ E ∧ Set.MapsTo G C C := by
  have hsub := recursiveConvexSet_subset G E v₀ hv₀ hE hstep
  refine ⟨recursiveConvexSet G v₀, recursiveConvexSet_nonempty G v₀,
    isClosed_recursiveConvexSet G v₀, ?_, convex_recursiveConvexSet G v₀, hsub,
    recursiveConvexSet_invariant G E v₀ hv₀ hE hunit hG hstep⟩
  apply isBounded_iff_forall_norm_le.mpr
  exact ⟨1, fun x hx => (hunit x (hsub hx)).le⟩

end Tingley

end

end OAI


