-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_AlignmentSet
-- name    : OAI_Analysis_SphereIsometry_AlignmentSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:12:14.431577+00:00
-- url     : https://prove2.me/theorems/d571c146-bcee-4f29-9c6a-f1ea982e3c44
-- title:
--   An invariant convex set for the return map
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Fix a bijective sphere isometry $f$ with defect bound $M$, a base point $y$ and $t\in(0,1)$; for a direction $v$ the return map uses the contact radii $p(v),s(v),u(v),r(v)\in[1-t,1+t]$ and returns $R(v)\in S_X$, and the extremal set consists of the directions with $s(v)-p(v)=M$.
--
--   1. **Return-invariant convex set.** If $\delta_t(x_0,y)=M$ for some $x_0$, there is a nonempty closed bounded convex
--   $$
--   C\subseteq\{\text{extremal directions}\}
--   $$
--   on which the (totalized) return map is continuous and maps $C$ into itself. It is obtained from the positive scheduling recursion, since common supports make extremal directions grow in positive hulls. No convexity of the whole extremal set is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/AlignmentSet.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/AlignmentSet.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_InvariantConvexSet

namespace OAI

/-!
# The actual closed convex invariant subset of the extremal sphere

The generic positive scheduling theorem is instantiated with the proved
common-support hull growth. No convexity of the full extremal set is assumed.
-/

noncomputable section

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_return_invariant_convex
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y x₀ : UnitSphere X)
    (t M : ℝ) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hatt : signedDefect f t x₀ y = M) :
    ∃ C : Set X, C.Nonempty ∧ IsClosed C ∧ Bornology.IsBounded C ∧
      Convex ℝ C ∧ C ⊆ extremalSet f y t ht M ∧
      ContinuousOn (returnAmbient f y t ht) C ∧
      Set.MapsTo (returnAmbient f y t ht) C C := by
  obtain ⟨v₀, hv₀⟩ := extremalSet_nonempty_of_attained f y t ht M x₀ hatt
  have hcont : ContinuousOn (returnAmbient f y t ht) (extremalSet f y t ht M) :=
    (continuousOn_returnAmbient f y t ht).mono
      (fun _ hv => norm_eq_one_of_mem_extremalSet f y t ht M hv)
  obtain ⟨C, hCne, hCc, hCb, hCconv, hCE, hGC⟩ :=
    exists_invariant_closed_convex (returnAmbient f y t ht)
      (extremalSet f y t ht M) v₀ hv₀ (isClosed_extremalSet f y t ht M)
      (fun _ hv => norm_eq_one_of_mem_extremalSet f y t ht M hv) hcont
      (positive_prefix_extension f y t ht M hb)
  exact ⟨C, hCne, hCc, hCb, hCconv, hCE, hcont.mono hCE, hGC⟩

end Tingley

end

end OAI


