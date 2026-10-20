-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_DefectAttainment
-- name    : OAI_Analysis_SphereIsometry_DefectAttainment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:04:01.135784+00:00
-- url     : https://prove2.me/theorems/97765d6d-2d89-4d9c-af12-b4fddfd94493
-- title:
--   Attaining the maximal defect in completed ultrapowers
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $f:S_X\to S_Y$ be a bijective isometry of nontrivial spaces.
--
--   1. **Completed ultrapower isometry.** $F$ is the isometry induced on the ultrapower spheres along the fixed free ultrafilter, followed by completion. It is a bijective isometry between unit spheres of nonzero real Banach spaces, and $\delta^F_q([s],[t])=\lim_{\mathcal U}\delta^f_q(s_n,t_n)$ on unit classes.
--   2. **Attainment.** If $M_f>0$, then $F$ and $F^{-1}$ both have defect bound $M_f$, and for some $t\in(0,1)$ and some $x,y$,
--   $$
--   \delta^F_t(x,y)=M_f\quad\text{or}\quad\delta^{F^{-1}}_t(x,y)=M_f .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/DefectAttainment.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/DefectAttainment.lean by skeleton subtraction
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

namespace OAI

/-!
# Positive maximal defect is attained on actual completed ultranorm spaces

The final spaces, sphere isometry, inverse, and bound are all constructed. The
orientation disjunction keeps the same original maximal absolute defect.
-/

noncomputable section
namespace Tingley
open Filter
open scoped Topology

universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [Nontrivial X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Nontrivial Y]

/-- The actual coordinatewise sphere equivalence followed by ambient completion. -/
def completedUltraSphereEquiv (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    UnitSphere (UltraCompletion U X) ≃ᵢ UnitSphere (UltraCompletion U Y) :=
  completedSphereEquiv (ultraSphereEquiv U f)

@[simp] theorem completedUltraSphereEquiv_symm (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    (completedUltraSphereEquiv U f).symm = completedUltraSphereEquiv U f.symm := by
  simp only [completedUltraSphereEquiv, completedSphereEquiv_symm, ultraSphereEquiv_symm]

/-- Exact fixed-radius formula on the canonical embedded unit classes. -/
theorem signedDefect_completedUltraSphereEquiv (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (q : ℝ) (s t : ℕ → UnitSphere X) :
    signedDefect (completedUltraSphereEquiv U f) q
      (sphereCoe (UltraQuotient U X) (unitClass U s))
      (sphereCoe (UltraQuotient U X) (unitClass U t)) =
        realULim U (fun n => signedDefect f q (s n) (t n)) := by
  exact (signedDefect_completedSphereEquiv_coe (ultraSphereEquiv U f) q
    (unitClass U s) (unitClass U t)).trans (signedDefect_ultraSphereEquiv U f q s t)

theorem HasDefectBound.completedUltraSphereEquiv
    {f : UnitSphere X ≃ᵢ UnitSphere Y} {M : ℝ} (h : HasDefectBound f M)
    (U : Ultrafilter ℕ) : HasDefectBound (completedUltraSphereEquiv U f) M :=
  (h.ultraSphereEquiv U).completedSphereEquiv

/-- Positive original maximal absolute defect is attained, with the same global
bound, in one orientation on explicitly constructed nonzero real Banach spaces. -/
theorem positive_maxDefect_attained_or_inverse
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (hM : 0 < maxDefect f) :
    let F := completedUltraSphereEquiv freeUltrafilter f
    HasDefectBound F (maxDefect f) ∧
    HasDefectBound F.symm (maxDefect f) ∧
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      ((∃ x y : UnitSphere (UltraCompletion freeUltrafilter X),
          signedDefect F t x y = maxDefect f) ∨
       (∃ x y : UnitSphere (UltraCompletion freeUltrafilter Y),
          signedDefect F.symm t x y = maxDefect f)) := by
  have hbound := (hasDefectBound_maxDefect f).completedUltraSphereEquiv freeUltrafilter
  refine ⟨hbound, hbound.symm, ?_⟩
  obtain ⟨t, ht, hseq | hseq⟩ := exists_fixed_radius_defect_sequence f hM
  · obtain ⟨s, r, hlim⟩ := hseq
    refine ⟨t, ht, Or.inl ⟨sphereCoe _ (unitClass freeUltrafilter s),
      sphereCoe _ (unitClass freeUltrafilter r), ?_⟩⟩
    rw [signedDefect_completedUltraSphereEquiv]
    exact realULim_eq_of_tendsto freeUltrafilter hlim
  · obtain ⟨s, r, hlim⟩ := hseq
    refine ⟨t, ht, Or.inr ⟨sphereCoe _ (unitClass freeUltrafilter s),
      sphereCoe _ (unitClass freeUltrafilter r), ?_⟩⟩
    rw [completedUltraSphereEquiv_symm, signedDefect_completedUltraSphereEquiv]
    exact realULim_eq_of_tendsto freeUltrafilter hlim

end Tingley

end

end OAI


