-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_DefectSequence
-- name    : OAI_Analysis_SphereIsometry_DefectSequence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:01:47.923436+00:00
-- url     : https://prove2.me/theorems/8076a2ec-d341-484f-ae05-31d1d1fe7aeb
-- title:
--   Fixed-radius sequences realizing the maximal defect
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $f$ be a sphere isometry with maximal defect $M_f>0$.
--
--   1. **Fixed radius.** If $q_n\to t$ and $\delta_{q_n}(x_n,y_n)\to M$ along a filter, then also $\delta_t(x_n,y_n)\to M$, by the Lipschitz bound in $q$.
--   2. **Interior radius.** A positive limiting defect forces $t\in(0,1)$, since $|\delta_q|\le2q$ and $\delta_1=0$.
--   3. **Witness sequences.** There are $t\in(0,1)$ and sequences $x_n,y_n$ such that, along the fixed free ultrafilter, either
--   $$
--   \delta_t(x_n,y_n)\to M_f\quad\text{or}\quad\delta^{f^{-1}}_t(x_n,y_n)\to M_f .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/DefectSequence.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/DefectSequence.lean by skeleton subtraction
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

namespace OAI

/-!
# A positive signed extremal sequence at a fixed radius

One fixed free ultrafilter chooses the orientation and the radius. The conclusion
is convergence along that actual filter, not an asserted compactness of spheres.
-/

noncomputable section
namespace Tingley
open Filter
open scoped Topology

universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Uniform radius control replaces a varying radius by its actual scalar limit. -/
theorem tendsto_signedDefect_fixed_radius
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (x y : ℕ → UnitSphere X)
    (q : ℕ → ℝ) {l : Filter ℕ} {t M : ℝ}
    (hq : Tendsto q l (𝓝 t))
    (hD : Tendsto (fun n => signedDefect f (q n) (x n) (y n)) l (𝓝 M)) :
    Tendsto (fun n => signedDefect f t (x n) (y n)) l (𝓝 M) := by
  have herr : Tendsto (fun n => 2 * |q n - t|) l (𝓝 0) := by
    simpa using ((hq.sub (tendsto_const_nhds (x := t))).abs.const_mul 2)
  have hlo := hD.sub herr
  have hhi := hD.add herr
  simp only [sub_zero, add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro n
    change signedDefect f (q n) (x n) (y n) - 2 * |q n - t| ≤
      signedDefect f t (x n) (y n)
    have h := (abs_le.mp (signedDefect_lipschitz f (q n) t (x n) (y n))).2
    linarith
  · intro n
    change signedDefect f t (x n) (y n) ≤
      signedDefect f (q n) (x n) (y n) + 2 * |q n - t|
    have h := (abs_le.mp (signedDefect_lipschitz f (q n) t (x n) (y n))).1
    linarith

/-- Positive limiting defect forces a strictly interior radius. -/
theorem radius_interior_of_positive_defect_limit
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (x y : ℕ → UnitSphere X)
    (U : Ultrafilter ℕ) {t M : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hM : 0 < M)
    (hD : Tendsto (fun n => signedDefect f t (x n) (y n)) (U : Filter ℕ) (𝓝 M)) :
    t ∈ Set.Ioo (0 : ℝ) 1 := by
  have habs : Tendsto (fun n => |signedDefect f t (x n) (y n)|)
      (U : Filter ℕ) (𝓝 M) := by
    simpa only [abs_of_pos hM] using hD.abs
  have h0 : M ≤ 2 * t :=
    le_of_tendsto_of_tendsto' habs tendsto_const_nhds
      (fun n => (signedDefect_le_endpoints f ht (x n) (y n)).1)
  have h1 : M ≤ 2 * (1 - t) :=
    le_of_tendsto_of_tendsto' habs tendsto_const_nhds
      (fun n => (signedDefect_le_endpoints f ht (x n) (y n)).2)
  constructor <;> linarith

/-- The absolute supremum has actual fixed-radius signed witnesses in one orientation. -/
theorem exists_fixed_radius_defect_sequence [Nontrivial X]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (hM : 0 < maxDefect f) :
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      ((∃ x y : ℕ → UnitSphere X,
          Tendsto (fun n => signedDefect f t (x n) (y n))
            (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f))) ∨
       (∃ x y : ℕ → UnitSphere Y,
          Tendsto (fun n => signedDefect f.symm t (x n) (y n))
            (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f)))) := by
  classical
  obtain ⟨d, _, hdlim, hdmem⟩ := exists_seq_tendsto_sSup
    (show (absoluteDefects f).Nonempty from ⟨0, zero_mem_absoluteDefects f⟩)
    (absoluteDefects_bddAbove f)
  change ∀ n, ∃ q ∈ Set.Icc (0 : ℝ) 1,
    ∃ x y : UnitSphere X, d n = |signedDefect f q x y| at hdmem
  choose q hq x y hd using hdmem
  have habs : Tendsto (fun n => |signedDefect f (q n) (x n) (y n)|)
      (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f)) := by
    have h := tendsto_freeUltrafilter_of_tendsto_atTop hdlim
    have heq : d = fun n => |signedDefect f (q n) (x n) (y n)| := funext hd
    simpa only [heq, maxDefect] using h
  have hqb : RealSeqBounded q := by
    refine ⟨1, fun n => ?_⟩
    simpa only [abs_of_nonneg (hq n).1] using (hq n).2
  let t := realULim freeUltrafilter q
  have hqt : Tendsto q (freeUltrafilter : Filter ℕ) (𝓝 t) :=
    tendsto_realULim freeUltrafilter hqb
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hqt (fun n => (hq n).1),
      le_of_tendsto_of_tendsto' hqt tendsto_const_nhds (fun n => (hq n).2)⟩
  rcases freeUltrafilter.em (fun n => 0 ≤ signedDefect f (q n) (x n) (y n)) with hpos | hneg
  · have hsign : Tendsto (fun n => signedDefect f (q n) (x n) (y n))
        (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f)) := by
      apply habs.congr'
      filter_upwards [hpos] with n hn
      exact abs_of_nonneg hn
    have hfixed := tendsto_signedDefect_fixed_radius f x y q hqt hsign
    exact ⟨t, radius_interior_of_positive_defect_limit f x y freeUltrafilter ht hM hfixed,
      Or.inl ⟨x, y, hfixed⟩⟩
  · have hsign : Tendsto (fun n => signedDefect f.symm (q n) (f (x n)) (f (y n)))
        (freeUltrafilter : Filter ℕ) (𝓝 (maxDefect f)) := by
      apply habs.congr'
      filter_upwards [hneg] with n hn
      rw [signedDefect_symm, abs_of_nonpos (le_of_lt (lt_of_not_ge hn))]
    have hfixed := tendsto_signedDefect_fixed_radius f.symm
      (fun n => f (x n)) (fun n => f (y n)) q hqt hsign
    exact ⟨t, radius_interior_of_positive_defect_limit f.symm
      (fun n => f (x n)) (fun n => f (y n)) freeUltrafilter ht hM hfixed,
      Or.inr ⟨_, _, hfixed⟩⟩

end Tingley

end

end OAI


