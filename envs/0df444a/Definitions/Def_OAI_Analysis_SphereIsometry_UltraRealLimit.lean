-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_UltraRealLimit
-- name    : OAI_Analysis_SphereIsometry_UltraRealLimit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T20:59:09.611799+00:00
-- url     : https://prove2.me/theorems/848b7017-ca77-4a12-907a-721f90759278
-- title:
--   Limits of bounded real sequences along ultrafilters
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords.
--
--   1. **Bounded sequences.** $(a_n)$ with $\sup_n|a_n|<\infty$. They are closed under sums, negation, differences and absolute values.
--   2. **Ultralimit.** For an ultrafilter $\mathcal U$ on $\mathbb N$, $\lim_{\mathcal U}a_n$ is the chosen limit along $\mathcal U$. Every bounded sequence converges along $\mathcal U$ to it, by compactness of closed intervals. It is additive, homogeneous, commutes with $|\cdot|$, and preserves eventual inequalities.
--   3. **Free ultrafilter.** A fixed ultrafilter $\mathcal U_\infty$ finer than the cofinite filter, so ordinary limits are also limits along $\mathcal U_\infty$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/UltraRealLimit.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/UltraRealLimit.lean by skeleton subtraction
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

namespace OAI

/-!
# Real ultralimits of bounded sequences

Every bounded real sequence converges along an ultrafilter, by compactness of a
closed real interval. All identities below use this convergence or an explicitly
given limit, so they do not depend on the fallback value of `limUnder`.
-/

noncomputable section

open Filter
open scoped Topology

namespace Tingley

/-- A real sequence has a uniform absolute-value bound. -/
def RealSeqBounded (f : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n, |f n| ≤ B

namespace RealSeqBounded

variable {f g : ℕ → ℝ}

theorem add (hf : RealSeqBounded f) (hg : RealSeqBounded g) :
    RealSeqBounded (fun n => f n + g n) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨C, hC⟩ := hg
  exact ⟨B + C, fun n => (abs_add_le (f n) (g n)).trans (add_le_add (hB n) (hC n))⟩

theorem neg (hf : RealSeqBounded f) : RealSeqBounded (fun n => -f n) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  simpa only [abs_neg] using hB n

theorem sub (hf : RealSeqBounded f) (hg : RealSeqBounded g) :
    RealSeqBounded (fun n => f n - g n) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem abs (hf : RealSeqBounded f) : RealSeqBounded (fun n => |f n|) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  simpa only [abs_abs] using hB n

end RealSeqBounded

/-- The chosen real limit along an ultrafilter. Use `tendsto_realULim` to establish
that this value is a limit for a bounded sequence. -/
def realULim (U : Ultrafilter ℕ) (f : ℕ → ℝ) : ℝ :=
  Filter.limUnder (U : Filter ℕ) f

variable {f g : ℕ → ℝ}

/-- Bounded real sequences converge along every ultrafilter. -/
theorem tendsto_realULim (U : Ultrafilter ℕ) (hf : RealSeqBounded f) :
    Tendsto f (U : Filter ℕ) (𝓝 (realULim U f)) := by
  obtain ⟨B, hB⟩ := hf
  have hmem : Set.Icc (-B) B ∈ Ultrafilter.map f U := by
    change ∀ᶠ n in (U : Filter ℕ), f n ∈ Set.Icc (-B) B
    exact Filter.Eventually.of_forall fun n => abs_le.mp (hB n)
  obtain ⟨a, _ha, hlim⟩ :=
    isCompact_Icc.ultrafilter_le_nhds' (Ultrafilter.map f U) hmem
  have ha : Tendsto f (U : Filter ℕ) (𝓝 a) := hlim
  exact tendsto_nhds_limUnder ⟨a, ha⟩

/-- A known limit determines the chosen ultralimit, without a boundedness premise. -/
theorem realULim_eq_of_tendsto (U : Ultrafilter ℕ) {a : ℝ}
    (h : Tendsto f (U : Filter ℕ) (𝓝 a)) : realULim U f = a :=
  h.limUnder_eq

@[simp]
theorem realULim_const (U : Ultrafilter ℕ) (c : ℝ) :
    realULim U (fun _ : ℕ => c) = c :=
  realULim_eq_of_tendsto U tendsto_const_nhds

theorem realULim_add (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) :
    realULim U (fun n => f n + g n) = realULim U f + realULim U g :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).add (tendsto_realULim U hg))

theorem realULim_sub (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) :
    realULim U (fun n => f n - g n) = realULim U f - realULim U g :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).sub (tendsto_realULim U hg))

theorem realULim_const_mul (U : Ultrafilter ℕ) (c : ℝ) (hf : RealSeqBounded f) :
    realULim U (fun n => c * f n) = c * realULim U f :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).const_mul c)

theorem realULim_abs (U : Ultrafilter ℕ) (hf : RealSeqBounded f) :
    realULim U (fun n => |f n|) = |realULim U f| :=
  realULim_eq_of_tendsto U (tendsto_realULim U hf).abs

/-- Eventual inequalities pass to the limits of bounded real sequences. -/
theorem realULim_le_realULim (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) (h : ∀ᶠ n in (U : Filter ℕ), f n ≤ g n) :
    realULim U f ≤ realULim U g :=
  le_of_tendsto_of_tendsto (tendsto_realULim U hf) (tendsto_realULim U hg) h

theorem realULim_le_of_eventually_le (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    {c : ℝ} (h : ∀ᶠ n in (U : Filter ℕ), f n ≤ c) : realULim U f ≤ c :=
  le_of_tendsto (tendsto_realULim U hf) h

/-- The actual free ultrafilter used for the bounded-sequence quotient. -/
def freeUltrafilter : Ultrafilter ℕ := Filter.hyperfilter ℕ

theorem freeUltrafilter_le_atTop : (freeUltrafilter : Filter ℕ) ≤ Filter.atTop :=
  Nat.hyperfilter_le_atTop

/-- Ordinary sequential convergence also holds along the fixed free ultrafilter. -/
theorem tendsto_freeUltrafilter_of_tendsto_atTop {α : Type*} [TopologicalSpace α]
    {a : ℕ → α} {x : α} (h : Tendsto a atTop (𝓝 x)) :
    Tendsto a (freeUltrafilter : Filter ℕ) (𝓝 x) :=
  h.mono_left freeUltrafilter_le_atTop

end Tingley

end

end OAI


