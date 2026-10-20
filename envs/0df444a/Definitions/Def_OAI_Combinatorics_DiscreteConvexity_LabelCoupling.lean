-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_LabelCoupling
-- name    : OAI_Combinatorics_DiscreteConvexity_LabelCoupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:42:57.628142+00:00
-- url     : https://prove2.me/theorems/65043dd6-8841-4da1-9418-abeeee85bc94
-- title:
--   Independent coordinate labels producing dependent rows
-- statement:
--   Let $L\in\mathbb{N}$ and $p\ge0$ with $Lp\le1$.
--
--   1. **Label law.** On $\{0,1,\dots,L\}$, label $0$ has mass $1-Lp$ and each label $j\ge1$ has mass $p$. Hence label $j\ge1$ has probability $p$, label $0$ has probability $1-Lp$, and $\Pr(\text{label}\ne0)=Lp$.
--   2. **Samples.** Labels are chosen independently at each coordinate of a finite ground set $X$.
--   3. **Rows.** Row $j\in\{1,\dots,L\}$ is the set of coordinates with label $j$:
--   $$
--   R_j=\{i\in X:\ \omega_i=j\}.
--   $$
--
--   Each row is a $p$-random subset, and the union of the rows is an $Lp$-random subset. The rows are not independent, which is not needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/LabelCoupling.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/LabelCoupling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandDiscreteConvexity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_SignedArrays
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_ProductProbability

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

noncomputable section

/-- One coordinate receives label zero with the residual mass, and each of the
`L` row labels with mass `p`. This does not assert independence of the rows. -/
def labelLaw (L : ℕ) (p : ℝ) (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    FiniteLaw (Fin (L + 1)) := by
  classical
  exact {
    weight := fun j => if j = 0 then 1 - (L : ℝ) * p else p
    nonneg := fun j => by
      split_ifs
      · exact sub_nonneg.mpr hLp
      · exact hp
    total := by
      rw [Fin.sum_univ_succ]
      simp [nsmul_eq_mul] }

@[simp] theorem labelLaw_weight_zero (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    (labelLaw L p hp hLp).weight 0 = 1 - (L : ℝ) * p := by
  simp [labelLaw]

@[simp] theorem labelLaw_weight_succ (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) (j : Fin L) :
    (labelLaw L p hp hLp).weight j.succ = p := by
  simp [labelLaw]

@[simp] theorem labelLaw_prob_zero (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    (labelLaw L p hp hLp).prob (fun j => j = 0) = 1 - (L : ℝ) * p := by
  classical
  unfold FiniteLaw.prob
  refine (Finset.sum_eq_single (0 : Fin (L + 1)) ?_ ?_).trans ?_
  · intro k _ hk
    exact ite_eq_right hk
  · simp
  · simp only [ite_true, labelLaw_weight_zero]

@[simp] theorem labelLaw_prob_succ (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) (j : Fin L) :
    (labelLaw L p hp hLp).prob (fun k => k = j.succ) = p := by
  classical
  unfold FiniteLaw.prob
  refine (Finset.sum_eq_single j.succ ?_ ?_).trans ?_
  · intro k _ hk
    exact ite_eq_right hk
  · simp
  · simp only [ite_true, labelLaw_weight_succ]

@[simp] theorem labelLaw_prob_nonzero (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    (labelLaw L p hp hLp).prob (fun j => j ≠ 0) = (L : ℝ) * p := by
  have h := (labelLaw L p hp hLp).prob_compl (fun j => j = 0)
  simpa only [labelLaw_prob_zero, sub_sub_cancel] using h

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Independent coordinate labels; the row membership events may be dependent. -/
def labelSamples (L : ℕ) (p : ℝ) (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    FiniteLaw (α → Fin (L + 1)) :=
  FiniteLaw.pi (fun _ : α => labelLaw L p hp hLp)

/-- Row `j` contains exactly the coordinates labeled by its successor label. -/
def labelRow {L : ℕ} (ω : α → Fin (L + 1)) (j : Fin L) : Finset α := by
  classical
  exact cubeSet (fun i => decide (ω i = j.succ))

omit [DecidableEq α] in
@[simp] theorem mem_labelRow {L : ℕ} {ω : α → Fin (L + 1)}
    {j : Fin L} {i : α} : i ∈ labelRow ω j ↔ ω i = j.succ := by
  classical
  simp [labelRow]

end

end TalagrandDiscreteConvexity

end OAI


