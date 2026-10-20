-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
-- name    : OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:29:08.492369+00:00
-- url     : https://prove2.me/theorems/394b2774-d04d-487d-88d5-f46ba7b1b666
-- title:
--   The independent multiscale color law
-- statement:
--   Fix $p\in\mathbb{R}$ and $s\in\mathbb{N}$. Colors are $0,\dots,s$, and a coloring of a finite set $X$ assigns a color to each point.
--
--   1. **Scale sum.** $\Sigma_s=\sum_{i=0}^{s-1}256^{\,i+1}$, with $\Sigma_0=0$.
--   2. **Color probabilities.**
--   $$
--   \Pr(c)=\begin{cases}256^{\,c+1}p,&c<s,\\1-p\,\Sigma_s,&c=s.\end{cases}
--   $$
--      These always sum to $1$. If $p>0$ and $p\Sigma_s\le\frac12$, all of them are positive, giving a finite law on colors.
--   3. **Colorings.** The mass of a coloring $a$ is $\prod_{x\in X}\Pr(a(x))$, and the coloring law colors the points independently.
--
--   The small colors are rare at density $p$, with probabilities increasing geometrically by the factor $256$. The last color absorbs the remaining mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/ProbabilityColors.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ProbabilityColors.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandExpectationThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation

namespace OAI

/-!
# The actual independent color law

Colors are indexed from zero; their numerical levels are one larger. The
first `s` colors have masses `256^(i+1) * p`, and the final color carries the
remaining mass. All laws below use these literal weights.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandThreshold

abbrev Color (s : ℕ) := Fin (s + 1)

abbrev Coloring (α : Type*) (s : ℕ) := α → Color s

/-- The geometric sum appearing in the admissibility condition. -/
def scaleSum (s : ℕ) : ℝ := ∑ i : Fin s, (256 : ℝ) ^ (i.val + 1)

/-- The literal single-coordinate probabilities from the selector experiment. -/
def colorProb (p : ℝ) (s : ℕ) (c : Color s) : ℝ :=
  if c.val < s then (256 : ℝ) ^ (c.val + 1) * p else 1 - p * scaleSum s

@[simp] theorem scaleSum_zero : scaleSum 0 = 0 := by
  simp [scaleSum]

@[simp] theorem colorProb_castSucc (p : ℝ) (s : ℕ) (i : Fin s) :
    colorProb p s i.castSucc = (256 : ℝ) ^ (i.val + 1) * p := by
  simp [colorProb, i.isLt]

@[simp] theorem colorProb_last (p : ℝ) (s : ℕ) :
    colorProb p s (Fin.last s) = 1 - p * scaleSum s := by
  simp [colorProb]

/-- Normalization is an algebraic identity, even before assuming positivity. -/
theorem sum_colorProb (p : ℝ) (s : ℕ) : ∑ c : Color s, colorProb p s c = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [colorProb_castSucc, colorProb_last]
  rw [← Finset.sum_mul]
  change scaleSum s * p + (1 - p * scaleSum s) = 1
  ring

theorem colorProb_pos (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (c : Color s) : 0 < colorProb p s c := by
  unfold colorProb
  split_ifs
  · exact mul_pos (pow_pos (by norm_num) _) hp
  · linarith

theorem colorProb_nonneg (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (c : Color s) : 0 ≤ colorProb p s c :=
  (colorProb_pos p s hp hs c).le

def colorLaw (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) : FiniteLaw (Color s) where
  weight := colorProb p s
  nonneg := colorProb_nonneg p s hp hs
  total := sum_colorProb p s

@[simp] theorem colorLaw_weight (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (c : Color s) :
    (colorLaw p s hp hs).weight c = colorProb p s c := rfl

variable {α : Type*} [Fintype α]

/-- Probability mass of a complete coloring, with one factor per vertex. -/
def colorMass (p : ℝ) (s : ℕ) (a : Coloring α s) : ℝ :=
  ∏ x, colorProb p s (a x)

variable [DecidableEq α]

/-- The independent product law on exactly the original vertex set. -/
def coloringLaw (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) : FiniteLaw (Coloring α s) :=
  FiniteLaw.pi (fun _ : α => colorLaw p s hp hs)

@[simp] theorem coloringLaw_weight (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a : Coloring α s) :
    (coloringLaw p s hp hs).weight a = colorMass p s a := rfl

end TalagrandThreshold

end

end OAI


