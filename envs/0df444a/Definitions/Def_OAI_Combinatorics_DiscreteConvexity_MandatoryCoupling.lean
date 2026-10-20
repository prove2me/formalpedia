-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_MandatoryCoupling
-- name    : OAI_Combinatorics_DiscreteConvexity_MandatoryCoupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:43:24.88825+00:00
-- url     : https://prove2.me/theorems/e5701942-4d08-4cea-b706-8dce23c8fc1f
-- title:
--   Mandatory-row coupling at high density
-- statement:
--   Let $L>1$ and $p<1$ with $Lp\ge1$.
--
--   1. **Extra probability.** $p'=\dfrac{p-1/L}{1-1/L}$, which satisfies $0\le p'<1$.
--   2. **Columns.** A column consists of a mandatory row index $j^*\in\{1,\dots,L\}$, uniform, and independent marks $m_j\in\{0,1\}$ with $\Pr(m_j=1)=p'$. The column puts its coordinate in row $j$ when
--   $$
--   j=j^*\ \text{ or }\ m_j=1 .
--   $$
--   3. **Arrays.** Columns are chosen independently for the coordinates of $X$, and row $j$ is the set of coordinates whose column puts them in row $j$.
--
--   Each coordinate lies in row $j$ with probability $\frac1L+(1-\frac1L)p'=p$, so every row is a $p$-random subset. The union of the rows is always all of $X$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/MandatoryCoupling.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/MandatoryCoupling.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_LabelCoupling

namespace OAI

/-!
# The mandatory-row coupling at high density

The auxiliary inclusion probability is valid throughout the closed high-density
regime `1 ≤ L * p`, including equality, when it is zero.

At each coordinate the mandatory label is uniform and independent of the
independent Bernoulli marks. Taking a product of these laws across coordinates
gives each row its full Bernoulli subset law. The union is full in every outcome;
only marginal probabilities are used to obtain simultaneous family membership.
-/

noncomputable section

namespace TalagrandDiscreteConvexity

/-- The extra inclusion probability after the uniformly chosen mandatory row. -/
def mandatoryParameter (L : ℕ) (p : ℝ) : ℝ :=
  (p - 1 / (L : ℝ)) / (1 - 1 / (L : ℝ))

theorem mandatoryParameter_den_pos {L : ℕ} (hL : 1 < L) :
    0 < 1 - 1 / (L : ℝ) := by
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_trans zero_lt_one hLreal
  exact sub_pos.mpr ((div_lt_one hLpos).mpr hLreal)

theorem mandatoryParameter_nonneg {L : ℕ} {p : ℝ}
    (hL : 1 < L) (hLp : 1 ≤ (L : ℝ) * p) :
    0 ≤ mandatoryParameter L p := by
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_trans zero_lt_one hLreal
  have hbase : 1 / (L : ℝ) ≤ p :=
    (div_le_iff₀ hLpos).mpr (by simpa only [mul_comm] using hLp)
  exact div_nonneg (sub_nonneg.mpr hbase) (mandatoryParameter_den_pos hL).le

theorem mandatoryParameter_lt_one {L : ℕ} {p : ℝ}
    (hL : 1 < L) (hp : p < 1) : mandatoryParameter L p < 1 := by
  exact (div_lt_one (mandatoryParameter_den_pos hL)).mpr
    (sub_lt_sub_right hp (1 / (L : ℝ)))

/-- A coordinate chooses one compulsory row, together with independent marks.
The mark in the compulsory row may be sampled and then ignored. -/
abbrev MandatoryColumn (L : ℕ) := Fin L × (Fin L → Bool)

def mandatoryBit {L : ℕ} (j : Fin L) (z : MandatoryColumn L) : Bool :=
  decide (z.1 = j ∨ z.2 j = true)

@[simp] theorem mandatoryBit_mandatory {L : ℕ} (z : MandatoryColumn L) :
    mandatoryBit z.1 z = true := by
  simp [mandatoryBit]

/-- Uniform mandatory label, independent of all the extra row marks. -/
def mandatoryColumnLaw {L : ℕ} (hL : 1 < L) (p : ℝ) (hp : p < 1)
    (hLp : 1 ≤ (L : ℝ) * p) : FiniteLaw (MandatoryColumn L) := by
  let : Nonempty (Fin L) := ⟨⟨0, lt_trans Nat.zero_lt_one hL⟩⟩
  exact (FiniteLaw.uniform (Fin L)).prod
    (FiniteLaw.iid (bitLaw (mandatoryParameter L p)
      (mandatoryParameter_nonneg hL hLp) (mandatoryParameter_lt_one hL hp).le) L)

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Read the sets in all rows of a coordinate array. -/
def mandatoryRows {L : ℕ} (ω : α → MandatoryColumn L) (j : Fin L) : Finset α :=
  cubeSet (fun i => mandatoryBit j (ω i))

/-- The coordinate choices are independent; the rows need not be independent. -/
def mandatoryArrayLaw {L : ℕ} (hL : 1 < L) (p : ℝ) (hp : p < 1)
    (hLp : 1 ≤ (L : ℝ) * p) : FiniteLaw (α → MandatoryColumn L) :=
  FiniteLaw.pi (fun _ : α => mandatoryColumnLaw hL p hp hLp)

end TalagrandDiscreteConvexity

end

end OAI


