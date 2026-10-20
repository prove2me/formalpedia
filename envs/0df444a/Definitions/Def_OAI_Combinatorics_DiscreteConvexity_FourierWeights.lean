-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights
-- name    : OAI_Combinatorics_DiscreteConvexity_FourierWeights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:39:14.272874+00:00
-- url     : https://prove2.me/theorems/b589321d-b8a0-443c-92da-c87262c6465f
-- title:
--   Alternating corrections, partial Fourier coefficients and their squared weights
-- statement:
--   Let $V$ be finite, $q\in\mathbb{R}$ and $f:\{0,1\}^V\to\mathbb{R}$.
--
--   1. **Correction.** $\gamma_q(0)=1-q$ and $\gamma_q(1)=-(1-q)$.
--   2. **Row kernel.** For $U\subseteq V$ and $x\in\{0,1\}^V$,
--   $$
--   K_U(x)=\prod_{i\in U}\gamma_q(x_i)\prod_{i\notin U}\bigl(q\text{ if }x_i=1,\ 1-q\text{ if }x_i=0\bigr).
--   $$
--   3. **Coefficients and weights.** $b_q(f,U)=\sum_xf(x)K_U(x)$ and $w_q(f,U)=b_q(f,U)^2$.
--   4. **Empty set.** $K_\emptyset$ is the $q$-biased product mass, so $b_q(f,\emptyset)$ is the $q$-biased expectation of $f$.
--
--   Up to the factor $(1-q)^{|U|}$, $b_q(f,U)$ is an alternating sum over the coordinates in $U$ of the $q$-biased expectation over the rest. These coefficients satisfy a biased Parseval identity and supply the weights of the covering argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/FourierWeights.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/FourierWeights.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators

namespace TalagrandDiscreteConvexity

/-- The alternating factor for a coordinate inside the differentiated set. -/
def correction (q : ℝ) (bit : Bool) : ℝ :=
  if bit then -(1 - q) else 1 - q

@[simp] theorem correction_false (q : ℝ) : correction q false = 1 - q := rfl

@[simp] theorem correction_true (q : ℝ) : correction q true = -(1 - q) := rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Coordinate product defining the alternating partial expectation. -/
def rowKernel (q : ℝ) (U : Finset V) (x : V → Bool) : ℝ :=
  ∏ i, if i ∈ U then correction q (x i) else bitWeight q (x i)

/-- Exactly `(1-q)^|U|` times the alternating sum over the coordinates in `U`,
with independent Bernoulli expectation on its complement. -/
def b (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) : ℝ :=
  ∑ x, f x * rowKernel q U x

/-- The nonnegative weights used by both global and exceptional-set bounds. -/
def w (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) : ℝ :=
  (b q f U) ^ 2

@[simp] theorem rowKernel_empty (q : ℝ) (x : V → Bool) :
    rowKernel q ∅ x = cubeWeight q x := by
  simp [rowKernel, cubeWeight]

/-- The empty coefficient is the original biased expectation. -/
@[simp] theorem b_empty (q : ℝ) (f : (V → Bool) → ℝ) :
    b q f ∅ = cubeExpectation q f := by
  simp only [b, rowKernel_empty, cubeExpectation]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

end TalagrandDiscreteConvexity

end

end OAI


