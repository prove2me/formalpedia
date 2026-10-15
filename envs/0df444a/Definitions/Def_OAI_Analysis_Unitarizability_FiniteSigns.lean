-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
-- name    : OAI_Analysis_Unitarizability_FiniteSigns
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:54:40.684666+00:00
-- url     : https://prove2.me/theorems/18e55aee-2bd6-44b1-a867-c40349f6650e
-- title:
--   Rademacher sign sums on the finite space of sign assignments
-- statement:
--   Let $J$ be a finite set. A *sign assignment* is a function $\sigma:J\to\{\mathrm{true},\mathrm{false}\}$; the $2^{|J|}$ assignments form a finite sample space in which every assignment has the same weight, so probabilities are counts divided by $2^{|J|}$ and expectations are averages over all assignments.
--
--   1. **Sign of a bit.** $\varepsilon(\mathrm{true})=1$ and $\varepsilon(\mathrm{false})=-1$.
--   2. **Signed sum.** For real coefficients $a:J\to\mathbb{R}$ and an assignment $\sigma$,
--   $$V_a(\sigma)=\sum_{j\in J}a_j\,\varepsilon(\sigma_j).$$
--
--   Under the uniform distribution the signs $\varepsilon(\sigma_j)$ are independent Rademacher variables and $V_a$ is a Rademacher sum. The module computes its exponential moments exactly, $\sum_{\sigma}e^{V_a(\sigma)}=2^{|J|}\prod_{j}\cosh a_j$, and derives sub-Gaussian tail bounds stated as explicit finite counts. These tails control the bilinear tests of random sign matrices and so lead to frames with good bounds on all small subfamilies.
--
--   **Formalization Note** The definitions are `FiniteSigns.sign : Bool → ℝ` and `FiniteSigns.value a σ`; decidable equality on `J` is supplied classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FiniteSigns.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FiniteSigns.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Dixmier mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

/-! Finite independent signs. Expectations are explicit finite sums over all sign
assignments with equal weight. -/
noncomputable section
namespace Dixmier
namespace FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
local instance instDecidableEq_oAI : DecidableEq J := Classical.decEq J

def sign (b : Bool) : ℝ := if b then 1 else -1

def value (a : J → ℝ) (σ : J → Bool) : ℝ := ∑ j, a j * sign (σ j)

end FiniteSigns
end Dixmier

end

end OAI


