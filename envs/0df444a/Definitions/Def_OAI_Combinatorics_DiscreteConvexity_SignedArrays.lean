-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_SignedArrays
-- name    : OAI_Combinatorics_DiscreteConvexity_SignedArrays
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:41:19.060911+00:00
-- url     : https://prove2.me/theorems/10e748ec-eb75-4a49-ae0e-e3b90ff05d0e
-- title:
--   Signed mass of a Boolean array relative to a set of columns
-- statement:
--   Let $V$ be finite, $q\in\mathbb{R}$, $S\subseteq V$, and $X=(X_{j,i})$ an array with rows $j=1,\dots,k$ and columns $i\in V$ of bits. With $\gamma_q(0)=1-q$, $\gamma_q(1)=-(1-q)$ and bit masses $q,1-q$, the signed mass is
--   $$
--   \sigma_S(X)=\prod_{i\in V}\Bigl(\prod_{j}\mathrm{mass}_q(X_{j,i})-[i\in S]\prod_j\gamma_q(X_{j,i})\Bigr).
--   $$
--
--   An all-zero column in $S$ has signed factor $(1-q)^k-(1-q)^k=0$. If $S$ is exceptional for $k$ rows of the family, every array whose rows lie in the family has some all-zero column in $S$. Expanding the product turns this into a signed identity between the coefficients $b_q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/SignedArrays.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/SignedArrays.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Signed arrays force weight on every exceptional set

The arrays have one common set of rows. Each column in `S` receives the
Bernoulli product mass minus the product of the alternating corrections.
All-zero columns in `S` have zero signed mass. This gives pointwise vanishing
for exceptional sets, without any nonnegativity assumption on these masses.
Expanding the column products and summing independently over the rows gives
the exact signed coefficient identity.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {V : Type*} [Fintype V] [DecidableEq V]

def signedArrayMass (q : ℝ) {k : ℕ} (S : Finset V)
    (X : Fin k → V → Bool) : ℝ :=
  ∏ i, ((∏ j, bitWeight q (X j i)) -
    if i ∈ S then ∏ j, correction q (X j i) else 0)

end TalagrandDiscreteConvexity

end

end OAI


