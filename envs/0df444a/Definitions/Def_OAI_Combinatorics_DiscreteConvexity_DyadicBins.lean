-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
-- name    : OAI_Combinatorics_DiscreteConvexity_DyadicBins
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:32:19.173157+00:00
-- url     : https://prove2.me/theorems/f4ba921b-8b87-439d-8e92-807e391ca6db
-- title:
--   The dyadic exponent of a positive weight
-- statement:
--   For a real $w>0$, let $m$ be the least natural number with $(1/2)^m<w$. The dyadic exponent of $w$ is
--   $$
--   e(w)=m-1,
--   $$
--   and $e(w)=0$ for $w\le0$ (this value is irrelevant).
--
--   For $0<w\le1$ this places $w$ in the dyadic bin $\bigl((1/2)^{e(w)+1},(1/2)^{e(w)}\bigr]$. A weight equal to a dyadic endpoint belongs to the bin whose upper endpoint it is.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/DyadicBins.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/DyadicBins.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Dyadic bins for positive weights

The exponent of a weight is determined by the first power of `1 / 2`
strictly below it.  In particular, a weight equal to a dyadic endpoint
belongs to the bin whose upper endpoint it equals.
-/

namespace TalagrandDiscreteConvexity

/-- The dyadic exponent of a positive weight.  Its value at a nonpositive
weight is irrelevant to the bin partition and is fixed to zero. -/
noncomputable def binExponent (w : ℝ) : ℕ := by
  classical
  exact if hw : 0 < w then
    Nat.find (exists_pow_lt_of_lt_one hw (by norm_num : (1 / 2 : ℝ) < 1)) - 1
  else 0

end TalagrandDiscreteConvexity

end OAI


