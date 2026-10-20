-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_ProductProbability
-- name    : OAI_Combinatorics_DiscreteConvexity_ProductProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:42:26.262029+00:00
-- url     : https://prove2.me/theorems/1ca1689d-8481-4a92-8513-fa0c45320aed
-- title:
--   Pushforward of a finite law
-- statement:
--   Let $\mu$ be a finite law on $\Omega$ and $f:\Omega\to\Gamma$ a map into a finite set. The pushforward law $f_*\mu$ on $\Gamma$ has weights
--   $$
--   (f_*\mu)(\gamma)=\sum_{\omega:\ f(\omega)=\gamma}\mu(\omega).
--   $$
--
--   It is again a finite law. Marginals of product laws and laws of derived random sets are obtained as pushforwards.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/ProductProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/ProductProbability.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Marginals and pushforwards of finite product laws

All identities below follow from the weights of the actual finite laws.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandDiscreteConvexity.FiniteLaw

section ProductCoordinates

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

/-- Pushforward by summing the source weights in each fiber. -/
def map (μ : FiniteLaw Ω) (f : Ω → Γ) : FiniteLaw Γ where
  weight γ := ∑ ω, if f ω = γ then μ.weight ω else 0
  nonneg γ := Finset.sum_nonneg fun ω _ => by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl
  total := by
    rw [Finset.sum_comm]
    simpa using μ.total

@[simp] theorem map_weight (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = ∑ ω, if f ω = γ then μ.weight ω else 0 := rfl

end TalagrandDiscreteConvexity.FiniteLaw

end

end OAI


