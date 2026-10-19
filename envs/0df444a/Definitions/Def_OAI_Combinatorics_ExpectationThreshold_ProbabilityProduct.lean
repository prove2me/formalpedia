-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
-- name    : OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:26:40.080636+00:00
-- url     : https://prove2.me/theorems/5c42be52-6a94-42cd-bbcf-908812c6d20c
-- title:
--   Pushforward of a finite law
-- statement:
--   Let $\mu$ be a finite law on $\Omega$ and $f:\Omega\to\Gamma$ a map into a finite set. The pushforward law has weights
--   $$
--   (f_*\mu)(\gamma)=\sum_{\omega:\ f(\omega)=\gamma}\mu(\omega).
--   $$
--
--   It is again a finite law, with the same total mass $1$. Marginals and laws of derived quantities are pushforwards.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/ProbabilityProduct.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ProbabilityProduct.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Marginals and pushforwards of finite product laws

Product moments, one-coordinate marginals, and pushforward identities follow
from the weights of the finite laws.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandThreshold.FiniteLaw

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

end TalagrandThreshold.FiniteLaw

end

end OAI


