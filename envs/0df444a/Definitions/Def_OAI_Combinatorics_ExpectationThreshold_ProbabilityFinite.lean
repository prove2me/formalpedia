-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
-- name    : OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:23:38.943304+00:00
-- url     : https://prove2.me/theorems/4d0af0cf-21bd-49e9-9385-f28fbdd5ae39
-- title:
--   Finite probability laws, products and independent samples
-- statement:
--   A finite law on a finite set $\Omega$ is a weight function $\mu\ge0$ with $\sum_\omega\mu(\omega)=1$.
--
--   1. **Expectation and probability.** $\mathbb{E}_\mu f=\sum_\omega\mu(\omega)f(\omega)$ and $\Pr_\mu(P)=\sum_{\omega\in P}\mu(\omega)$; constants have expectation equal to themselves, $\Pr(\text{true})=1$ and $\Pr(\text{false})=0$.
--   2. **Products.** The product law of $\mu$ on $\Omega$ and $\nu$ on $\Gamma$ has weights $\mu(\omega)\nu(\gamma)$. The product of a family $(\mu_i)$ on $\prod_iA_i$ has weights
--   $$
--   \prod_i\mu_i(\omega_i).
--   $$
--   3. **Independent samples.** $n$ independent samples from $\mu$ form the product law on $\Omega^n$.
--
--   All probabilistic statements of the threshold comparison are finite sums of this kind.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/ProbabilityFinite.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ProbabilityFinite.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite probability laws

Probabilities and expectations are finite real sums. Independent samples,
product laws, and uniform laws satisfy the usual elementary inequalities.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandThreshold

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw

def expectation {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * f ω

def prob {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.weight ω else 0

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

@[simp] theorem expectation_const (μ : FiniteLaw Ω) (c : ℝ) :
    μ.expectation (fun _ => c) = c := by
  rw [expectation, ← Finset.sum_mul, μ.total, one_mul]

@[simp] theorem prob_true (μ : FiniteLaw Ω) : μ.prob (fun _ => True) = 1 := by
  simp [prob, μ.total]

@[simp] theorem prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

def prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) : FiniteLaw (Ω × Γ) where
  weight ω := μ.weight ω.1 * ν.weight ω.2
  nonneg ω := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

@[simp] theorem prod_weight (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (ω : Ω) (γ : Γ) :
    (μ.prod ν).weight (ω, γ) = μ.weight ω * ν.weight γ := rfl

def pi {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) := by
  classical
  exact {
    weight := fun ω => ∏ i, (μ i).weight (ω i)
    nonneg := fun ω => Finset.prod_nonneg fun i _ => (μ i).nonneg (ω i)
    total := by
      rw [← Fintype.prod_sum (fun i a => (μ i).weight a)]
      simp_rw [(μ _).total]
      simp }

@[simp] theorem pi_weight {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) (ω : ∀ i, A i) :
    (pi μ).weight ω = ∏ i, (μ i).weight (ω i) := rfl

def iid (μ : FiniteLaw Ω) (n : ℕ) : FiniteLaw (Fin n → Ω) := pi (fun _ : Fin n => μ)

@[simp] theorem iid_weight (μ : FiniteLaw Ω) (n : ℕ) (ω : Fin n → Ω) :
    (iid μ n).weight ω = ∏ i, μ.weight (ω i) := rfl

end FiniteLaw

end TalagrandThreshold

end

end OAI


