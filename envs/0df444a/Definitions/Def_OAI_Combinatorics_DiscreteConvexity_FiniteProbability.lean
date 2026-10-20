-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
-- name    : OAI_Combinatorics_DiscreteConvexity_FiniteProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:35:14.579547+00:00
-- url     : https://prove2.me/theorems/a5fca7fb-eafb-4ed4-939f-2d4f22ec20d1
-- title:
--   Finite probability laws, expectations and product laws
-- statement:
--   A finite law on a finite set $\Omega$ is a weight function $\mu:\Omega\to[0,\infty)$ with $\sum_\omega\mu(\omega)=1$.
--
--   1. **Expectation and probability.** $\mathbb{E}_\mu f=\sum_\omega\mu(\omega)f(\omega)$ and $\Pr_\mu(P)=\sum_{\omega\in P}\mu(\omega)$. Constants have expectation equal to themselves, $\Pr(\text{true})=1$, $\Pr(\text{false})=0$, and
--   $$
--   \Pr_\mu(\neg P)=1-\Pr_\mu(P).
--   $$
--   2. **Products.** The product law $\mu\otimes\nu$ on $\Omega\times\Gamma$, with weights $\mu(\omega)\nu(\gamma)$, and the product law $\bigotimes_i\mu_i$ on $\prod_iA_i$, with weights $\prod_i\mu_i(\omega_i)$.
--   3. **Independent samples and uniform laws.** The law of $n$ independent samples from $\mu$, and the uniform law $1/|\Omega|$ on a nonempty $\Omega$.
--
--   All probabilistic arguments in the development are finite sums of this kind.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/FiniteProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/FiniteProbability.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite probability laws

All probabilities and expectations are finite real sums. Finite laws admit
elementary probability inequalities, product laws, independent samples, and
uniform distributions.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandDiscreteConvexity

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

theorem prob_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob (fun ω => ¬ P ω) = 1 - μ.prob P := by
  classical
  have h : μ.prob P + μ.prob (fun ω => ¬ P ω) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  linarith

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

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hN]

end FiniteLaw

end TalagrandDiscreteConvexity

end

end OAI


