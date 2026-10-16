-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
-- name    : OAI_Combinatorics_GraphThreshold_FiniteProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:13:22.09152+00:00
-- url     : https://prove2.me/theorems/1b9f2325-6651-432e-aaf7-94f9099343f7
-- title:
--   Product, i.i.d., uniform and Bernoulli finite probability laws
-- statement:
--   A finite law $\mu$ on a finite set $\Omega$ is a weight function $\mu:\Omega\to\mathbb{R}$ with nonnegative values summing to $1$; its expectation is $\mathbb{E}_\mu[f]=\sum_\omega\mu(\omega)f(\omega)$ and the probability of a property $P$ is $\mu(P)=\sum_{\omega:\,P(\omega)}\mu(\omega)$. This file constructs the standard finite laws and records their basic identities.
--
--   1. **Normalisation.** $\mathbb{E}_\mu[c]=c$ for every constant $c\in\mathbb{R}$; the always-true property has probability $1$ and the always-false property has probability $0$.
--
--   2. **Products.** For finite laws $\mu$ on $\Omega$ and $\nu$ on $\Gamma$, the product law on $\Omega\times\Gamma$ has weights $(\mu\otimes\nu)(\omega,\gamma)=\mu(\omega)\,\nu(\gamma)$. More generally, for a finite index set $I$ and finite laws $\mu_i$ on finite sets $A_i$, the product law on $\prod_{i\in I}A_i$ has weights $\prod_{i\in I}\mu_i(\omega_i)$. The i.i.d. law $\mu^{\otimes n}$ on $\Omega^n$ (sequences $(\omega_0,\dots,\omega_{n-1})$) has weights $\prod_{i=0}^{n-1}\mu(\omega_i)$.
--
--   3. **Uniform law.** For a nonempty finite set $\Omega$, the uniform law has weight $1/|\Omega|$ at every point; it is positive (every weight is strictly positive), and
--
--      $$\mathrm{Unif}_\Omega(P)=\frac{|\{\omega\in\Omega:\ P(\omega)\}|}{|\Omega|} .$$
--
--   4. **Subsets as Boolean vectors.** For a finite set $X$, the map $W\mapsto(x\mapsto[x\in W])$ is a bijection between subsets of $X$ and functions $X\to\{\mathrm{true},\mathrm{false}\}$, where $[x\in W]$ is the truth value of $x\in W$. Consequently, for every $f:X\times\{\mathrm{true},\mathrm{false}\}\to\mathbb{R}$,
--
--      $$\sum_{W\subseteq X}\ \prod_{x\in X}f\bigl(x,[x\in W]\bigr)=\prod_{x\in X}\bigl(f(x,\mathrm{true})+f(x,\mathrm{false})\bigr).$$
--
--   5. **Bernoulli law.** For $p\in\mathbb{R}$ let $\mu_p(W)=\prod_{x\in X}w_x(W)$, where $w_x(W)=p$ if $x\in W$ and $w_x(W)=1-p$ if $x\notin W$, and let $\mathbb{E}_p[f]=\sum_{W\subseteq X}\mu_p(W)f(W)$. For every real $p$ and every $f$ as in item 4,
--
--      $$\mathbb{E}_p\Bigl[\prod_{x\in X}f\bigl(x,[x\in W]\bigr)\Bigr]=\prod_{x\in X}\bigl(p\,f(x,\mathrm{true})+(1-p)\,f(x,\mathrm{false})\bigr),$$
--
--      and in particular $\sum_{W\subseteq X}\mu_p(W)=1$. If $0\le p\le 1$, then $\mu_p(W)\ge 0$ for all $W$, so $\mu_p$ is a finite law on the subsets of $X$, the Bernoulli law of the $p$-random subset; its expectation and probability are $\mathbb{E}_p$ and the Bernoulli probability $\mathbb{P}_p[P]=\sum_{W:\,P(W)}\mu_p(W)$.
--
--   These laws model the random objects of the threshold argument: the Bernoulli law is the $p$-random subset of the edge set of $K_n$ (the random graph $G(n,p)$), products and i.i.d. laws model independent repeated trials, and uniform laws model a uniformly random copy of a set. The product formula expresses the independence of the coordinates of the $p$-random subset.
--
--   **Formalization Note** The constructions are `FiniteLaw.prod`, `FiniteLaw.pi` (dependent products over a finite index type with decidable equality), `FiniteLaw.iid μ n` on `Fin n → Ω`, `FiniteLaw.uniform Ω` (requiring `Nonempty Ω`), `finsetBoolEquiv`, and `bernoulliLaw p hp0 hp1`, which takes the proofs of $0\le p$ and $p\le 1$ as arguments. The product identities are `sum_finset_product` and `bernoulliExpectation_product`; the other members are simp lemmas computing weights, expectations and probabilities of these laws.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/FiniteProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/FiniteProbability.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SecondKahnKalai mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

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

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hN]

theorem uniform_isPositive (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    (uniform Ω).IsPositive := fun _ => inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

theorem uniform_prob (Ω : Type*) [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    (uniform Ω).prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  simp [prob, uniform, ← Finset.sum_filter, div_eq_mul_inv]

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

def finsetBoolEquiv : Finset X ≃ (X → Bool) where
  toFun W x := decide (x ∈ W)
  invFun b := Finset.univ.filter fun x => b x = true
  left_inv W := by ext x; simp
  right_inv b := by
    funext x
    cases hb : b x <;> simp [hb]

theorem sum_finset_product (f : X → Bool → ℝ) :
    (∑ W : Finset X, ∏ x, f x (decide (x ∈ W))) =
      ∏ x, (f x true + f x false) := by
  calc
    (∑ W : Finset X, ∏ x, f x (decide (x ∈ W))) =
        ∑ b : X → Bool, ∏ x, f x (b x) :=
      (finsetBoolEquiv (X := X)).sum_comp (fun b => ∏ x, f x (b x))
    _ = _ := by rw [← Fintype.prod_sum f]; simp only [Fintype.sum_bool]

theorem bernoulliExpectation_product (p : ℝ) (f : X → Bool → ℝ) :
    bernoulliExpectation p (fun W => ∏ x, f x (decide (x ∈ W))) =
      ∏ x, (p * f x true + (1 - p) * f x false) := by
  unfold bernoulliExpectation bernoulliWeight
  simp_rw [← Finset.prod_mul_distrib]
  simpa using sum_finset_product (fun x b => (if b then p else 1 - p) * f x b)

theorem bernoulliWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset X) :
    0 ≤ bernoulliWeight p W := by
  apply Finset.prod_nonneg
  intro x _
  split_ifs <;> linarith

theorem bernoulliWeight_sum (p : ℝ) : ∑ W : Finset X, bernoulliWeight p W = 1 := by
  have hp : p + (1 - p) = 1 := by ring
  simpa [bernoulliExpectation, hp] using
    bernoulliExpectation_product p (fun (_ : X) (_ : Bool) => 1)

def bernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw (Finset X) where
  weight := bernoulliWeight p
  nonneg := bernoulliWeight_nonneg hp0 hp1
  total := bernoulliWeight_sum p

@[simp] theorem bernoulliLaw_weight (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset X) :
    (bernoulliLaw p hp0 hp1).weight W = bernoulliWeight p W := rfl

@[simp] theorem bernoulliLaw_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Finset X → ℝ) :
    (bernoulliLaw p hp0 hp1).expectation f = bernoulliExpectation p f := rfl

@[simp] theorem bernoulliLaw_prob (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset X → Prop) : (bernoulliLaw p hp0 hp1).prob P = bernoulliProbability p P := rfl

end LeanBlast.SecondKahnKalai

end

end OAI


