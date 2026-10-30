-- Prove2me | Definitions.Def_JointParametricPricing_PSC_Exploration
-- name    : JointParametricPricing_PSC_Exploration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:48:23.346827+00:00
-- url     : https://prove2.me/theorems/5527c6b3-ed0c-46cf-afba-3cd68c2e9e97
-- title:
--   Exploration prices, A5, likelihoods, and arbitrary maximizing selectors
-- statement:
--   A positive number $\widetilde q$ of fixed ordinary price vectors defines a product categorical experiment. A5 requires identifiability of this block law; constants $0<\lambda_{\min}<\lambda_{\max}<1$ bounding each sale probability below and their sum above; and a symmetric Fisher matrix bounded below by $c_f I$ for a positive uniform $c_f$. The Fisher entries are the expected negative second coordinate derivatives of the block log likelihood, whose existence is explicit. For $L$ observations, zero-based time $s$ uses price index $\lfloor s\widetilde q/L\rfloor$. The likelihood uses all $L$ observations at these prices. A selector takes any maximizer on $\Theta$ for each observation string; compactness and continuity supply a canonical selector, but no tie rule is imposed on the theorems. Tail probabilities and mean-square errors are finite sums under the unconditioned exploration experiment, with no inventory-survival conditioning.
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); §2, printed 8 / PDF 9; PSC box, printed 11 / PDF 12; Lemma 1, printed 12 / PDF 13

import Definitions.Def_JointParametricPricing_PSC_Model

open scoped BigOperators
noncomputable section

namespace JointParametricPricing.PSC

/-- Categorical mass: none is no purchase, some j is one sale of j. -/
def categoricalMass {n : ℕ} (x : Vec n) : Sale n → ℝ
  | none => 1 - ∑ j, x j
  | some j => x j

structure ExplorationPrices {n m q : ℕ} (M : Model n m q) where
  count : ℕ
  count_pos : 0 < count
  price : Fin count → M.prices

namespace ExplorationPrices
variable {n m q : ℕ} {M : Model n m q}
def blockLikelihood (E : ExplorationPrices M) (θ : Vec q) (y : Fin E.count → Sale n) : ℝ :=
  ∏ s, categoricalMass (M.demand (E.price s) θ) (y s)

def fisher (E : ExplorationPrices M) (θ : Vec q) (i j : Fin q) : ℝ :=
  ∑ y : Fin E.count → Sale n, E.blockLikelihood θ y *
    (-secondPartial (fun z => Real.log (E.blockLikelihood z y)) θ i j)

/-- All clauses of A5; no estimation or regret bound is part of this predicate. -/
def A5 (E : ExplorationPrices M) : Prop :=
  (∀ θ ∈ M.Θ, ∀ θ' ∈ M.Θ, θ ≠ θ' → E.blockLikelihood θ ≠ E.blockLikelihood θ') ∧
  ∃ lmin lmax cf : ℝ, 0 < lmin ∧ lmin < lmax ∧ lmax < 1 ∧ 0 < cf ∧
    (∀ θ ∈ M.Θ, ∀ s, (∀ j, lmin ≤ M.demand (E.price s) θ j) ∧
      ∑ j, M.demand (E.price s) θ j ≤ lmax) ∧
    (∀ θ ∈ M.Θ, ∀ y : Fin E.count → Sale n, ∀ i j,
      DifferentiableAt ℝ
        (fun t : ℝ => Real.log (E.blockLikelihood (θ + t • coordinate j) y)) 0 ∧
      DifferentiableAt ℝ
        (fun t : ℝ => coordDeriv (fun z => Real.log (E.blockLikelihood z y))
          (θ + t • coordinate i) j) 0) ∧
    (∀ θ ∈ M.Θ, (∀ i j, E.fisher θ i j = E.fisher θ j i) ∧
      ∀ z : Vec q, cf * ‖z‖ ^ 2 ≤ ∑ i, ∑ j, z i * E.fisher θ i j * z j)

/-- Zero-based form of floor((t-1) qtilde / L)+1. -/
def scheduled (E : ExplorationPrices M) (L : ℕ) (s : Fin L) : M.prices :=
  E.price ⟨s.val * E.count / L, Nat.div_lt_of_lt_mul (by
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right s.isLt E.count_pos)⟩

def likelihood (E : ExplorationPrices M) (L : ℕ) (y : Fin L → Sale n) (θ : Vec q) : ℝ :=
  ∏ s, categoricalMass (M.demand (E.scheduled L s) θ) (y s)

def IsMLE (E : ExplorationPrices M) (L : ℕ) (y : Fin L → Sale n) (θ : M.Θ) : Prop :=
  ∀ z ∈ M.Θ, E.likelihood L y z ≤ E.likelihood L y θ

/-- An arbitrary fixed maximizing choice for every observation string. -/
structure MLESelector (E : ExplorationPrices M) where
  choose : (L : ℕ) → (Fin L → Sale n) → M.Θ
  maximizes : ∀ L y, E.IsMLE L y (choose L y)

theorem likelihood_continuous (E : ExplorationPrices M) (L : ℕ) (y : Fin L → Sale n) :
    ContinuousOn (E.likelihood L y) M.Θ := by
  unfold likelihood
  apply continuousOn_finsetProd
  intro s hs θ hθ
  apply ContinuousAt.continuousWithinAt
  have hd := (M.parameter_C1 (E.scheduled L s) (E.scheduled L s).property θ hθ).continuousAt
  cases y s with
  | none => simp only [categoricalMass]; fun_prop
  | some j => simp only [categoricalMass]; fun_prop

/-- Compactness supplies a selector; arbitrary maximizing selectors remain permitted. -/
def canonicalMLE (E : ExplorationPrices M) : E.MLESelector where
  choose L y :=
    let ex := M.theta_compact.exists_isMaxOn ⟨M.thetaStar, M.thetaStar_mem⟩
      (E.likelihood_continuous L y)
    ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩
  maximizes L y :=
    (Classical.choose_spec (M.theta_compact.exists_isMaxOn ⟨M.thetaStar, M.thetaStar_mem⟩
      (E.likelihood_continuous L y))).2

def tail (E : ExplorationPrices M) (S : E.MLESelector) (L : ℕ) (θ : M.Θ) (δ : ℝ) : ℝ :=
  ∑ y : Fin L → Sale n, if δ < ‖(S.choose L y : Vec q) - θ‖ then E.likelihood L y θ else 0

def meanSquare (E : ExplorationPrices M) (S : E.MLESelector) (L : ℕ) (θ : M.Θ) : ℝ :=
  ∑ y : Fin L → Sale n, E.likelihood L y θ * ‖(S.choose L y : Vec q) - θ‖ ^ 2
end ExplorationPrices
end JointParametricPricing.PSC


