-- Prove2me | Definitions.Def_GaoImpatientMNL_Pricing_Model
-- name    : GaoImpatientMNL_Pricing_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:10.331965+00:00
-- url     : https://prove2.me/theorems/70c653c9-0e8d-4b88-a1e7-5de62a27b07f
-- title:
--   Sequential assortments and unrestricted pricing objectives
-- statement:
--   There are $n$ products and $m$ stages. The standing parameter predicate requires $n,m\ge1$, $\beta>0$, and patience tails $1=\lambda_1\ge\cdots\ge\lambda_m>0$. Intrinsic utilities $\alpha_i$ and prices $p_i$ are arbitrary reals. Feasible assortments are pairwise disjoint sets $S_1,\ldots,S_m$; products may be omitted and stages may be empty. Write $v_i(p)=e^{\alpha_i-\beta p_i}$ and $V_k(p)=\sum_{i\in S_k}v_i(p)$. The objective is
--   $$\Pi(p,S)=\sum_{k=1}^m\frac{\lambda_k\sum_{i\in S_k}p_i v_i(p)}{(1+\sum_{h<k}V_h(p))(1+\sum_{h\le k}V_h(p))}.$$
--   The independent choice-probability formula uses the same denominator. The all-products-first sequence is $(N,\varnothing,\ldots,\varnothing)$ and its single-stage revenue uses the published definition of MNL pricing revenue with constant sensitivity. The joint revenue set ranges over every feasible sequence and every real price vector. Its supremum and the first-stage supremum are real-valued; their nonemptiness, upper bounds, attainment, and positive joint value are collected in a predicate used only as a theorem conclusion. Fixed-assortment optimality means comparison with every real price vector. Finite indices are zero-based. Definitions are total even outside the standing parameter assumptions; no claim about their economic interpretation is made there.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, held source.pdf, §§2,4 and Appendix F; PDF pp.6,11–16,45–51 (printed pp.6,11–16,ec8–ec14).

import Mathlib
import Definitions.Def_MultiStoreAssort_Pricing_Model

open scoped BigOperators
noncomputable section

/- BEGIN IMPORTED LEAN FOR BLIND AUDIT
noncomputable section
namespace MultiStoreAssort.Pricing
variable {n : ℕ}
noncomputable def rev14 (a b : Fin n → ℝ) (S : Finset (Fin n)) (p : Fin n → ℝ) : ℝ :=
  (∑ k ∈ S, p k * Real.exp (a k - b k * p k)) / (1 + ∑ k ∈ S, Real.exp (a k - b k * p k))
end MultiStoreAssort.Pricing
end
END IMPORTED LEAN FOR BLIND AUDIT -/

namespace GaoImpatientMNL.Pricing

/-- §2 and §4: arbitrary real intrinsic utilities; positive common sensitivity;
positive decreasing patience tails, with first tail one. Fin indices are zero-based. -/
def Parameters {n m : ℕ} (β : ℝ) (lam : Fin m → ℝ) : Prop :=
  0 < n ∧ 0 < m ∧ 0 < β ∧
    (∀ k, k.val = 0 → lam k = 1) ∧ (∀ k, 0 < lam k) ∧ Antitone lam

/-- §2, p.6: disjoint assortments; neither coverage nor nonempty stages is required. -/
def Feasible {n m : ℕ} (S : Fin m → Finset (Fin n)) : Prop :=
  ∀ k h, k ≠ h → Disjoint (S k) (S h)

/-- §4.2 total attraction in an assortment. -/
def attraction {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ)
    (s : Finset (Fin n)) : ℝ := ∑ i ∈ s, Real.exp (α i - β * p i)

/-- Cumulative attraction before a zero-based stage. -/
def prefixWeight {n m : ℕ} (v : Fin n → ℝ) (S : Fin m → Finset (Fin n)) (k : Fin m) : ℝ :=
  ∑ h ∈ Finset.univ.filter (fun h => h < k), ∑ i ∈ S h, v i

/-- Theorem 2.1's formula, independently of the operational purchase event. -/
def choiceFormula {n m : ℕ} (v : Fin n → ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (k : Fin m) (i : Fin n) : ℝ :=
  lam k * v i / ((1 + prefixWeight v S k) * (1 + prefixWeight v S k + ∑ j ∈ S k, v j))

/-- §4.2, p.16: objective on all real product prices.
Outside Parameters, lam can be signed or identically zero. In particular,
lam identically zero makes this function identically zero for every beta.
Thus no unconditional unboundedness claim for beta ≤ 0 is part of this definition. -/
def revenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) : ℝ :=
  ∑ k, (lam k * ∑ i ∈ S k, p i * Real.exp (α i - β * p i)) /
    ((1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k) *
      (1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k + attraction α β p (S k)))

/-- Every product is offered in stage one. -/
def firstSequence (n m : ℕ) : Fin m → Finset (Fin n) :=
  fun k => if k.val = 0 then Finset.univ else ∅

/-- Reuse of the published single-stage revenue, with constant price sensitivity. -/
def firstRevenue {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ) : ℝ :=
  MultiStoreAssort.Pricing.rev14 α (fun _ => β) Finset.univ p

/-- The full joint feasible revenue set, including omitted products and empty stages. -/
def jointRevenues {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ) : Set ℝ :=
  {r | ∃ S : Fin m → Finset (Fin n), Feasible S ∧ ∃ p : Fin n → ℝ, r = revenue α β lam S p}

/-- Suprema are related to finite attained maxima in the theorem conclusions. -/
def jointValue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ) : ℝ :=
  sSup (jointRevenues α β lam)

def firstValue {n : ℕ} (α : Fin n → ℝ) (β : ℝ) : ℝ :=
  sSup (Set.range (firstRevenue α β))

/-- Fixed-assortment global optimality on the entire real price space. -/
def IsPricingMax {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) : Prop :=
  ∀ p', revenue α β lam S p' ≤ revenue α β lam S p

/-- Well-posedness is a conclusion, never an assumption: nonempty bounded revenue
sets and attainment of both maxima, plus positivity of the joint optimum. -/
def MaximaExist {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ) : Prop :=
  (jointRevenues α β lam).Nonempty ∧ BddAbove (jointRevenues α β lam) ∧
  (Set.range (firstRevenue α β)).Nonempty ∧ BddAbove (Set.range (firstRevenue α β)) ∧
  (∃ S p, Feasible S ∧ revenue α β lam S p = jointValue α β lam) ∧
  (∃ p, firstRevenue α β p = firstValue α β) ∧ 0 < jointValue α β lam

end GaoImpatientMNL.Pricing


