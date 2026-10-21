-- Prove2me | Definitions.Def_OverflowBinPacking_IID_Model
-- name    : OverflowBinPacking_IID_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:59.92447+00:00
-- url     : https://prove2.me/theorems/096309ea-9a08-47c0-b694-7d3fdf80f190
-- title:
--   §1.2 and §3.1 — adaptive overflow bin packing model, policy, cost, and risk
-- statement:
--   There are $n$ items with independent nonnegative sizes $X_1,\ldots,X_n$ and at most $n$ unit-capacity bins. A deterministic policy chooses a bin for each item using only earlier realized sizes. It never assigns an item to a bin whose current load exceeds one; the assignment is measurable so its expected cost is defined.
--
--   A bin opens when it first receives an item and breaks when its final load is strictly greater than one. With opening cost one and overflow penalty $C\ge1$, the policy's cost is
--   $$\operatorname{cost}(P)=\mathbb E[N_P]+C\,\mathbb E[O_P].$$
--   The conditional risk of placing an item in a bin of current load $S$ is $\Pr(X_i+S>1)$; a bin's accumulated risk is the sum of these placement risks. These definitions let the paper's policy and risk comparisons share one model.
--
--   **Formalization Note** Items and bins are indexed from zero. Measurability is explicit. Feasibility is imposed on all outcome vectors, including those outside the nonnegative support; every policy on the paper's outcomes admits such an extension.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, pp. 2, 7–9, §1.2 and §3.1

import Mathlib

namespace OverflowBinPacking.IID

open MeasureTheory

/-- A deterministic assignment of each arriving item to one of at most `n` bins. -/
abbrev Rule (n : ℕ) := Fin n → (Fin n → ℝ) → Fin n

/-- The load of bin `j` immediately before round `t`. -/
noncomputable def usage {n : ℕ} (a : Rule n) (x : Fin n → ℝ)
    (j : Fin n) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < t ∧ a k x = j), x k

def Nonanticipative {n : ℕ} (a : Rule n) : Prop :=
  ∀ (i : Fin n) (x y : Fin n → ℝ),
    (∀ k : Fin n, k < i → x k = y k) → a i x = a i y

def MeasurableRule {n : ℕ} (a : Rule n) : Prop :=
  ∀ i j, MeasurableSet {x : Fin n → ℝ | a i x = j}

/-- An overflowed bin (load strictly exceeding one) is never used again. -/
def Feasible {n : ℕ} (a : Rule n) : Prop :=
  ∀ (x : Fin n → ℝ) (i : Fin n), usage a x (a i x) i ≤ 1

def IsPolicy {n : ℕ} (a : Rule n) : Prop :=
  Nonanticipative a ∧ MeasurableRule a ∧ Feasible a

def numOpened {n : ℕ} (a : Rule n) (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.image (fun i : Fin n => a i x)).card

noncomputable def numBroken {n : ℕ} (a : Rule n) (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => 1 < usage a x j n)).card

/-- Expected bin-opening cost plus the overflow penalty. The count is computed from
final loads, independently of the risk expression below. -/
noncomputable def cost {n : ℕ} (μ : Fin n → Measure ℝ) (C : ℝ)
    (a : Rule n) : ℝ :=
  ∫ x, ((numOpened a x : ℝ) + C * (numBroken a x : ℝ)) ∂(Measure.pi μ)

/-- The probability that an item of law `ν` overflows a bin of present load `S`. -/
noncomputable def overflowProb (ν : Measure ℝ) (S : ℝ) : ℝ :=
  ν.real (Set.Ioi (1 - S))

/-- Accumulated conditional overflow risk in bin `j` before round `t`. -/
noncomputable def riskUpTo {n : ℕ} (μ : Fin n → Measure ℝ)
    (a : Rule n) (x : Fin n → ℝ) (j : Fin n) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < t ∧ a k x = j),
    overflowProb (μ k) (usage a x j k)

noncomputable def risk {n : ℕ} (μ : Fin n → Measure ℝ)
    (a : Rule n) (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  riskUpTo μ a x j n

def IsBudgeted {n : ℕ} (μ : Fin n → Measure ℝ)
    (a : Rule n) (b : ℝ) : Prop :=
  ∀ x j, risk μ a x j ≤ b

/-- Heavy items have individual bins; every other bin respects the risk budget. -/
def IsolatesHeavy {n : ℕ} (μ : Fin n → Measure ℝ)
    (C γ : ℝ) (a : Rule n) : Prop :=
  (∀ x (i : Fin n), γ / C < (μ i).real (Set.Ioi 1) →
    ∀ k : Fin n, k ≠ i → a k x ≠ a i x) ∧
  (∀ x (j : Fin n),
    (∀ i : Fin n, a i x = j → (μ i).real (Set.Ioi 1) ≤ γ / C) →
    risk μ a x j ≤ γ / C)

end OverflowBinPacking.IID


