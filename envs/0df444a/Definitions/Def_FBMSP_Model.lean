-- Prove2me | Definitions.Def_FBMSP_Model
-- name    : FBMSP_Model
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T04:51:56.501077+00:00
-- url     : https://prove2.me/theorems/deee3584-857f-46ab-850f-b94b5deb9e3c
-- title:
--   Independent-error pricing model and revenue objectives
-- statement:
--   This bundle defines inclusive survival $S(t)=\Pr(E\ge t)$, integrable mean-zero error, nonnegative integrable prediction laws, and density-bearing MHR through log-concave survival. It defines customer revenue, the least optimal price, price menus, unrestricted $k$-menu revenue, personalized revenue, model-market revenue, mean, variance, and segmentation loss. General prediction distributions remain available. A separate predicate records nonnegative realized valuations and is explicitly used by Theorem 3 and Corollary 2.
--
--   The finite layer specifies sorted distinct prediction values, positive normalized weights, arbitrary assignments and nonnegative prices, index-block revenues, an attaining block-price oracle, cuts, and the assignment that realizes them. The final definitions specify submodularity, finite-candidate greedy chains, and their optimization benchmark. These objects are built from the economic primitives; none assumes interval optimality or the desired approximation/concavity conclusions.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Sections 2–4, pp.7–24; definitions supporting Theorems 2–5.

import Mathlib

/-! Independent location-family pricing. Prediction values and errors are
sampled from separate probability laws. All suprema optimize over prices,
not over a set defined in terms of the desired theorem. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace FBMSP

/-- Inclusive survival, including atoms at a posted price. -/
def survival (η : Measure ℝ) (t : ℝ) : ℝ := (η (Ici t)).toReal

def ValidNoise (η : Measure ℝ) : Prop :=
  IsProbabilityMeasure η ∧ Integrable (fun e : ℝ => e) η ∧
    (∫ e, e ∂η) = 0

def ValidPredictions (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ Integrable (fun x : ℝ => x) ν ∧
    ∀ᵐ x ∂ν, 0 ≤ x

/-- A density-bearing MHR law, using the log-concave-survival formulation
used in the proof of Lemma 2(b). Zeros outside the support are allowed. -/
def HasMHR (η : Measure ℝ) : Prop :=
  η ≪ volume ∧
    ConcaveOn ℝ {t : ℝ | 0 < survival η t}
      (fun t => Real.log (survival η t))

def NonnegativeValuations (ν η : Measure ℝ) : Prop :=
  ∀ᵐ x ∂ν, ∀ᵐ e ∂η, 0 ≤ x + e

def postedRevenue (η : Measure ℝ) (x p : ℝ) : ℝ :=
  p * survival η (p - x)

def singleRevenue (η : Measure ℝ) (x : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ p : ℝ, 0 ≤ p ∧ r = postedRevenue η x p}

def IsOptimalPrice (η : Measure ℝ) (x p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ q : ℝ, 0 ≤ q → postedRevenue η x q ≤ postedRevenue η x p

def IsLeastOptimalPrice (η : Measure ℝ) (x p : ℝ) : Prop :=
  IsOptimalPrice η x p ∧ ∀ q, IsOptimalPrice η x q → p ≤ q

def singlePrice (η : Measure ℝ) (x : ℝ) : ℝ :=
  sInf {p : ℝ | IsOptimalPrice η x p}

def margin (η : Measure ℝ) (x : ℝ) : ℝ := singlePrice η x - x

/-- Price zero is always available as the zero-revenue outside option. -/
def menuAt (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) : ℝ :=
  if h : P.Nonempty then max 0 (P.sup' h (fun p => postedRevenue η x p)) else 0

def FeasibleMenu (P : Finset ℝ) (k : ℕ) : Prop :=
  P.card ≤ k ∧ ∀ p ∈ P, 0 ≤ p

def menuRevenue (ν η : Measure ℝ) (P : Finset ℝ) : ℝ :=
  ∫ x, menuAt η x P ∂ν

/-- At most k prices; ties and unused/duplicate price slots do not change revenue. -/
def optimalRevenue (ν η : Measure ℝ) (k : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ P : Finset ℝ, FeasibleMenu P k ∧ r = menuRevenue ν η P}

def personalizedRevenue (ν η : Measure ℝ) : ℝ :=
  ∫ x, singleRevenue η x ∂ν

def predictionMean (ν : Measure ℝ) : ℝ := ∫ x, x ∂ν

def predictionVariance (ν : Measure ℝ) : ℝ :=
  ∫ x, (x - predictionMean ν) ^ 2 ∂ν

def modelRevenue (ν : Measure ℝ) (k : ℕ) : ℝ :=
  optimalRevenue ν (Measure.dirac 0) k

def segmentationLoss (ν η : Measure ℝ) (k : ℕ) : ℝ :=
  personalizedRevenue ν η - optimalRevenue ν η k

def finitePolicyRevenue {n k : ℕ} (η : Measure ℝ)
    (μ w : Fin n → ℝ) (a : Fin n → Fin k) (p : Fin k → ℝ) : ℝ :=
  ∑ i, w i * postedRevenue η (μ i) (p (a i))

def finiteMenuRevenue {n : ℕ} (η : Measure ℝ)
    (μ w : Fin n → ℝ) (P : Finset ℝ) : ℝ :=
  ∑ i, w i * menuAt η (μ i) P

def ValidFiniteMarket {n : ℕ} (μ w : Fin n → ℝ) : Prop :=
  0 < n ∧ StrictMono μ ∧ (∀ i, 0 ≤ μ i) ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1

/-- The score of an index interval [a,b), so the largest type is included
when b=n. Empty intervals have score zero. -/
def blockRevenue {n : ℕ} (η : Measure ℝ) (μ w : Fin n → ℝ)
    (a b : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b),
    w i * postedRevenue η (μ i) p

/-- The oracle returns an attaining price. Its charged cost includes
evaluation of the attained block revenue. -/
def BlockOracle {n : ℕ} (η : Measure ℝ) (μ w : Fin n → ℝ)
    (o : ℕ → ℕ → ℝ) : Prop :=
  ∀ a b, a ≤ b → b ≤ n →
    0 ≤ o a b ∧ ∀ p : ℝ, 0 ≤ p →
      blockRevenue η μ w a b p ≤ blockRevenue η μ w a b (o a b)

def oracleScore {n : ℕ} (η : Measure ℝ) (μ w : Fin n → ℝ)
    (o : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ :=
  blockRevenue η μ w a b (o a b)

def ValidCuts (n k : ℕ) (c : Fin (k + 1) → ℕ) : Prop :=
  Monotone c ∧ c 0 = 0 ∧ c (Fin.last k) = n

def RealizesCuts {n k : ℕ} (a : Fin n → Fin k) (c : Fin (k + 1) → ℕ) : Prop :=
  ∀ i, c (a i).castSucc ≤ i.val ∧ i.val < c (a i).succ

def cutsRevenue {n k : ℕ} (η : Measure ℝ) (μ w : Fin n → ℝ)
    (o : ℕ → ℕ → ℝ) (c : Fin (k + 1) → ℕ) : ℝ :=
  ∑ j : Fin k, oracleScore η μ w o (c j.castSucc) (c j.succ)

def IsSubmodular (F : Finset ℝ → ℝ) : Prop :=
  ∀ A B, F (A ∩ B) + F (A ∪ B) ≤ F A + F B

def IsGreedyChain (F : Finset ℝ → ℝ) (P : Finset ℝ)
    (k : ℕ) (A : ℕ → Finset ℝ) : Prop :=
  A 0 = ∅ ∧ ∀ t, t < k → A t ⊆ P ∧
    ∃ p ∈ P \ A t, A (t + 1) = insert p (A t) ∧
      ∀ q ∈ P \ A t, F (insert q (A t)) - F (A t) ≤
        F (insert p (A t)) - F (A t)

def candidateOptimum (F : Finset ℝ → ℝ) (P : Finset ℝ) (k : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ A : Finset ℝ, A ⊆ P ∧ A.card ≤ k ∧ r = F A}

end FBMSP


