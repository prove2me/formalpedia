-- Prove2me | Definitions.Def_ExponomialAssortment_FPTAS_Model
-- name    : ExponomialAssortment_FPTAS_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T21:12:30.31248+00:00
-- url     : https://prove2.me/theorems/5c5039e2-db6e-46cf-ad67-cd12f2b1f6c6
-- title:
--   Exponomial choice, feasible assortments and revenue
-- statement:
--   Normalized real utilities, nonnegative prices, a mandatory stochastic outside option, choice probabilities from independent exponential errors, finite prefix statistics, true revenue, optimality and normalization.
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, §§2.1–2.3, printed 7–8, PDF 8–9

import Definitions.Def_HetExponomial_ChoiceProb_Model

noncomputable section

namespace ExponomialAssortment.FPTAS
open scoped BigOperators

structure Instance (n : ℕ) where
  outside : Fin n
  price : Fin n → ℝ
  utility : Fin n → ℝ

def Valid {n : ℕ} (I : Instance n) : Prop :=
  (∀ i, 0 ≤ I.price i) ∧ I.price I.outside = 0 ∧
  Antitone I.utility ∧ (∃ i, I.utility i = 0) ∧ (∀ i, 0 ≤ I.utility i)

def Feasible {n : ℕ} (I : Instance n) (C : ℕ) (S : Finset (Fin n)) : Prop :=
  I.outside ∈ S ∧ S.card ≤ C

def probability {n : ℕ} (u : Fin n → ℝ) (rate : ℝ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if h : i ∈ S then
    HetExponomial.ChoiceProb.choiceProb
      (fun j : Fin S.card => u ((S.orderIsoOfFin rfl) j)) (fun _ => rate)
      ((S.orderIsoOfFin rfl).symm ⟨i, h⟩)
  else 0

def revenue {n : ℕ} (I : Instance n) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, I.price i * probability I.utility 1 S i

def prefixSet {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : Finset (Fin n) :=
  S.filter (fun j => j.val < k)

def average {n : ℕ} (I : Instance n) (S : Finset (Fin n)) (k : ℕ) : ℝ :=
  if (prefixSet S k).card = 0 then 0 else
    (∑ j ∈ prefixSet S k, I.price j) / (prefixSet S k).card

def gapSum {n : ℕ} (u : Fin n → ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ j ∈ prefixSet S (i.val + 1), u j - u i

def coefficient {n : ℕ} (u : Fin n → ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if (prefixSet S (i.val + 1)).card = 0 then 0 else
    Real.exp (-gapSum u S i) / (prefixSet S (i.val + 1)).card

def contributionScore {n : ℕ} (I : Instance n) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, coefficient I.utility S i * (I.price i - average I S i.val)

def indexedScore {n : ℕ} (I : Instance n) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, (coefficient I.utility S i -
    ∑ j ∈ S.filter (fun j => i < j),
      coefficient I.utility S j / (prefixSet S j.val).card) * I.price i

def Optimal {n : ℕ} (I : Instance n) (C : ℕ) (S : Finset (Fin n)) : Prop :=
  Feasible I C S ∧ ∀ T, Feasible I C T → revenue I T ≤ revenue I S

/-- Normalization retains the full real-utility and positive-rate semantics. -/
def Normalization : Prop :=
  ∀ (n : ℕ) (u : Fin n → ℝ) (rate : ℝ), 0 < rate →
    ∀ (outside : Fin n) (p : Fin n → ℝ), (∀ i, 0 ≤ p i) → p outside = 0 →
    ∃ (I : Instance n) (e : Fin n ≃ Fin n) (b : ℝ),
      Valid I ∧ I.outside = e.symm outside ∧
      (∀ i, I.price i = p (e i) ∧ I.utility i = rate * u (e i) - b) ∧
      ∀ S i, probability I.utility 1 S i =
        probability u rate (S.map e.toEmbedding) (e i)

end ExponomialAssortment.FPTAS


