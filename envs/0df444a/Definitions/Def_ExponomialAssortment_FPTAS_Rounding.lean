-- Prove2me | Definitions.Def_ExponomialAssortment_FPTAS_Rounding
-- name    : ExponomialAssortment_FPTAS_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T21:13:04.812667+00:00
-- url     : https://prove2.me/theorems/c82da2fc-16cb-44cb-8dfd-6aa8614966e5
-- title:
--   Printed price grid and rounded objective graphs
-- statement:
--   Integer powers in the printed price grid, partial least-ceiling rounding, floor-rounded utilities, average trajectories through the prefix before the last product, signed scores and attained optima. Undefined rounding has no default.
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, §§4.1–4.2, printed 14–16, PDF 15–17

import Definitions.Def_ExponomialAssortment_FPTAS_Model

noncomputable section

namespace ExponomialAssortment.FPTAS
open scoped BigOperators

def pmax {n : ℕ} (I : Instance n) : ℝ := (Finset.univ.image I.price).sup' ⟨I.price I.outside, by simp⟩ id

def positivePrices {n : ℕ} (I : Instance n) : Finset ℝ :=
  (Finset.univ.image I.price).filter (fun p => 0 < p)

def pmin {n : ℕ} (I : Instance n) : ℝ :=
  if h : (positivePrices I).Nonempty then (positivePrices I).inf' h id else 0

def theta (n : ℕ) (η : ℝ) : ℝ := η / (2 * (n : ℝ)^3)
def delta (n : ℕ) (η : ℝ) : ℝ := η / (2 * n)

def priceGrid {n : ℕ} (I : Instance n) (η : ℝ) : Set ℝ :=
  {a | a = 0 ∨ ∃ k : ℤ, a = (1 + theta n η)^k ∧ pmin I / n ≤ a ∧ a ≤ pmax I}

/-- No fallback value if the printed grid has no ceiling. -/
def Round {n : ℕ} (I : Instance n) (η t a : ℝ) : Prop :=
  a ∈ priceGrid I η ∧ t ≤ a ∧ ∀ b ∈ priceGrid I η, t ≤ b → a ≤ b

def roundedUtility {n : ℕ} (I : Instance n) (η : ℝ) (i : Fin n) : ℝ :=
  delta n η * (⌊I.utility i / delta n η⌋ : ℤ)

def utilityGrid {n : ℕ} (I : Instance n) (η : ℝ) : Set ℝ :=
  {a | ∃ k : ℕ, a = k * delta n η ∧ 0 ≤ a ∧
    ∀ i : Fin n, (∀ j, I.utility j ≤ I.utility i) → a ≤ n * I.utility i}

/-- Only the averages used by (7) and (10), through the prefix before the last product. -/
def AverageTrajectory {n : ℕ} (I : Instance n) (η : ℝ)
    (S : Finset (Fin n)) (a : ℕ → ℝ) : Prop :=
  a 0 = 0 ∧ ∀ i : Fin n, i.val + 1 < n →
    if i ∈ S then Round I η
      (((prefixSet S i.val).card * a i.val + I.price i) / ((prefixSet S i.val).card + 1))
      (a (i.val + 1))
    else a (i.val + 1) = a i.val

def score {n : ℕ} (I : Instance n) (u : Fin n → ℝ)
    (S : Finset (Fin n)) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ S, coefficient u S i * (I.price i - a i.val)

def RoundedScore {n : ℕ} (I : Instance n) (η : ℝ) (joint : Bool)
    (S : Finset (Fin n)) (v : ℝ) : Prop :=
  ∃ a, AverageTrajectory I η S a ∧
    v = score I (if joint then roundedUtility I η else I.utility) S a

def RoundedOptimal {n : ℕ} (I : Instance n) (C : ℕ) (η : ℝ)
    (joint : Bool) (S : Finset (Fin n)) (v : ℝ) : Prop :=
  Feasible I C S ∧ RoundedScore I η joint S v ∧
    ∀ T w, Feasible I C T → RoundedScore I η joint T w → w ≤ v

def TotalRounded {n : ℕ} (I : Instance n) (C : ℕ) (η : ℝ) : Prop :=
  ∀ S, Feasible I C S → ∃ a, AverageTrajectory I η S a

end ExponomialAssortment.FPTAS


