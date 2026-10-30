-- Prove2me | Definitions.Def_XinMartingaleInventory_Minimax_bellman
-- name    : XinMartingaleInventory_Minimax_bellman
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:57:29.18633+00:00
-- url     : https://prove2.me/theorems/55f6c292-c39e-43e6-8588-9a22216882dd
-- title:
--   Independent and martingale Bellman recursions
-- statement:
--   The zero-horizon continuation is zero. With n≥1 periods left, the stage objective is the holding/backlog cost plus the previous value at post-demand stock. The martingale version passes the realized demand as the next mean; the independent version keeps μ fixed. The inner value is the supremum of expected stage objectives over M(m); the outer value is the infimum over rational post-order stocks in [0,U] at least the pre-order stock. The argmax and argmin sets include feasibility and equality to their actual optimization values. No explicit formula or attainment assumption is built into these definitions.
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, §§2.1–3 and §7.2, p.10 (PDF p.10)

import Definitions.Def_XinMartingaleInventory_Minimax_inventoryModel

noncomputable section

namespace XinMartingaleInventory.Minimax

/-- Recursion (2.5)-(2.6), with zero-horizon value zero. -/
def bellmanV (U b : ℚ) : ℕ → ℚ → ℚ → ℝ
  | 0, _, _ => 0
  | n+1, y, m => sInf ((fun z : ℚ =>
      sSup ((fun q : DemandLaw => expectation q (fun d =>
        cost b z d + bellmanV U b n (z-d) d)) '' meanLaws U m)) ''
      {z | z ∈ Set.Icc 0 U ∧ y ≤ z})

def bellmanF (U b : ℚ) (n : ℕ) (x d : ℚ) : ℝ :=
  cost b x d + bellmanV U b (n-1) (x-d) d

def bellmanG (U b : ℚ) (n : ℕ) (x m : ℚ) : ℝ :=
  sSup ((fun q => expectation q (bellmanF U b n x)) '' meanLaws U m)

def bellmanMax (U b : ℚ) (n : ℕ) (x m : ℚ) : Set DemandLaw :=
  {q | q ∈ meanLaws U m ∧ expectation q (bellmanF U b n x) = bellmanG U b n x m}

def bellmanMin (U b : ℚ) (n : ℕ) (y m : ℚ) : Set ℚ :=
  {z | z ∈ Set.Icc 0 U ∧ y ≤ z ∧ bellmanG U b n z m = bellmanV U b n y m}

/-- Independent-demand recursion keeps the mean fixed at μ. -/
def independentV (U b μ : ℚ) : ℕ → ℚ → ℝ
  | 0, _ => 0
  | n+1, y => sInf ((fun z : ℚ =>
      sSup ((fun q : DemandLaw => expectation q (fun d =>
        cost b z d + independentV U b μ n (z-d))) '' meanLaws U μ)) ''
      {z | z ∈ Set.Icc 0 U ∧ y ≤ z})

def independentF (U b μ : ℚ) (n : ℕ) (x d : ℚ) : ℝ :=
  cost b x d + independentV U b μ (n-1) (x-d)

def independentG (U b μ : ℚ) (n : ℕ) (x : ℚ) : ℝ :=
  sSup ((fun q => expectation q (independentF U b μ n x)) '' meanLaws U μ)

def independentMax (U b μ : ℚ) (n : ℕ) (x : ℚ) : Set DemandLaw :=
  {q | q ∈ meanLaws U μ ∧ expectation q (independentF U b μ n x) = independentG U b μ n x}

def independentMin (U b μ : ℚ) (n : ℕ) (y : ℚ) : Set ℚ :=
  {z | z ∈ Set.Icc 0 U ∧ y ≤ z ∧ independentG U b μ n z = independentV U b μ n y}

end XinMartingaleInventory.Minimax


