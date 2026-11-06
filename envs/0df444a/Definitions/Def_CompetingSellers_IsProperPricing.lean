-- Prove2me | Definitions.Def_CompetingSellers_IsProperPricing
-- name    : CompetingSellers_IsProperPricing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:15.466721+00:00
-- url     : https://prove2.me/theorems/a96ee8f9-017f-4711-b1f7-d3ce54696047
-- title:
--   Proper pricing function $P:[0,1]\to\mathbb R_{\ge0}\cup\{\infty\}$
-- statement:
--   A **pricing function** $P:[0,1]\to\mathbb R_{\ge0}\cup\{\infty\}$ lets the buyer obtain the good with probability $x$ for the expected payment $P(x)$; $P(x)=\infty$ means the allocation is unavailable. Let $\bar x=\sup\{x:P(x)<\infty\}$. $P$ is **proper** if
--
--   1. $P(0)=0$,
--   2. $P$ is non-decreasing, and
--   3. $P$ is continuous and weakly convex on $[0,\bar x]$ (continuity at the endpoint in the extended-real sense).
--
--   A pricing function used as a seller's mechanism must in addition satisfy $P(\bar x)<\infty$ (footnote 19).
--
--   Proper pricing functions are the menus to which every mechanism reduces (Observation 2.2).
--
--   **Formalization Note** $P$ is a map $\mathbb R\to[0,\infty]$ read on $[0,1]$; continuity is in the topology of $[0,\infty]$ and convexity is the convexity inequality in $[0,\infty]$.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2 Pricing Functions and the Taxation Principle, p.16 (PDF 19), footnote 19

import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace CompetingSellers

/-- `x̄ = sup{x ∈ [0, 1] : P(x) < ∞}`, the supremum of the allocation probabilities available at
finite prices (p.16). -/
noncomputable def xBar (P : ℝ → ℝ≥0∞) : ℝ :=
  sSup {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ P x ≠ ⊤}

/-- **Proper pricing function** (§2 "Pricing Functions and the Taxation Principle", p.16).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.16 (PDF 19): "a pricing mechanism is described by a
pricing function `P : [0, 1] → ℝ≥0 ∪ {∞}`. The buyer can choose any `x ∈ [0, 1]` with
`P(x) < ∞`, make an expected payment of `P(x)`, and receive the good with probability `x`. …
We say that a pricing function is proper if (a) `P(0) = 0`, (b) `P` is non-decreasing, and (c)
`P` is continuous and weakly convex on the interval `[0, x̄]`, where `x̄ = sup{x : P(x) < ∞}`";
footnote 19: "Endpoint continuity is understood in the extended-real sense."

**Formalization Note.** A pricing function is a map `ℝ → ℝ≥0∞` of which only the values on
`[0, 1]` matter; `∞` (`⊤`) marks an unavailable allocation. Continuity on `[0, x̄]` is in the
topology of `ℝ≥0∞` (so `P(x) → ∞` at `x̄` is allowed when `P(x̄) = ∞`); weak convexity is the
convexity inequality in `ℝ≥0∞`. -/
def IsProperPricing (P : ℝ → ℝ≥0∞) : Prop :=
  P 0 = 0 ∧ MonotoneOn P (Set.Icc 0 1) ∧ ContinuousOn P (Set.Icc 0 (xBar P)) ∧
    ∀ x ∈ Set.Icc 0 (xBar P), ∀ y ∈ Set.Icc 0 (xBar P), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      P (t * x + (1 - t) * y) ≤ ENNReal.ofReal t * P x + ENNReal.ofReal (1 - t) * P y

/-- A pricing function usable as a seller's mechanism (footnote 19, p.16): proper, and
`P(x̄) < ∞`. -/
def IsSellerPricing (P : ℝ → ℝ≥0∞) : Prop :=
  IsProperPricing P ∧ P (xBar P) ≠ ⊤

end CompetingSellers


