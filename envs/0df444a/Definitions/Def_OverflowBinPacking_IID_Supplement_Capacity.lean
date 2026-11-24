-- Prove2me | Definitions.Def_OverflowBinPacking_IID_Supplement_Capacity
-- name    : OverflowBinPacking_IID_Supplement_Capacity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:51:28.62932+00:00
-- url     : https://prove2.me/theorems/2ae75c1e-384c-4217-97fb-cce549ea9404
-- title:
--   Capacity-dependent feasibility, cost, and input laws
-- statement:
--   Let $a$ assign each item to a bin before observing its size. A policy feasible at capacity $c$ never assigns an item to a bin whose previous load exceeds $c$. The independent nonnegative input laws are probability measures on the nonnegative real numbers. Define
--   $$\operatorname{cost}_c(a)=\mathbb E[N_a]+C\mathbb E[O_{a,c}],$$
--   where $N_a$ counts opened bins and $O_{a,c}$ counts bins with final load strictly greater than $c$. At $c=1$ these definitions are definitionally the published feasibility and expected cost. Exponential laws have positive rate $r$ and survival probability $e^{-rt}$ for every $t\ge0$.
--
--   This interface changes capacity without imposing unit-capacity feasibility at larger capacities. The bounded input predicate records support in $[0,1+\varepsilon]$; it does not implement or assume the paper's informal truncation reduction.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 20, §6.1; p. 14, §5

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Model

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

/-- The source's independent, nonnegative laws. -/
def InputLaws {n : ℕ} (μ : Fin n → Measure ℝ) : Prop :=
  (∀ i, IsProbabilityMeasure (μ i)) ∧ ∀ i, μ i (Set.Iio 0) = 0

def BoundedInput {n : ℕ} (μ : Fin n → Measure ℝ) (ε : ℝ) : Prop :=
  InputLaws μ ∧ ∀ i, μ i (Set.Iic (1 + ε))ᶜ = 0

/-- Capacity is a parameter of feasibility, not a scaling of the penalty. -/
def PolicyAt {n : ℕ} (c : ℝ) (a : Rule n) : Prop :=
  Nonanticipative a ∧ MeasurableRule a ∧
    ∀ x (i : Fin n), usage a x (a i x) i ≤ c

noncomputable def brokenAt {n : ℕ} (c : ℝ) (a : Rule n) (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => c < usage a x j n)).card

noncomputable def costAt {n : ℕ} (μ : Fin n → Measure ℝ) (C c : ℝ)
    (a : Rule n) : ℝ :=
  ∫ x, ((numOpened a x : ℝ) + C * (brokenAt c a x : ℝ)) ∂Measure.pi μ

/-- Survival-function characterization, including positivity and probability. -/
def ExponentialLaw (ν : Measure ℝ) (rate : ℝ) : Prop :=
  0 < rate ∧ IsProbabilityMeasure ν ∧ ν (Set.Iio 0) = 0 ∧
    ∀ t : ℝ, 0 ≤ t → ν.real (Set.Ioi t) = Real.exp (-rate * t)

end OverflowBinPacking.IID.Supplement


