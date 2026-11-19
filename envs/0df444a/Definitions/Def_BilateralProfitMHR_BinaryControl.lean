-- Prove2me | Definitions.Def_BilateralProfitMHR_BinaryControl
-- name    : BilateralProfitMHR_BinaryControl
-- status  : Definition
-- author  : @sim2000dg
-- created : 2026-11-18T12:18:21.967676+00:00
-- url     : https://prove2.me/theorems/778908ae-710c-4dae-bfa0-42af3c0d61e9
-- title:
--   Finite binary controllers and posted-price policy realization
-- statement:
--   A finite binary controller consists of a state space, an action map, an initial state, and a state update after each Boolean observation. The function `binaryValue` is its finite-horizon expected cumulative nonnegative cost when the success probability at action x is q(x). The function `binaryRunState` reads a finite Boolean history in chronological order. Given seed-dependent actions and updates, legal prices at every state, and measurability of each fixed-history action in the seed, `controllerPolicy` realizes the controller as a nonanticipating posted-price policy: it reads each previous feedback pair only through the product of its two acceptance bits.

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model

noncomputable section
namespace BilateralProfitMHR
open MeasureTheory BilateralProfit Set
open scoped ENNReal

def binaryValue {X S : Type} (q : X → ℝ) (g : X → ℝ≥0∞)
    (act : S → X) (step : S → Bool → S) : ℕ → S → ℝ≥0∞
  | 0, _ => 0
  | n + 1, s =>
      g (act s) + (ENNReal.ofReal (q (act s)) * binaryValue q g act step n (step s true) +
        ENNReal.ofReal (1 - q (act s)) * binaryValue q g act step n (step s false))

variable {Ω S : Type} [MeasurableSpace Ω]

def binaryRunState (step : Ω → S → Bool → S) (sinit : Ω → S) :
    (t : ℕ) → (Fin t → Bool) → Ω → S
  | 0, _, ω => sinit ω
  | t+1, h, ω => step ω (binaryRunState step sinit t (Fin.init h) ω) (h (Fin.last t))

def controllerPolicy (T : ℕ) (act : Ω → S → ℝ × ℝ) (step : Ω → S → Bool → S)
    (sinit : Ω → S) (hlegal : ∀ ω s, act ω s ∈ unitSq)
    (hmeas : ∀ t (h : Fin t → Bool), Measurable fun ω => act ω (binaryRunState step sinit t h ω)) :
    Policy T Ω where
  price t ω h := act ω (binaryRunState step sinit t (fun i => (h i).1 && (h i).2) ω)
  price_mem t ω h := hlegal ω _
  price_measurable t h := hmeas t _


end BilateralProfitMHR


