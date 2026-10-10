-- Prove2me | Definitions.Def_actuarial_orderStopLossDominates
-- name    : actuarial_orderStopLossDominates
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:24:22.982345+00:00
-- url     : https://prove2.me/theorems/fb20c447-94fe-4320-97e3-21fc18c550a6
-- title:
--   Finite-grid stop-loss ordering of aggregate risks
-- statement:
--   The first aggregate loss distribution is no riskier in stop-loss order than the second when its expected excess payment never exceeds the other's for any integer attachment d. Equal means and unit total masses can be imposed separately to obtain a mean-preserving spread interpretation.
--
--   **Mathematical statement**
--
--   $$
--   f\preceq_{\rm sl}g\iff\forall d:\Pi_f(d)\le\Pi_g(d)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration actuarial_orderStopLossDominates is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossPremium

namespace ActuarialValuation

noncomputable def orderStopLossDominates
  (f g : ℕ → ℝ) (bound : ℕ) : Prop :=
  ∀ d : ℕ, orderStopLossPremium f bound d ≤
    orderStopLossPremium g bound d

end ActuarialValuation


