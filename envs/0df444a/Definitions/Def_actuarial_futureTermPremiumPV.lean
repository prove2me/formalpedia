-- Prove2me | Definitions.Def_actuarial_futureTermPremiumPV
-- name    : actuarial_futureTermPremiumPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T22:35:39.208242+00:00
-- url     : https://prove2.me/theorems/92bf0121-1c8b-4278-9c80-89ff4bfc52cc
-- title:
--   Prospective premium annuity at duration
-- statement:
--   Future level premiums occur at integer dates j from t to the earlier of term expiry or the last surviving payment date.
--
--   **Mathematical statement**
--
--   $$
--   Y_{n,t}(\omega)=\sum_{t\le j<n}v^{j-t}\mathbf1_{\{K(\omega)\ge j\}}
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def futureTermPremiumPV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, if t ≤ j ∧ j ≤ K ω then v ^ (j - t) else 0

end ActuarialValuation


