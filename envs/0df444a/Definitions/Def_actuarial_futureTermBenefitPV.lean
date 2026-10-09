-- Prove2me | Definitions.Def_actuarial_futureTermBenefitPV
-- name    : actuarial_futureTermBenefitPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T22:35:27.206381+00:00
-- url     : https://prove2.me/theorems/fc04ebcf-4b62-4cbb-8700-a5410f13c56f
-- title:
--   Prospective benefit value at duration
-- statement:
--   At duration t, a unit benefit is due at the end of the remaining death year if death occurs before expiry and the life was in force at t.
--
--   **Mathematical statement**
--
--   $$
--   B_{n,t}(\omega)=\mathbf1_{\{t\le K(\omega)<n\}}v^{K(\omega)+1-t}
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def futureTermBenefitPV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω) : ℝ :=
  if t ≤ K ω ∧ K ω < n then v ^ (K ω + 1 - t) else 0

end ActuarialValuation


