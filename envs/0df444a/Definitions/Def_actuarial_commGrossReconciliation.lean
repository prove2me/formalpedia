-- Prove2me | Definitions.Def_actuarial_commGrossReconciliation
-- name    : actuarial_commGrossReconciliation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:11:30.48765+00:00
-- url     : https://prove2.me/theorems/9d220a72-4e2a-4837-890c-79a05c6c6c12
-- title:
--   Finite commutation functions: commGrossReconciliation
-- statement:
--   Unnormalised insurance plus annuity plus survival value reconciliation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G=M_{x:n}+dN_{x:n}+D_{x+n}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commEffectiveDiscount
import Definitions.Def_actuarial_commSurvivorSum
import Definitions.Def_actuarial_commDeathSum
import Definitions.Def_actuarial_commTerminalLives

namespace ActuarialValuation

noncomputable def commGrossReconciliation (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := commDeathSum l v x n + commEffectiveDiscount v * commSurvivorSum l v x n + commTerminalLives l v x n

end ActuarialValuation


