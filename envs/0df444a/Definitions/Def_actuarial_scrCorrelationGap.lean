-- Prove2me | Definitions.Def_actuarial_scrCorrelationGap
-- name    : actuarial_scrCorrelationGap
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:11:21.618255+00:00
-- url     : https://prove2.me/theorems/51fcca48-48eb-4ead-a442-3abf1450d88c
-- title:
--   Diversification gains and pairwise correlation bounds: scrCorrelationGap
-- statement:
--   The loss of perfect positive correlation measures potential diversification for nonnegative risk modules. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g=1-\rho
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def scrCorrelationGap (rho : ℝ) : ℝ := 1-rho

end ActuarialValuation


