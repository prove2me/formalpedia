-- Prove2me | Definitions.Def_actuarial_scrPairSquared
-- name    : actuarial_scrPairSquared
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:10:33.953985+00:00
-- url     : https://prove2.me/theorems/a960929a-5479-4c18-9324-8e64ed7d329c
-- title:
--   Two-module capital charges and correlation cross terms: scrPairSquared
-- statement:
--   The two-risk capital aggregation is formulated in squared units to avoid hidden square-root assumptions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q=SCR_1^2+SCR_2^2+2\rho SCR_1SCR_2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrCovarianceTerm

namespace ActuarialValuation

noncomputable def scrPairSquared (rho c1 c2 : ℝ) : ℝ := c1^2 + c2^2 + 2 * scrCovarianceTerm rho c1 c2

end ActuarialValuation


