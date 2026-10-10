-- Prove2me | Definitions.Def_actuarial_scrPairShift
-- name    : actuarial_scrPairShift
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:11:32.744069+00:00
-- url     : https://prove2.me/theorems/8f205231-536e-4394-a9ea-343e92ac5c64
-- title:
--   Diversification gains and pairwise correlation bounds: scrPairShift
-- statement:
--   Capital sensitivity to increasing one module while holding the other charge fixed. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q(C_1+h,C_2)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared

namespace ActuarialValuation

noncomputable def scrPairShift (rho c1 c2 add : ℝ) : ℝ := scrPairSquared rho (c1+add) c2

end ActuarialValuation


