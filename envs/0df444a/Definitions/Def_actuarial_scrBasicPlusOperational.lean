-- Prove2me | Definitions.Def_actuarial_scrBasicPlusOperational
-- name    : actuarial_scrBasicPlusOperational
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:07.031161+00:00
-- url     : https://prove2.me/theorems/ee2aa713-4526-47a2-9130-04774676bd4f
-- title:
--   Finite-dimensional standard formula quadratic aggregation: scrBasicPlusOperational
-- statement:
--   The regulatory total capital equation combines basic capital, operational risk and a separately signed absorption adjustment. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SCR=BSCR+SCR_{op}+Adj
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def scrBasicPlusOperational (basic operational adjustment : ℝ) : ℝ := basic + operational + adjustment

end ActuarialValuation


