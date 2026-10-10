-- Prove2me | Definitions.Def_actuarial_scrPortfolioQuadratic
-- name    : actuarial_scrPortfolioQuadratic
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:11:43.635859+00:00
-- url     : https://prove2.me/theorems/fdc02c65-15bf-4dcf-8fb5-c090b01cfdcf
-- title:
--   Finite-dimensional standard formula quadratic aggregation: scrPortfolioQuadratic
-- statement:
--   The finite quadratic risk charge includes all ordered pairs of standard formula module indices. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q_n=\sum_{i,j<n}\rho_{ij}C_iC_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def scrPortfolioQuadratic (c : ℕ → ℝ) (corr : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, corr i j * c i * c j

end ActuarialValuation


