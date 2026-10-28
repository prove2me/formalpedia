-- Prove2me | Definitions.Def_actuarial_f_gmpAdjustedParallelInstalment
-- name    : actuarial_f_gmpAdjustedParallelInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:44:39.155336+00:00
-- url     : https://prove2.me/theorems/728e6b5d-c4b6-4e02-b151-cd8ed00af791
-- title:
--   GMP-adjusted parallel contract instalment
-- statement:
--   Algebraic parallel-payment comparator: take the linked monthly contract cashflow and add two arbitrary supplied supplement functions, one member and one survivor. Its signature does not require that these functions are legally certified minima or prevent overlapping statutory benefits.
-- source:
--   Original derived finite-state cashflow identity using monthlyLinkedInstalment and externally supplied supplements. Legislative relevance depends on the separately certified entitlements; PSA 1993 sections 17 and 87: https://www.legislation.gov.uk/ukpga/1993/48/section/87 .

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyLinkedInstalment

namespace ActuarialUnderpinsF
noncomputable def gmpAdjustedParallelInstalment
    (h r g z i j t : ℕ) (a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (survivorSupplement : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  monthlyLinkedInstalment h r g z i j t a b c sa sb estate
    ga gb gc gs ge +
  memberSupplement z i t + survivorSupplement z i j t
end ActuarialUnderpinsF


