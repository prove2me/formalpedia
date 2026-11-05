-- Prove2me | Definitions.Def_PartitionStatement
-- name    : PartitionStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:12.487545+00:00
-- url     : https://prove2.me/theorems/8008583b-0d9e-4bba-badc-f928e812aa19
-- title:
--   Partition Statement
-- statement:
--   Definitions and structural lemmas for Partition Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PartitionStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option autoImplicit false
section
section
namespace Partitions
def p (E : ℕ) : ℕ := Fintype.card (Nat.Partition E)
noncomputable def cHR : ℝ := Real.pi * Real.sqrt (2 / 3)
noncomputable def kappa : ℝ := cHR / Real.log 2
def Bounds (B C : ℝ) : Prop :=
  (∀ E : ℕ, 1 ≤ E → kappa * Real.sqrt E - B * Real.logb 2 E - C ≤ Real.logb 2 (p E)) ∧
    ∀ E : ℕ, Real.logb 2 (p E) ≤ kappa * Real.sqrt E + C
end Partitions


