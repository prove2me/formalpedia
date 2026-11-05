-- Prove2me | Definitions.Def_ClauseBound_Part_ListP
-- name    : ClauseBound_Part_ListP
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:51.667852+00:00
-- url     : https://prove2.me/theorems/a2c9d1f9-70ed-4365-89f2-122e2017a7e1
-- title:
--   List P
-- statement:
--   Definitions and structural lemmas for List P, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_PartitionStatement
import Definitions.Def_ClauseBound_Part_Rec
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Part
open Finset Partitions
@[expose] def partsLe : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[]]
  | _ + 1, 0 => []
  | E, k + 1 => partsLe E k ++ (if k + 1 ≤ E then (partsLe (E - (k + 1)) (k + 1)).map fun L => (k + 1) :: L else [])
termination_by E k => E + k
@[expose] def partsOf (E : ℕ) : List (List ℕ) := partsLe E E
namespace ListP
end ListP
open ListP
end ClauseBound.Part


