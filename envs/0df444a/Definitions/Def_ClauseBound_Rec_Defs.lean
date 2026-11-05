-- Prove2me | Definitions.Def_ClauseBound_Rec_Defs
-- name    : ClauseBound_Rec_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:28:04.989704+00:00
-- url     : https://prove2.me/theorems/5bf49b2a-9197-4a8f-8c14-c76cfd7aa99c
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Defs.lean

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
import Definitions.Def_PiecesStatement
import Definitions.Def_ClauseBound_Rec_Window
set_option autoImplicit false
section
section
namespace ClauseBound.Rec
open Finset Polynomial Pieces
def sg (h : Bool × Bool) : ℤ := if h = (true, true) then -1 else 1
abbrev BLab (n h : ℕ) (b : Fin (nblk n h)) : Type := {k : Fin n // k.val / h = b.val} → Bool × Bool
end ClauseBound.Rec


