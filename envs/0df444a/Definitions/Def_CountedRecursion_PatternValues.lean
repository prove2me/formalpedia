-- Prove2me | Definitions.Def_CountedRecursion_PatternValues
-- name    : CountedRecursion_PatternValues
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:18:52.533312+00:00
-- url     : https://prove2.me/theorems/0ca51bbc-4304-4202-9feb-32b7bea38df5
-- title:
--   Pattern Values
-- statement:
--   Definitions and structural lemmas for Pattern Values, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
noncomputable abbrev gridOf (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (W : ℕ → List Bool → ℤ) : Groundwork.Network (Fin (nParts g g tr)) (List Bool) (List Bool) :=
  gridN (piecesOf D c) [()] g g tr 0 lam y fun w θ => W w.val (List.ofFn θ).flatten
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
end ExplicitCost


