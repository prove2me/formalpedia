-- Prove2me | Definitions.Def_PairsToBound_FrontEnd
-- name    : PairsToBound_FrontEnd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:46:37.409958+00:00
-- url     : https://prove2.me/theorems/e3165368-474d-496c-9d14-70c7dbdef39a
-- title:
--   Front End
-- statement:
--   Definitions and structural lemmas for Front End, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/FrontEnd.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
@[expose] section
namespace PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)
@[expose] def widthN (ψ : Fml) : ℕ := (ψ.map List.length).foldr max 3
@[expose] def atWidthOr3 (x : List Bool) : List Bool := encN (List.replicate (widthN (fmlOf x).2) ()) (fmlOf x)
@[expose] def inMainRegime (K₀ : ℕ) (x : List Bool) : Bool :=
  decide (K₀ ^ 17 ≤ (fmlOf x).1.length) && decide (2 ^ (widthN (fmlOf x).2 ^ 4) ≤ (fmlOf x).1.length)
variable {α : Type} [Enc α]
end PairsToBound


