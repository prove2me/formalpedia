-- Prove2me | Definitions.Def_VariableBound_Field_Cert
-- name    : VariableBound_Field_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:38:20.968676+00:00
-- url     : https://prove2.me/theorems/e7a56ff4-6e15-4852-a475-6e785653e60c
-- title:
--   Cert
-- statement:
--   Definitions and structural lemmas for Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.List.Find
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any


set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Fld.Cert
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
def irrS (s : ℕ) (g : List Bool) : Bool :=
  (wordsL s).all fun x => decide (x = zeroW g) || (wordsL s).any fun y => decide (mulW g x y = oneW g)
end VariableBound.Fld.Cert


