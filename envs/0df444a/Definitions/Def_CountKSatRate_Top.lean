-- Prove2me | Definitions.Def_CountKSatRate_Top
-- name    : CountKSatRate_Top
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:14:07.586355+00:00
-- url     : https://prove2.me/theorems/2878d128-8204-4ad5-914b-9acd9769cb75
-- title:
--   Top
-- statement:
--   Definitions and structural lemmas for Top, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Top.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace CountKSatRate.Top
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)
end CountKSatRate.Top
namespace CountKSatRate
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate.Top
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)
end CountKSatRate


