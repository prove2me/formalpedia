-- Prove2me | Definitions.Def_GeneralPieces_Group_Lemma
-- name    : GeneralPieces_Group_Lemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:59:56.680494+00:00
-- url     : https://prove2.me/theorems/1924ed6e-c341-4c76-a537-20f8a61b535a
-- title:
--   Lemma
-- statement:
--   Definitions and structural lemmas for Lemma, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Group
open Finset Groundwork
variable {J J' σ τ A : Type*}
open Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F PaddedDescent.F.RebalF PaddedDescent.Col
end GeneralPieces.Group
namespace GeneralPieces
open Finset Groundwork PaddedDescent.F ClauseBound.Alg GeneralPieces.Group
end GeneralPieces


