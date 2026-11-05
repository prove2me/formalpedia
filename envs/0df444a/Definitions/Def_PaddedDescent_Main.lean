-- Prove2me | Definitions.Def_PaddedDescent_Main
-- name    : PaddedDescent_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:19:37.017106+00:00
-- url     : https://prove2.me/theorems/870b2f77-a1fb-460b-ab55-aef6c52893c5
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_Reduce
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_PaddedDescent_F_Expand
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_MarkLayers
import Definitions.Def_PaddedDescent_F_MarkCode
import Definitions.Def_PaddedDescent_F_MarkVal
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkSum
import Definitions.Def_PaddedDescent_F_MarkSize
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_ArithSched
import Definitions.Def_PaddedDescent_F_ArithA
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_PaddedDescent_F_CertSide
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_PaddedDescent_F_CertA
set_option autoImplicit false
section
namespace Sat3
open PaddedDescent PaddedDescent.F
end Sat3


