-- Prove2me | Definitions.Def_SparsificationLemma_Sketch
-- name    : SparsificationLemma_Sketch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:26:14.63466+00:00
-- url     : https://prove2.me/theorems/8acf7d96-e40d-47bf-9192-1a2677e0df44
-- title:
--   Sketch
-- statement:
--   Definitions and structural lemmas for Sketch, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Sketch.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_StepSparsifyDefs
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_SparsificationLemma_Nodes
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_ClauseBoundStatement
import Definitions.Def_CountKSatStatement
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace SparsificationLemma.Sketch
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
section branch
variable {θ : ℕ → ℕ} {k : ℕ} {x : CNode} {H : PCl} {Q : PFml}
end branch
end SparsificationLemma.Sketch


