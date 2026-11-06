-- Prove2me | Definitions.Def_Eight_Cor_ENP
-- name    : Eight_Cor_ENP
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:18:18.740581+00:00
-- url     : https://prove2.me/theorems/c81b9354-19fd-4baf-90e1-2e47fa44bf5d
-- title:
--   ENP
-- statement:
--   Definitions and structural lemmas for ENP, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/ENP.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundStatement
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_Eight_Cor_Defs
import Definitions.Def_Eight_Level_End
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_KSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_WidthK_Top_EndLemmas
import Definitions.Def_WidthK_Decode
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_CircuitLowerBound_Closed
import Definitions.Def_CircuitLowerBound_Inf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight
open ENP Groundwork Turing CircuitLowerBound
end Eight


