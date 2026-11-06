-- Prove2me | Definitions.Def_Eight_Cor_Graph
-- name    : Eight_Cor_Graph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:17:55.205872+00:00
-- url     : https://prove2.me/theorems/8a7b2761-3d26-4e10-a603-720d3f60ce2c
-- title:
--   Graph
-- statement:
--   Definitions and structural lemmas for Graph, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Graph.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblemsStatement
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
import Definitions.Def_GraphProblems_Sized
import Definitions.Def_GraphProblems_ColorTM
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_CountKSat_Walk
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_WidthK_Top_Sat
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
namespace Eight
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat GraphProblems Finset Turing
end Eight


