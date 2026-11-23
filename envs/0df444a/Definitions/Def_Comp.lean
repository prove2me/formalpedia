-- Prove2me | Definitions.Def_Comp
-- name    : Comp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:41:37.622613+00:00
-- url     : https://prove2.me/theorems/8d5c200f-1071-474e-abfd-fc554c84de69
-- title:
--   Comp
-- statement:
--   Definitions and structural lemmas for Comp, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp.lean

import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
import Definitions.Def_Comp_Search
import Definitions.Def_Comp_Shapley
import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_Reach
import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_RockPaperScissorsQ
import Definitions.Def_Comp_TwoStateQ
import Definitions.Def_Comp_SafetyChainQ
import Definitions.Def_Comp_HideOrRunQ
import Definitions.Def_Comp_LeakyGateQ
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true


