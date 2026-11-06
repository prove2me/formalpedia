-- Prove2me | Definitions.Def_Eight_Cor_Defs
-- name    : Eight_Cor_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:11:09.865297+00:00
-- url     : https://prove2.me/theorems/862d2a99-496f-4e97-bb96-2c784d8cc178
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecPseudocode_Algorithm
import Definitions.Def_KSatStatement
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_GraphProblemsStatement
import Definitions.Def_CircuitLowerBoundStatement
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_Eight_Level_Defs
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
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_WidthK_Decode
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_GraphProblems_Sized
import Definitions.Def_GraphProblems_ColorTM
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Definitions.Def_PaddedDescent_BrutePad
import Theorems.Thm_Groundwork_PolyT_dropWhile
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.takeWhile


set_option autoImplicit false
section
section
namespace Eight
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Paper CountKSat CountKSat.CountTop GraphProblems
def stripW (y : List Bool) : List Bool := ((y.dropWhile id).tail).drop (y.takeWhile id).length
def Serves (E : Stepped (List Unit × Fml) (List Bool)) (k : ℕ) (δ : ℝ) (c : ℕ) : Prop := ∀ (N : ℕ) (ψ : Fml),
  (∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < N) → ψ.Nodup →
  ∃ T : ℕ, E.Runs (List.replicate N (), ψ) T (c * (N + 2) ^ c) (SatK.binary N (cntN N ψ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * N)
def StEngine : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ E : Stepped (List Unit × Fml) (List Bool), Nonempty (IsPolyT E) ∧ ∃ c : ℕ, Serves E k δ c
end Eight


