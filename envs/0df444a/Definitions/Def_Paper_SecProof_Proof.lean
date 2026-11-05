-- Prove2me | Definitions.Def_Paper_SecProof_Proof
-- name    : Paper_SecProof_Proof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:18:17.348626+00:00
-- url     : https://prove2.me/theorems/a69d4082-87d8-4685-8e71-03672688b8c3
-- title:
--   Sec Proof Proof
-- statement:
--   Definitions and structural lemmas for Sec Proof Proof, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecProof_Proof.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Math_SatArith
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_StepMachines_Math_SparsifyList
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Sat
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace Paper
open Groundwork Groundwork.Prog Finset
abbrev Formula : Type := Fml
def Formula.Is3CNF (n : ℕ) (ψ : Formula) : Prop := ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n
abbrev clusterSize (g : ℕ) (Φ : Formula) : ℕ := Count.mu g Φ
abbrev networkOf (g : ℕ) (Φ : Formula) : Network (Fin g) (List Bool) (List Bool) := Count.wordNet g 3 Φ
end Paper


