-- Prove2me | Definitions.Def_GraphProblems_SetTM
-- name    : GraphProblems_SetTM
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:56:50.546146+00:00
-- url     : https://prove2.me/theorems/be2d8fc7-2621-4bca-8a24-2f69ef2bb419
-- title:
--   Set TM
-- statement:
--   Definitions and structural lemmas for Set TM, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/SetTM.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
namespace GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Turing
public abbrev Inst : Type := (n : ℕ) × SimpleGraph (Fin n) × {s : ℕ // s ≤ n}
@[expose] public def nzW (v : ℕ) : List Bool := [decide (v ≠ 0)]
@[expose] public def readF (F : ℕ → List Bool → Fml) (x : List Bool) : List Unit × ℕ × Fml :=
  ((read2 x).1, (read2 x).2.1, F (read2 x).1.length (read2 x).2.2)
end GraphProblems


