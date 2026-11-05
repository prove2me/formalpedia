-- Prove2me | Definitions.Def_Wrap_Coding
-- name    : Wrap_Coding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:57:23.017392+00:00
-- url     : https://prove2.me/theorems/c29c4282-6e0c-40a2-95f7-41e13168cf3f
-- title:
--   Coding
-- statement:
--   Definitions and structural lemmas for Coding, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Coding.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Definitions.Def_ToTuring_EncLemmas
set_option autoImplicit false
section
section
namespace Wrap
open Turing Groundwork
abbrev Rep : Type := (ℕ × ℕ) × List (List ℕ)
structure Coding (M : TM2ComputableAux Bool Bool) where
  /-- the value that stands for a configuration -/
  rep : M.tm.Cfg → Rep
  /-- one step, on values -/
  step : Rep → Rep
  /-- the start configuration on the bit string x, as a value -/
  init : List Bool → Rep
  /-- the output, if the value stands for a halted configuration -/
  out : Rep → Option (List Bool)
  /-- a constant for the two bounds on sizes -/
  a : ℕ
  /-- the step is polynomial-time -/
  step_poly : PolyT step
  /-- the start is polynomial-time -/
  init_poly : PolyT init
  /-- reading the output is polynomial-time -/
  out_poly : PolyT out
  /-- the step on values is the step of M -/
  step_rep : ∀ c : M.tm.Cfg, step (rep c) = rep (CircuitLowerBound.Tab.stay M c)
  /-- the start on values is the start configuration of M -/
  init_rep : ∀ x : List Bool, init x = rep (initList M.tm (x.map M.inputAlphabet.invFun))
  /-- on a halted configuration the output is the content of the output stack -/
  out_halted : ∀ c : M.tm.Cfg, c.l = none → out (rep c) = some ((c.stk M.tm.k₁).map M.outputAlphabet)
  /-- on a configuration that is not halted there is no output -/
  out_running : ∀ c : M.tm.Cfg, c.l ≠ none → out (rep c) = none
  /-- the start configuration is at most linear in the input -/
  size_init : ∀ x : List Bool, size (init x) ≤ a * (x.length + 1)
  /-- a step adds at most a constant to the size -/
  size_step : ∀ c : M.tm.Cfg, size (rep (CircuitLowerBound.Tab.stay M c)) ≤ size (rep c) + a
end Wrap


