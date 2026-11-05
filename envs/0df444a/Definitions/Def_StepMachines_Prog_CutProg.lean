-- Prove2me | Definitions.Def_StepMachines_Prog_CutProg
-- name    : StepMachines_Prog_CutProg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:37:06.312637+00:00
-- url     : https://prove2.me/theorems/615fdd13-56cf-4343-acfb-9ed3a88e8ce9
-- title:
--   Cut Prog
-- statement:
--   Definitions and structural lemmas for Cut Prog, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CutProg.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Math_CutWord
set_option autoImplicit false
section
section
namespace Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (sideCnt topTerm botTerm cutW)
abbrev CutQ : Type := (Bool × ℕ) × (List Bool × List Bool × List Bool)
def cutLen (q : CutQ) : ℕ := q.2.1.length
def cutValid (tr : Bool) (q : CutQ) : Bool := validW q.2.1.length (sideCnt tr q.2.1.length q.1.2) q.2.2.2
def cutTop (q : CutQ) : Bool := q.1.1
def topE (tr : Bool) (p : CutQ × ℕ) : ℤ := topTerm tr p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2
def cutPow (q : CutQ) : ℕ := 2 ^ q.2.1.length
def cutPop (p : CutQ × ℕ) : Bool := decide ((toWord p.1.2.1.length p.2).count true = p.1.1.2)
def cutLen' (p : CutQ × ℕ) : ℕ := p.1.2.1.length
def botE (tr : Bool) (p : (CutQ × ℕ) × ℕ) : ℤ := botTerm tr p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2 p.1.2 p.2
def cutP (tr : Bool) : Stepped CutQ ℤ :=
  ite (cutValid tr)
    (ite cutTop (prodRange cutLen (ofFun (topE tr)))
      (sumRange cutPow (ite cutPop (prodRange cutLen' (ofFun (botE tr))) (const 0))))
    (const 0)
end Groundwork.Prog


