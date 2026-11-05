-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_StepOne
-- name    : ClauseBound_ParityChecks_StepOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:00.384996+00:00
-- url     : https://prove2.me/theorems/a30f83a7-73b7-4061-9540-51c4b018897c
-- title:
--   Step One
-- statement:
--   Definitions and structural lemmas for Step One, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
section Cutoff
variable {E : Type} {r : ℕ}
def fac (J₁ J₂ : Finset (Fin r)) (j : Fin r) (s : Finset E) : ℤ := if j ∈ J₁ then sig #s else if j ∈ J₂ then (-2) ^ #s else 1
def dom (A : Fin r → Finset E) (J : Finset (Fin r)) (j : Fin r) : Finset (Finset E) := if j ∈ J then (A j).powerset else {∅}
end Cutoff
end ClauseBound.ParityChecks.StepOne


