-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Dummy
-- name    : ClauseBound_ParityChecks_Dummy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:22.968876+00:00
-- url     : https://prove2.me/theorems/505214b3-22c2-45ea-8ba0-9084add8acad
-- title:
--   Dummy
-- statement:
--   Definitions and structural lemmas for Dummy, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option autoImplicit false
section
section
open Finset ParityChecks
namespace ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
def inc (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (ξ : X) (y : Fin r → Bool) : Finset (E × Fin r) :=
  univ.filter fun q => q.1 ∈ Λ q.2 ∩ V ξ ∧ ((q.2 ∈ J₁ ∧ y q.2 = true) ∨ q.2 ∈ J₂)
def fac (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (ξ : X) (j : Fin r) (b : Bool) : ℤ :=
  if (j ∈ J₁ ∧ b = true) ∨ j ∈ J₂ then (-1) ^ #(Λ j ∩ V ξ) else 1
end ClauseBound.ParityChecks.Dummy


