-- Prove2me | Definitions.Def_StepMachines_Math_SideCodes
-- name    : StepMachines_Math_SideCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:36:52.19034+00:00
-- url     : https://prove2.me/theorems/8a0dbfd5-e072-412c-8d50-a9f3f6d48930
-- title:
--   Side Codes
-- statement:
--   Definitions and structural lemmas for Side Codes, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
set_option autoImplicit false
section
section
namespace Groundwork.Grid
open Finset
def gridE (g : ℕ) (tr : Bool) : Fin (g * g) ≃ Fin g × Fin g :=
  if tr = true then finProdFinEquiv.symm.trans (Equiv.prodComm _ _) else finProdFinEquiv.symm
def node (g : ℕ) (tr : Bool) (a i : ℕ) : ℕ := if tr = true then a + g * i else i + g * a
def he (g ℓ : ℕ) (z : List Bool) (x u : ℕ) : List Bool := block ℓ u (block (g * g * ℓ) x z)
def vC (g n : ℕ) : Code (univ : Finset (Fin g → Bits n)) (g * n) :=
  ((bitsC n).blocks (Equiv.refl (Fin g))).cast Fintype.piFinset_univ rfl
def nodeC (g : ℕ) (tr : Bool) (n : ℕ) : Code (univ : Finset (Fin g × Fin g → Bits n)) (g * g * n) :=
  ((bitsC n).blocks (gridE g tr).symm).cast Fintype.piFinset_univ rfl
def stC (g : ℕ) (tr : Bool) (n : ℕ) : Code (univ : Finset (Fin g → Fin g × Fin g → Bits n)) (g ^ 3 * n) :=
  ((nodeC g tr n).blocks (Equiv.refl (Fin g))).cast Fintype.piFinset_univ (by ring)
noncomputable def instW {K : ℕ} (n : ℕ) (Rm : Inst (Fin K) (List Bool)) : Inst (Fin K) (Bits n) :=
  fun v θ => Rm v fun u => if u = v then [] else (bitsC n).enc (θ u)
noncomputable def sideR (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : Inst (Fin g × Fin g) (Bits n) :=
  onGrid (instW n Rm) (fun _ => false) (gridE g tr)
end Groundwork.Grid


