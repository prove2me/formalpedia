-- Prove2me | Definitions.Def_ClauseBound_Inst_RecArith
-- name    : ClauseBound_Inst_RecArith
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:08:03.045373+00:00
-- url     : https://prove2.me/theorems/c231c424-6c15-4822-8dde-33c7aa353b11
-- title:
--   Rec Arith
-- statement:
--   Definitions and structural lemmas for Rec Arith, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
def powZ (b : ℤ) (k : ℕ) : ℤ := prodL k fun _ => b
def fallZ (a : ℤ) (k : ℕ) : ℤ := prodL k fun i => a - i
def factN (k : ℕ) : ℕ := (prodL k fun i => (i : ℤ) + 1).natAbs
def chooseZ (a : ℤ) (k : ℕ) : ℤ :=
  if fallZ a k < 0 then -(((fallZ a k).natAbs / factN k : ℕ) : ℤ) else (((fallZ a k).natAbs / factN k : ℕ) : ℤ)
def sumR (w : ℕ) (f : ℕ → ℤ) : ℤ := ((List.range w).map f).sum
def sgnZ (a : ℤ) : ℤ := if a.natAbs % 2 = 0 then 1 else -1
def phiF (a : ℤ) (w : ℕ) (j : ℤ) : ℤ := sgnZ a * sumR w fun k => powZ (-2) k * chooseZ (j - a) k
def qqF (μ t j : ℕ) : ℤ := phiF ((μ : ℤ) - t) (2 * t + 1) j - phiF ((μ : ℤ) - t + 1) (2 * t - 1) j
def linF (a : ℤ) (w : ℕ) (σ : ℤ) (ν z n₀ : ℕ) (ε : Bool) (r : ℕ) : ℤ :=
  σ * sumR (z + 1) fun i => chooseZ z i * powZ (powZ 2 n₀) (z - i) * powZ (1 - powZ 2 n₀) i *
    ((bif ε then powZ 2 r else 1) * phiF a (w - (ν + i)) 0 + (bif ε then 1 - powZ 2 r else 0) * phiF a (w - (ν + i + 1)) 0)
def ccF (μ t : ℕ) (σ : ℤ) (ν z n₀ : ℕ) (ε : Bool) (r : ℕ) : ℤ :=
  linF ((μ : ℤ) - t) (2 * t + 1) σ ν z n₀ ε r - linF ((μ : ℤ) - t + 1) (2 * t - 1) σ ν z n₀ ε r
def nbF (lam h b : ℕ) : ℕ := (List.range lam).countP fun k => decide (k / h = b)
def muF (lam h : ℕ) : ℕ :=
  ((List.range (Pieces.nblk lam h)).map fun b => (2 ^ nbF lam h b - 1) * 2 ^ (lam - nbF lam h b)).sum / 2 ^ (lam + 1)
variable {α β : Type} [Enc α] [Enc β]
end ClauseBound.Inst.Rec


