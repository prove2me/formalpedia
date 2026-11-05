-- Prove2me | Definitions.Def_SparsifyWidthK_DefsProg
-- name    : SparsifyWidthK_DefsProg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:33:59.86386+00:00
-- url     : https://prove2.me/theorems/59b572cf-e1ca-423e-8cf3-4ec5cbf1e98f
-- title:
--   Defs Prog
-- statement:
--   Definitions and structural lemmas for Defs Prog, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/DefsProg.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyTree
set_option autoImplicit false
section
section
namespace WidthK.Prog
open Groundwork.Sparsify
def maskP (m : List Bool) (C : PCl) : PCl := ((C.zip m).filter fun p => p.2).map fun p => p.1
def masks : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (masks k).flatMap fun m => [false :: m, true :: m]
def heartsP (k : ℕ) (s : PFml) (j h : ℕ) : PFml :=
  (s.filter fun C => decide (C.length = j)).flatMap fun C =>
    ((masks k).map fun m => maskP m C).filter fun H => decide (H.length = h)
def pairsK (k : ℕ) : List (ℕ × ℕ) :=
  (List.range (k + 1)).flatMap fun j => ((List.range j).reverse.filter fun h => decide (0 < h)).map fun h => (j, h)
def tryP (θ : ℕ → ℕ) (k : ℕ) (s : PFml) (jh : ℕ × ℕ) : Option (PCl × PFml) :=
  ((heartsP k s jh.1 jh.2).find? fun H => decide (θ (jh.1 - jh.2) ≤ (overP s jh.1 H).length)).map fun H =>
    (H, (overP s jh.1 H).map (minusP H))
def pickK (θ : ℕ → ℕ) (k : ℕ) (s : PFml) : Option (PCl × PFml) := ((pairsK k).filterMap (tryP θ k s)).head?
def stepK (θ : ℕ → ℕ) (k : ℕ) (s : PFml) : Option (PFml × PFml) :=
  (pickK θ k s).map fun HP => (addP [HP.1] s, addP HP.2 s)
def toFin (s : PFml) : Finset (Finset PLit) := (s.map List.toFinset).toFinset
def NF (s : PFml) : Prop := (∀ C ∈ s, C.Nodup) ∧ (s.map List.toFinset).Nodup
end WidthK.Prog


