-- Prove2me | Definitions.Def_SparsificationLemma_Mach_Walk
-- name    : SparsificationLemma_Mach_Walk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:24:24.945629+00:00
-- url     : https://prove2.me/theorems/7993be8c-f7cd-4850-9b1c-db84259afdb2
-- title:
--   Walk
-- statement:
--   Definitions and structural lemmas for Walk, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Walk.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
def walkL (k : ℕ) (pad : U) (τ : ℕ) (r : CNode) : List CNode :=
  (pad.foldl (fun st _ => cap pad ([], []) (round (stepC (thetaU τ) k) st)) (cap pad ([], []) ([r], []))).2.reverse
def codeNatP (pad : U) (v : ℕ) : List Bool := (pad.take v).map (fun _ => true) ++ [false]
def codeLitP (pad : U) (l : PLit) : List Bool := l.2 :: codeNatP pad l.1
def codeClP (pad : U) (C : PCl) : List Bool := C.flatMap (fun l => true :: codeLitP pad l) ++ [false]
def codeFmlP (pad : U) (ψ : PFml) : List Bool := ψ.flatMap (fun C => true :: codeClP pad C) ++ [false]
def codeP (pad : U) (L : List PFml) : List Bool := L.flatMap (fun ψ => true :: codeFmlP pad ψ) ++ [false]
def sL (x : List Bool) : ℕ := (kOf x).length
def kL (x : List Bool) : ℕ := (kOf (restOf x)).length
def dL (x : List Bool) : U × Fml := fmlOf (restOf x)
def eL (x : List Bool) : ℕ := (dL x).1.length / 2 ^ sL x + kL x + 3 * Nat.size x.length + 9
def BL (p : List Bool × U) : List Bool :=
  codeP p.2 ((walkL (min (kL p.1) (Nat.log 2 p.2.length)) p.2 (tauOf (sL p.1)) (rootC (dL p.1))).map out)
def nodeLen (k n m : ℕ) : ℕ := 2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 6
section
variable {σ : Type} (step : σ → Option (σ × σ))
end
end SparsificationLemma.Mach


