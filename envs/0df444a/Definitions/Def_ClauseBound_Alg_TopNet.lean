-- Prove2me | Definitions.Def_ClauseBound_Alg_TopNet
-- name    : ClauseBound_Alg_TopNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:29:40.10633+00:00
-- url     : https://prove2.me/theorems/8796b8fb-e1f4-46e5-8762-4ca368440305
-- title:
--   Top Net
-- statement:
--   Definitions and structural lemmas for Top Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace ClauseBound.Alg
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def lamS (K g Ub P : ℕ) : ℕ := (K ^ 3 + K * Ub + g * P) / K ^ 3
def bitsS (K g P B : ℕ) : ℕ := P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K
def valS {C : Type} (pad : U) (i : Idx) (Ub P : ℕ) (F : FNet C) (c : C) : ℤ :=
  (rebalG pad (S.K i) (3 * S.K i ^ 8) (lamS (S.K i) (3 * S.K i ^ 8) Ub P) F c).elim 0 fun I => S.run (pad, i, I)
def needNet (i : Idx) (Ub P B : ℕ) : ℕ :=
  max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (P * (2 * (3 * S.K i ^ 8) / S.K i + 1)))
    (max ((S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) Ub P)
      (S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) Ub P) (), List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) P B) ())))
def StValS : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (C : Type) (F : FNet C) (c : C) (pad : U) (i : Idx)
  (N : Network (Fin (3 * S.K i ^ 8)) (List Bool) (List Bool)) (Ub P B : ℕ), ok i → 2 ≤ S.K i → F.toP.Presents c N 0 0 → N.Sized P B → N.U ≤ Ub →
  2 ^ needNet S i Ub P B ≤ pad.length → valS S pad i Ub P F c = N.value
def StCertValS : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (C : Type) [Enc C] (F : FNet C), FKeeps F →
  ∀ (α : Type) [Enc α] (pad : α → U) (i : α → Idx) (Ub P : α → ℕ) (c : α → C), PolyT pad → PolyT i → Unary Ub → Unary P → PolyT c →
  PolyT fun t => valS S (pad t) (i t) (Ub t) (P t) F (c t)
end ClauseBound.Alg


