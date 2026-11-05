-- Prove2me | Definitions.Def_GeneralPieces_DefGenPieces_Progs
-- name    : GeneralPieces_DefGenPieces_Progs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:19:10.355007+00:00
-- url     : https://prove2.me/theorems/5200bd72-5abd-463f-a31b-a1061e53d872
-- title:
--   Progs
-- statement:
--   Definitions and structural lemmas for Progs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Progs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
abbrev VQ : Type := (U × Bool) × (U × ℕ) × (List Bool × List Bool × List Bool × List Bool)
def valF (P : PiecesF) (q : VQ) : ℤ :=
  sumF (2 ^ P.cap q.1.2 q.2.1.1.length q.2.2.1.length q.2.1.2) q.1.1 fun t =>
    P.top (q.1, (q.2.1.1.length, q.2.1.2), (q.2.2.1, q.2.2.2.1, toWord (P.cap q.1.2 q.2.1.1.length q.2.2.1.length q.2.1.2) t)) *
      P.bot (q.1, (q.2.1.1.length, q.2.1.2), (q.2.2.2.2.1, q.2.2.2.2.2, toWord (P.cap q.1.2 q.2.1.1.length q.2.2.1.length q.2.1.2) t))
def isLong (q : PQ) : Bool := decide (q.2.2.2.2.length = 2 * q.2.2.1.length)
def Realizes (P : PiecesF) (h lam : ℕ) (A : ℕ → Pieces.Four lam) : Prop :=
  (∀ x y u v, ∑ i ∈ Finset.range (P.cnt h lam), A i x y u v = P.d h lam * Pieces.cross x y u v) ∧
  (∀ i < P.cnt h lam, ∀ x y u v, |A i x y u v| ≤ 2 ^ P.bits h lam) ∧
  ∀ pad : U, 2 ^ P.need h lam ≤ pad.length → ∀ i < P.cnt h lam,
    (∀ x y u v, A i x y u v = ∑ θ ∈ words (P.cap false h lam i),
      P.top ((pad, false), (h, i), (bitsOf x, bitsOf y, θ)) * P.bot ((pad, false), (h, i), (bitsOf u, bitsOf v, θ))) ∧
    (∀ x y u v, A i x y u v = ∑ θ ∈ words (P.cap true h lam i),
      P.top ((pad, true), (h, i), (bitsOf x, bitsOf u, θ)) * P.bot ((pad, true), (h, i), (bitsOf y, bitsOf v, θ))) ∧
    ∀ tr (x y : Pieces.Bits lam) θ, |P.top ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ P.bits h lam ∧
      |P.bot ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ P.bits h lam
def valOf (P : PiecesF) (q : ValQ) : ℤ := valF P ((q.1, false), ([], q.2.1.2), q.2.2)
def atZero (P : PiecesF) (c m : ℕ) : PiecesF where
  cnt _ lam := P.cnt 0 lam
  d _ lam := P.d 0 lam
  cap tr _ lam i := P.cap tr 0 lam i
  top q := P.top (q.1, (0, q.2.1.2), q.2.2)
  bot q := P.bot (q.1, (0, q.2.1.2), q.2.2)
  need _ lam := c * lam
  bits _ lam := (2 * lam) ^ c
  m := m
def askAt (q : PQ) : List Bool × List Bool × List Bool × List Bool :=
  bif q.1.2 then (q.2.2.2.2.take q.2.2.1.length, q.2.2.1, q.2.2.2.2.drop q.2.2.1.length, q.2.2.2.1)
  else (q.2.2.2.2.take q.2.2.1.length, q.2.2.2.2.drop q.2.2.1.length, q.2.2.1, q.2.2.2.1)
def trimV (P : PiecesF) (val : ValQ → ℤ) (c : ℕ) : PiecesF where
  cnt _ lam := P.cnt 0 lam
  d _ lam := P.d 0 lam
  cap tr _ lam i := min (P.cap tr 0 lam i) (2 * lam)
  top q := bif isLong q then (if q.2.2.1 ++ q.2.2.2.1 = q.2.2.2.2 then 1 else 0) else P.top (q.1, (0, q.2.1.2), q.2.2)
  bot q := bif isLong q then val (q.1.1, (List.replicate q.2.2.1.length (), q.2.1.2), askAt q) else P.bot (q.1, (0, q.2.1.2), q.2.2)
  need _ lam := c * lam
  bits _ lam := (2 * lam) ^ c
  m := 1
end GeneralPieces


