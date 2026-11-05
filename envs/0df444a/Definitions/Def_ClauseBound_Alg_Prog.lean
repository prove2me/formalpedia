-- Prove2me | Definitions.Def_ClauseBound_Alg_Prog
-- name    : ClauseBound_Alg_Prog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:07:25.022963+00:00
-- url     : https://prove2.me/theorems/2b2e8ee7-aea9-4ca2-a3a0-c6dace27a6b2
-- title:
--   Prog
-- statement:
--   Definitions and structural lemmas for Prog, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Prog.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace ClauseBound.Alg
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
def enumLen {C : Type} (g : ℕ) (F : FNet C) (c : C) (j : ℕ) : ℕ := if j / g < j % g then F.cap c (j / g) (j % g) else 0
def enumBits {C : Type} (g : ℕ) (F : FNet C) (c : C) : ℕ := ∑ j ∈ Finset.range (g * g), enumLen g F c j
def enumF {C : Type} (pad : U) (g : ℕ) (F : FNet C) (c : C) : ℤ :=
  sumF (2 ^ enumBits g F c) pad fun t =>
    prodL g fun a => sumF (2 ^ F.n c a) pad fun zi =>
      F.W (c, (a, toWord (F.n c a) zi)) * prodL g fun b =>
        if b = a then 1
        else F.f (c, ((a, b), (toWord (F.n c a) zi, chunkAt (enumLen g F c) (min a b * g + max a b) (toWord (enumBits g F c) t))))
section Level
variable (P : PiecesF)
def gctx (pad : U) (s : Step) (tr : Bool) (I : PInst) (y : ℕ) : GridCtx := ((pad, (s.1.2.1, s.1.2.2), tr, s.2.1.2), (I.1, y, I.2))
def nPat (s : Step) (lam : ℕ) : ℕ := P.cnt s.h lam ^ nRectG s.p s.d
def sumDig (s : Step) (lam y : ℕ) : ℕ := ∑ q ∈ Finset.range (nRectG s.p s.d), digit (P.cnt s.h lam - 1) y q
def colSide (s : Step) (lam y : ℕ) : Bool :=
  if s.thin = true then decide (sumDig P s lam y ^ 2 * s.a ≤ s.b * (nRectG s.p s.d * Pieces.nblk lam s.h) ^ 2)
  else decide (totalG P s.p s.d true s.h lam y < totalG P s.p s.d false s.h lam y)
def capSum (h lam : ℕ) : ℕ := (Finset.range (P.cnt h lam)).sup fun i => P.cap false h lam i + P.cap true h lam i
def Nof (s : Step) (lam : ℕ) : ℕ := (s.p * s.d) ^ 2 * lam
def ubarG (s : Step) (lam : ℕ) : ℕ :=
  if s.thin = true then Nof s lam - Nof s lam / s.a + (s.p * s.d) ^ 2
  else s.p * (s.p - 1) * s.d * lam + nRectG s.p s.d * capSum P s.h lam
def ebarG (s : Step) (lam : ℕ) : ℕ :=
  c2 s.d * s.p * lam + nRectG s.p s.d + 8 * (Nat.sqrt (s.b * (nRectG s.p s.d * (lam + s.h)) ^ 2 / s.a) + 1)
def lamNextG (s : Step) (lam : ℕ) : ℕ := (s.D * ubarG P s lam + 3 * s.p ^ 2 * (s.d ^ 2 * (P.m * lam))) / (s.D * s.K ^ 2) + 1
def childG (pad : U) (s : Step) (I : PInst) (y : ℕ) : Option PInst :=
  rebalG pad s.K s.p (lamNextG P s I.1.length) (gridF P) (gctx pad s (!s.thin && colSide P s I.1.length y) I y)
def expandG (pad : U) (s : Step) (I : PInst) : ℤ × List PInst :=
  (sumF (nPat P s I.1.length) pad fun y =>
      if (s.thin && colSide P s I.1.length y) = true then enumF pad s.d (gridF P) (gctx pad s true I y) else 0,
   (rng pad (nPat P s I.1.length)).filterMap fun y =>
      if (s.thin && colSide P s I.1.length y) = true then none else childG P pad s I y)
abbrev DState : Type := (ℤ × ℕ) × U × List PInst
def stepG (pad : U) (st : DState) (s : Step) : DState :=
  ((st.1.1 * (P.d s.h st.2.1.length ^ nRectG s.p s.d : ℕ) + ((st.2.2.map (expandG P pad s)).map Prod.fst).sum,
    st.1.2 * P.d s.h st.2.1.length ^ nRectG s.p s.d),
   List.replicate (lamNextG P s st.2.1.length) (), (st.2.2.map (expandG P pad s)).flatMap Prod.snd)
def descendG (pad : U) (sched : List Step) (I : PInst) : DState :=
  sched.foldl (fun st s => cap pad ((0, 1), [], []) (stepG P pad st s)) (cap pad ((0, 1), [], []) ((0, 1), I.1, [I]))
def solveG (pad : U) (K₀ : ℕ) (sched : List Step) (I : PInst) : ℤ :=
  ((descendG P pad sched I).1.1 + ((descendG P pad sched I).2.2.map (bruteF pad K₀)).sum) / (descendG P pad sched I).1.2
def PnG (s : Step) (lam : ℕ) : ℕ := P.m * (s.p * s.d ^ 2 * lam)
def bNextG (s : Step) (lam B : ℕ) : ℕ :=
  PnG P s lam * (2 * s.p / s.K) + (s.d * B + s.d ^ 2 * P.bits s.h lam) * (2 * s.p / s.K + 2 * s.p / s.K * (2 * s.p / s.K)) * s.K
structure BudG (F : ℕ) (s : Step) (lam : ℕ) : Prop where
  pieces : 2 ^ P.need s.h lam ≤ F
  pat : nPat P s lam ≤ F
  col : s.K ^ s.p ≤ F
  st : 2 ^ (PnG P s lam * (2 * s.p / s.K)) ≤ F
  lab : 2 ^ PnG P s lam ≤ F
  tab : 2 ^ ((s.K - 1) * lamNextG P s lam) ≤ F
  enumLab : s.thin = true → 2 ^ ebarG s lam ≤ F
  enumSt : s.thin = true → 2 ^ (s.p ^ 2 * s.d * lam) ≤ F
end Level
end ClauseBound.Alg


