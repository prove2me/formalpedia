-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLength
-- name    : OddOrder_BG_Ch1_Preliminary_PLength
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:04:51.950628+00:00
-- url     : https://prove2.me/theorems/c06ff939-9b25-4a77-95af-d6cfb5e0efef
-- title:
--   $p$-length one
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §5: a group $G$ has $p$-length one if $G=O_{p',p,p'}(G)$. This predicate is a shared BG hypothesis used in §5 (Thm 5.6), §6 (Lemma 6.6 / Thm 6.7) and §10.
--
--   The main definition is `hasPLengthOne`, the predicate $G=O_{p',p,p'}(G)$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/PLength.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/PLength.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main

namespace OddOrder.BG.Ch1

open OddOrder.Isaacs

/-- **BG "`G` has `p`-length one"** (§5, mmd L1943): `G = O_{p',p,p'}(G)`, encoded as the
quotient `G / O_{p',p}(G)` being a `p'`-group (`p ∤ |G / O_{p',p}(G)|`). -/
def hasPLengthOne (p : ℕ) (G : Type*) [Group G] : Prop :=
  ¬ p ∣ Nat.card (G ⧸ Ch03.oPiPrimePiCore {p} G)

end OddOrder.BG.Ch1


