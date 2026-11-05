-- Prove2me | Definitions.Def_ClauseBound_Alg_Data
-- name    : ClauseBound_Alg_Data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:06:03.415709+00:00
-- url     : https://prove2.me/theorems/24714ecb-ed50-40ea-a1d6-b2909af14c48
-- title:
--   Data
-- statement:
--   Definitions and structural lemmas for Data, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Data.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Definitions.Def_PiecesStatement
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace ClauseBound.Alg
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
abbrev PQ : Type := (U × Bool) × (ℕ × ℕ) × (List Bool × List Bool × List Bool)
structure PiecesF where
  cnt : ℕ → ℕ → ℕ
  d : ℕ → ℕ → ℕ
  cap : Bool → ℕ → ℕ → ℕ → ℕ
  top : PQ → ℤ
  bot : PQ → ℤ
  /-- the pad that the loops inside top and bot need, as an exponent of 2 -/
  need : ℕ → ℕ → ℕ
  /-- all values of the pieces and of top and bot have at most this many bits -/
  bits : ℕ → ℕ → ℕ
  /-- every cap is at most 2·m·λ (the paper has m = 1; code words that are easier to compute may
  need m = 2) -/
  m : ℕ
def bitsOf {n : ℕ} (x : Pieces.Bits n) : List Bool := List.ofFn x
structure PiecesF.Spec (P : PiecesF) (h lam : ℕ) : Prop where
  cnt_pos : 1 ≤ P.cnt h lam
  d_pos : 1 ≤ P.d h lam
  m_pos : 1 ≤ P.m
  cap_le : ∀ tr i, i < P.cnt h lam → P.cap tr h lam i ≤ 2 * P.m * lam
  ex : ∃ A : ℕ → Pieces.Four lam,
    (∀ x y u v, ∑ i ∈ Finset.range (P.cnt h lam), A i x y u v = P.d h lam * Pieces.cross x y u v) ∧
    (∀ i < P.cnt h lam, ∀ x y u v, |A i x y u v| ≤ 2 ^ P.bits h lam) ∧
    ∀ pad : U, 2 ^ P.need h lam ≤ pad.length → ∀ i < P.cnt h lam,
      (∀ x y u v, A i x y u v = ∑ θ ∈ words (P.cap false h lam i),
        P.top ((pad, false), (h, i), (bitsOf x, bitsOf y, θ)) * P.bot ((pad, false), (h, i), (bitsOf u, bitsOf v, θ))) ∧
      (∀ x y u v, A i x y u v = ∑ θ ∈ words (P.cap true h lam i),
        P.top ((pad, true), (h, i), (bitsOf x, bitsOf u, θ)) * P.bot ((pad, true), (h, i), (bitsOf y, bitsOf v, θ))) ∧
      ∀ tr (x y : Pieces.Bits lam) θ, |P.top ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ P.bits h lam ∧
        |P.bot ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ P.bits h lam
structure PiecesF.Keeps (P : PiecesF) : Prop where
  cnt : Unary fun p : U × U => P.cnt p.1.length p.2.length
  d : PolyT fun p : U × U => P.d p.1.length p.2.length
  cap : Unary fun p : Bool × U × U × ℕ => P.cap p.1 p.2.1.length p.2.2.1.length p.2.2.2
  top : PolyT P.top
  bot : PolyT P.bot
  need : Unary fun p : U × U => P.need p.1.length p.2.length
  bits : Unary fun p : U × U => P.bits p.1.length p.2.length
abbrev Step : Type := (U × U × U) × (U × U) × (Bool × U × U)
namespace Step
variable (s : Step)
def K : ℕ := s.1.1.length
def p : ℕ := s.1.2.1.length
def d : ℕ := s.1.2.2.length
def D : ℕ := s.2.1.1.length
def h : ℕ := s.2.1.2.length
def thin : Bool := s.2.2.1
def a : ℕ := s.2.2.2.1.length
def b : ℕ := s.2.2.2.2.length
end Step
def nRectG (p d : ℕ) : ℕ := c2 p * c2 d
def nParts (p d : ℕ) (tr : Bool) : ℕ := if tr = true then d else p
def nMemb (p d : ℕ) (tr : Bool) : ℕ := if tr = true then p else d
def nodeG (d : ℕ) (tr : Bool) (a i : ℕ) : ℕ := if tr = true then a + d * i else i + d * a
def rectIxG (d : ℕ) (tr : Bool) (q κ : ℕ) : ℕ := if tr = true then κ * c2 d + q else q * c2 d + κ
def heG (p d ℓ : ℕ) (z : List Bool) (x u : ℕ) : List Bool := block ℓ u (block (p * d * ℓ) x z)
abbrev GridCtx : Type := (U × (U × U) × Bool × U) × (U × ℕ × Tab)
section Grid
variable (P : PiecesF)
def digG (d : ℕ) (tr : Bool) (h ℓ y q κ : ℕ) : ℕ := digit (P.cnt h ℓ - 1) y (rectIxG d tr q κ)
def lenG (d : ℕ) (tr : Bool) (h ℓ y q κ : ℕ) : ℕ := P.cap tr h ℓ (digG P d tr h ℓ y q κ)
def capG (p d : ℕ) (tr : Bool) (h ℓ y a b : ℕ) : ℕ :=
  nMemb p d tr * ℓ + ∑ κ ∈ Finset.range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri (min a b) (max a b)) κ
def chkG (p d : ℕ) (tr : Bool) (ℓ : ℕ) (q : WQ) : Bool :=
  ((List.range (nMemb p d tr)).all fun i => (heG p d ℓ q.2 i (nodeG d tr q.1 i)).all (!·)) &&
    (List.range (nMemb p d tr)).all fun i => (List.range (nMemb p d tr)).all fun i' =>
      decide (i' ≤ i) || (heG p d ℓ q.2 i (nodeG d tr q.1 i') == heG p d ℓ q.2 i' (nodeG d tr q.1 i))
def gridW (p d : ℕ) (tr : Bool) (ℓ : ℕ) (T : Tab) (q : WQ) : ℤ :=
  bif chkG p d tr ℓ q then
    prodL (nMemb p d tr) fun i => look T (nodeG d tr q.1 i,
      (List.range (p * d)).map fun u => if u = nodeG d tr q.1 i then [] else heG p d ℓ q.2 i u)
  else 0
def gridFf (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) (q : FQ) : ℤ :=
  bif (List.range (nMemb p d tr)).all fun i => heG p d ℓ q.2.1 i (nodeG d tr q.1.2 i) == block ℓ i q.2.2 then
    prodL (nMemb p d tr * nMemb p d tr) fun j =>
      if j / nMemb p d tr < j % nMemb p d tr then
        (if q.1.1 < q.1.2 then P.top else P.bot) ((pad, tr),
          (h, digG P d tr h ℓ y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri (j / nMemb p d tr) (j % nMemb p d tr))),
          (heG p d ℓ q.2.1 (j / nMemb p d tr) (nodeG d tr q.1.2 (j % nMemb p d tr)),
           heG p d ℓ q.2.1 (j % nMemb p d tr) (nodeG d tr q.1.2 (j / nMemb p d tr)),
           chunkAt (lenG P d tr h ℓ y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2))) (tri (j / nMemb p d tr) (j % nMemb p d tr))
             (q.2.2.drop (nMemb p d tr * ℓ))))
      else 1
  else 0
def gridF : FNet GridCtx where
  n c _ := nMemb c.1.2.1.1.length c.1.2.1.2.length c.1.2.2.1 * (c.1.2.1.1.length * c.1.2.1.2.length) * c.2.1.length
  cap c a b := capG P c.1.2.1.1.length c.1.2.1.2.length c.1.2.2.1 c.1.2.2.2.length c.2.1.length c.2.2.1 a b
  W x := gridW x.1.1.2.1.1.length x.1.1.2.1.2.length x.1.1.2.2.1 x.1.2.1.length x.1.2.2.2 x.2
  f x := gridFf P x.1.1.1 x.1.1.2.1.1.length x.1.1.2.1.2.length x.1.1.2.2.1 x.1.1.2.2.2.length x.1.2.1.length x.1.2.2.1 x.2
def priceG (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) : ℕ :=
  2 * ∑ q ∈ Finset.range (nRectG p d), P.cap tr h ℓ (digit (P.cnt h ℓ - 1) y q)
def totalG (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) : ℕ :=
  nParts p d tr * (nParts p d tr - 1) * nMemb p d tr * ℓ + priceG P p d tr h ℓ y
end Grid
end ClauseBound.Alg


