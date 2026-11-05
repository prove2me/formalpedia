-- Prove2me | Definitions.Def_ClauseBound_Inst_HalfIfc
-- name    : ClauseBound_Inst_HalfIfc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:41:48.496259+00:00
-- url     : https://prove2.me/theorems/f0ddc6b6-1001-448d-9414-0bbabb8f2c60
-- title:
--   Half Ifc
-- statement:
--   Definitions and structural lemmas for Half Ifc, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfIfc.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Boson_HalfList
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Finset
def ell {lam : ℕ} (h : ℕ) (x : Pieces.Bits lam) : List ℕ := encF (allTab (4 * h)) h (bitsOf x)
def valK (tr top : Bool) (h : ℕ) (s : ℤ) (α β : List ℕ) (p : ℕ × List ℕ) : ℤ :=
  bif top then
    (bif tr then ClauseBound.Boson.topK α h p.1 (s - h + p.1) (β : Multiset ℕ) (p.2 : Multiset ℕ)
     else ClauseBound.Boson.topK α h p.1 (s - h + p.1) (p.2 : Multiset ℕ) (β : Multiset ℕ))
  else
    (bif tr then ClauseBound.Boson.botK β h (h - s - p.1) (p.2 : Multiset ℕ) (α : Multiset ℕ)
     else ClauseBound.Boson.botK β h (h - s - p.1) (α : Multiset ℕ) (p.2 : Multiset ℕ))
def StWords : Prop := ∀ (β : Type) (L : List β) (c : ℕ) (f g : β → ℤ), L.length ≤ 2 ^ c →
  ∑ θ ∈ words c, (L[ofWord θ]?).elim 0 f * (L[ofWord θ]?).elim 0 g = (L.map fun b => f b * g b).sum
def StLabs : Prop := ∀ (tr : Bool) (h : ℕ) (s : ℤ), |s| ≤ 2 * (h : ℤ) →
  (labs (allTab (4 * h)) tr h s).length = (bif tr then ClauseBound.Part.Rcol h s else ClauseBound.Part.Rrow h s) ∧
  (∀ G : ℕ → Multiset ℕ → ℤ, ((labs (allTab (4 * h)) tr h s).map fun p => G p.1 (p.2 : Multiset ℕ)).sum =
    ∑ j ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (wOf tr h s j), G j τ) ∧
  ∀ p ∈ labs (allTab (4 * h)) tr h s, p.2 ∈ (allTab (4 * h)).flatten ∧ p.1 ≤ 2 * h
def StEnc : Prop := ∀ (lam h : ℕ), 1 ≤ h → 2 ^ lam ≤ Partitions.p h →
  (∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell h x) ∧ (ell h x).sum = h ∧ ell h x ∈ (allTab (4 * h)).flatten) ∧
  ∀ x v : Pieces.Bits lam, (ell h x : Multiset ℕ) = ell h v → x = v
def StVal : Prop := ∀ (c₀ lam : ℕ) (pad : U), 1 ≤ lam → ClauseBound.Part.hOf lam ≤ c₀ * lam ^ 2 → padLen (ClauseBound.Part.hOf lam) ≤ pad.length →
  ∀ (tr top : Bool) (h' i : ℕ) (a b : Pieces.Bits lam) (θ : List Bool),
    partH c₀ top ((pad, tr), (h', i), (bitsOf a, bitsOf b, θ)) =
      ((labs (allTab (4 * ClauseBound.Part.hOf lam)) tr (ClauseBound.Part.hOf lam) (sOf (ClauseBound.Part.hOf lam) i))[ofWord θ]?).elim 0
        (valK tr top (ClauseBound.Part.hOf lam) (sOf (ClauseBound.Part.hOf lam) i) (ell (ClauseBound.Part.hOf lam) a) (ell (ClauseBound.Part.hOf lam) b))
structure Cst (c₀ c lam : ℕ) : Prop where
  h_le : ClauseBound.Part.hOf lam ≤ c₀ * lam ^ 2
  cnt : 4 * ClauseBound.Part.hOf lam + 1 ≤ (2 * lam) ^ c
  fact : (ClauseBound.Part.hOf lam).factorial < 2 ^ (2 * lam) ^ c
  bits : 40 * (ClauseBound.Part.hOf lam + 1) ^ 2 + Nat.clog 2 (∑ E ∈ range (4 * ClauseBound.Part.hOf lam + 1), Partitions.p E) ≤ (2 * lam) ^ c
  pad : 2 ^ 10 * (ClauseBound.Part.hOf lam + 2) ^ 4 * ((∑ E ∈ range (4 * ClauseBound.Part.hOf lam + 1), Partitions.p E) + 1) ^ 2 ≤ 2 ^ (c * lam)
  caps : ∀ s : ℤ, |s| ≤ 2 * (ClauseBound.Part.hOf lam : ℤ) →
    Nat.clog 2 (ClauseBound.Part.Rrow (ClauseBound.Part.hOf lam) s) ≤ 2 * c * lam ∧ Nat.clog 2 (ClauseBound.Part.Rcol (ClauseBound.Part.hOf lam) s) ≤ 2 * c * lam ∧
      ((Nat.clog 2 (ClauseBound.Part.Rrow (ClauseBound.Part.hOf lam) s) + Nat.clog 2 (ClauseBound.Part.Rcol (ClauseBound.Part.hOf lam) s) : ℕ) : ℝ) ≤
        4 * (1 / Real.sqrt 2) * lam + c * Real.logb 2 (2 * lam)
def StFact : Prop := ∀ (c₀ c lam : ℕ) (pad : U), 1 ≤ lam → Cst c₀ c lam → 2 ^ (c * lam) ≤ pad.length → ∀ (h' i : ℕ), i < 4 * ClauseBound.Part.hOf lam + 1 →
  ∀ x y u v : Pieces.Bits lam,
    ClauseBound.Boson.ApcL (ell (ClauseBound.Part.hOf lam)) (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) x y u v =
      ∑ θ ∈ words ((halfF c₀ c).cap false h' lam i),
        (halfF c₀ c).top ((pad, false), (h', i), (bitsOf x, bitsOf y, θ)) * (halfF c₀ c).bot ((pad, false), (h', i), (bitsOf u, bitsOf v, θ)) ∧
    ClauseBound.Boson.ApcL (ell (ClauseBound.Part.hOf lam)) (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) x y u v =
      ∑ θ ∈ words ((halfF c₀ c).cap true h' lam i),
        (halfF c₀ c).top ((pad, true), (h', i), (bitsOf x, bitsOf u, θ)) * (halfF c₀ c).bot ((pad, true), (h', i), (bitsOf y, bitsOf v, θ))
def StSpec : Prop := ∀ (c₀ c lam h' : ℕ), 1 ≤ lam → Cst c₀ c lam → (halfF c₀ c).Spec h' lam
end ClauseBound.Inst.Half


