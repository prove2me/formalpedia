-- Prove2me | Definitions.Def_GeneralPieces_Ring_LemmaQ
-- name    : GeneralPieces_Ring_LemmaQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:28:20.184629+00:00
-- url     : https://prove2.me/theorems/9ce76740-0315-48c1-b020-0bfb720dcc0a
-- title:
--   Lemma Q
-- statement:
--   Definitions and structural lemmas for Lemma Q, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
@[expose] def StMatA : Prop := ∀ (A : ClauseBound.Boson.FA) (b : List ℕ), A.Ok b.sum → ClauseBound.Boson.Pos b → 1 ≤ b.sum → ∀ (s : ℤ) (π σ : Multiset ℕ), 0 ∉ π → 0 ∉ σ →
  ClauseBound.Boson.Qk A b s π σ = ClauseBound.Boson.Qk' A b s π σ
@[expose] def StMatB : Prop := ∀ (A : ClauseBound.Boson.FA) (b : List ℕ), A.Ok b.sum → ClauseBound.Boson.Pos b → 1 ≤ b.sum → ∀ (s : ℤ) (π σ : Multiset ℕ), 0 ∉ π → 0 ∉ σ →
  (σ.sum : ℤ) + b.sum < |s| → ClauseBound.Boson.Qk A b s π σ = 0
@[expose] def StMatC : Prop := ∀ (A : ClauseBound.Boson.FA) (b : List ℕ), A.Ok b.sum → ClauseBound.Boson.Pos b → 1 ≤ b.sum → ∀ (π σ : Multiset ℕ), 0 ∉ π → 0 ∉ σ →
  ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), ClauseBound.Boson.Qk A b s π σ =
    if π = σ then (A.map fun c => c.1 * ClauseBound.Boson.op c.2 (-(b.sum : ℤ)) 0 (b : Multiset ℕ)).sum else 0
@[expose] def ptnsLe (h : ℕ) : Finset Ptn := (range (h + 1)).biUnion ptns
structure Tri (T : V → V → V → V) : Prop where
  add₁ : ∀ a a' b f, T (a + a') b f = T a b f + T a' b f
  smul₁ : ∀ (q : ℚ) a b f, T (q • a) b f = q • T a b f
  add₂ : ∀ a b b' f, T a (b + b') f = T a b f + T a b' f
  smul₂ : ∀ (q : ℚ) a b f, T a (q • b) f = q • T a b f
  add₃ : ∀ a b f f', T a b (f + f') = T a b f + T a b f'
  smul₃ : ∀ (q : ℚ) a b f, T a b (q • f) = q • T a b f
namespace Tri
variable {T T' : V → V → V → V}
theorem sum {ι : Type} (s : Finset ι) {F : ι → V → V → V → V} (hF : ∀ i, Tri (F i)) : Tri fun a b f => ∑ i ∈ s, F i a b f where
  add₁ a a' b f := by simp only [(hF _).add₁, sum_add_distrib]
  smul₁ q a b f := by simp only [(hF _).smul₁, smul_sum]
  add₂ a b b' f := by simp only [(hF _).add₂, sum_add_distrib]
  smul₂ q a b f := by simp only [(hF _).smul₂, smul_sum]
  add₃ a b f f' := by simp only [(hF _).add₃, sum_add_distrib]
  smul₃ q a b f := by simp only [(hF _).smul₃, smul_sum]
end Tri
@[expose] noncomputable def lst (μ : Ptn) : List ℕ := toL μ.toList
end GeneralPieces.LemQ
namespace GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
end GeneralPieces


