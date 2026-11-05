-- Prove2me | Definitions.Def_GeneralPieces_Ring_OpFacts
-- name    : GeneralPieces_Ring_OpFacts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:25:33.922698+00:00
-- url     : https://prove2.me/theorems/ee0b9532-b460-46c8-84fa-06da5405cd9f
-- title:
--   Op Facts
-- statement:
--   Definitions and structural lemmas for Op Facts, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_GeneralPieces_Ring_nabla_add
import Theorems.Thm_GeneralPieces_Ring_nabla_smul
import Theorems.Thm_GeneralPieces_Ring_nordQ_smul
import Theorems.Thm_GeneralPieces_Ring_term_eq

set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
@[expose] noncomputable def nablaL (k : ℤ) : V →ₗ[ℚ] V where
  toFun := nabla k
  map_add' := nabla_add k
  map_smul' := nabla_smul k
theorem foldr_nabla_add (l : List ℤ) (f g : V) : l.foldr nabla (f + g) = l.foldr nabla f + l.foldr nabla g := by
  induction l with
  | nil => rfl
  | cons k l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, nabla_add]
theorem nordQ_add (ks : List ℤ) (f g : V) : nordQ ks (f + g) = nordQ ks f + nordQ ks g := by
  unfold nordQ
  rw [foldr_nabla_add, foldr_nabla_add]
@[expose] noncomputable def termL (μ : List ℕ+) (ks : List ℤ) : V →ₗ[ℚ] V where
  toFun := term μ ks
  map_add' := fun f g => by rw [term_eq, term_eq, term_eq, nordQ_add, smul_add]
  map_smul' := fun q f => by rw [term_eq, term_eq, nordQ_smul, smul_comm]; rfl
@[expose] def Bd (f : V) (E : ℤ) : Prop := ∀ μ, coef μ f ≠ 0 → (wt μ : ℤ) ≤ E
@[expose] noncomputable def opWin (μ : List ℕ+) (M : ℕ) (r : ℤ) (f : V) : V := ∑ ks ∈ ClauseBound.Boson.tup M μ.length with ks.sum = -r, term μ ks f
end GeneralPieces.Ring
namespace GeneralPieces
open AppHalfPieces GeneralPieces.Ring
end GeneralPieces


