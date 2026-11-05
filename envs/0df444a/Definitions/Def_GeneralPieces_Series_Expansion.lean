-- Prove2me | Definitions.Def_GeneralPieces_Series_Expansion
-- name    : GeneralPieces_Series_Expansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:22:56.444848+00:00
-- url     : https://prove2.me/theorems/42bb9071-58b8-4155-a479-90b8af3b8f1e
-- title:
--   Expansion
-- statement:
--   Definitions and structural lemmas for Expansion, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Expansion.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Defs
set_option autoImplicit false
section
section
namespace GeneralPieces.Series
open ClauseBound.Boson
noncomputable def fP (a b : List ℕ) (π σ : Multiset ℕ) : Lp :=
  diag (-((a.sum : ℤ) + b.sum)) (fun j => (mul2 a (-j - b.sum) b (j + b.sum) π σ : ℚ)) (-(σ.sum : ℤ) - b.sum)
noncomputable def fM (a b : List ℕ) (π σ : Multiset ℕ) : Lm :=
  diag (-((a.sum : ℤ) + b.sum)) (fun j => (mul2 b (-j - a.sum) a (j + a.sum) π σ : ℚ)) (-(σ.sum : ℤ) - a.sum)
structure Expansion (a b : List ℕ) (G : ℚ) (π σ : Multiset ℕ) where
  /-- The terms (Γ_c, N_c, n_c). -/
  terms : List (ℚ × ℕ × L)
  le : ∀ c ∈ terms, c.2.1 ≤ a.sum + b.sum
  plus : fP a b π σ = (terms.map fun c => c.1 • (epsP ^ c.2.1 * toP c.2.2)).sum
  minus : fM a b π σ = (terms.map fun c => c.1 • (epsM ^ c.2.1 * toM c.2.2)).sum
  top : ∀ c ∈ terms, c.2.1 = a.sum + b.sum → c.2.2 = if π = σ then 1 else 0
  tot : ((terms.filter fun c => c.2.1 = a.sum + b.sum).map fun c => c.1).sum = G
  vac : π = 0 → σ = 0 → ∀ c ∈ terms, c.2.1 < a.sum + b.sum → c.2.2 = 0
def StExpansion : Prop := ∀ a b : List ℕ, Pos a → Pos b → ∃ G : ℚ, ∀ π σ : Multiset ℕ, 0 ∉ π → 0 ∉ σ → Nonempty (Expansion a b G π σ)
end GeneralPieces.Series


