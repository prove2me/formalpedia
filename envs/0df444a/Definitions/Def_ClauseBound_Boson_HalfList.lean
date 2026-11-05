-- Prove2me | Definitions.Def_ClauseBound_Boson_HalfList
-- name    : ClauseBound_Boson_HalfList
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:21:58.708686+00:00
-- url     : https://prove2.me/theorems/90136566-cf23-4138-853e-181b8b1d7b46
-- title:
--   Half List
-- statement:
--   Definitions and structural lemmas for Half List, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfList.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Boson
open Finset
@[expose] def ApcL {lam : ℕ} (ℓ : Pieces.Bits lam → List ℕ) (h : ℕ) (s : ℤ) : Pieces.Four lam := fun x y u v =>
  ((h.factorial / zz (ℓ v : Multiset ℕ) : ℕ) : ℤ) * Qk (aFam (ℓ x)) (ℓ v) s (ℓ u : Multiset ℕ) (ℓ y : Multiset ℕ)
namespace HalfList
end HalfList
variable {lam h : ℕ}
variable {ℓ : Pieces.Bits lam → List ℕ}
end ClauseBound.Boson


