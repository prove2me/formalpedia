-- Prove2me | Definitions.Def_GeneralPieces_Ring_Bridge
-- name    : GeneralPieces_Ring_Bridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:27:11.614592+00:00
-- url     : https://prove2.me/theorems/4952af07-3070-4747-ad15-a1d8d2ff9e3d
-- title:
--   Bridge
-- statement:
--   Definitions and structural lemmas for Bridge, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
@[expose] noncomputable def nordQ (ks : List ℤ) (f : V) : V := (ks.filter (· < 0)).foldr nabla ((ks.filter (0 < ·)).foldr nabla f)
@[expose] def wtQ (μ : List ℕ+) (ks : List ℤ) : ℤ := (List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) μ ks).prod
end GeneralPieces.Ring
namespace GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
end GeneralPieces


