-- Prove2me | Definitions.Def_GeneralPieces_GenF_NormalL
-- name    : GeneralPieces_GenF_NormalL
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:27:52.593217+00:00
-- url     : https://prove2.me/theorems/4a4e8396-8282-4df3-9d9a-a131879cc557
-- title:
--   Normal L
-- statement:
--   Definitions and structural lemmas for Normal L, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
@[expose] noncomputable def cS (rd : Bool) (i : X) (r : ℤ) : S := sel rd (fun n => (bet n r : ℚ) • mo (r - n) 0) (fun n => (bet n r : ℚ) • mo 0 (r - n)) i
@[expose] def StNeq : Prop := ∀ (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ) (i : X), σ.sum ≤ E →
  MvPowerSeries.pderiv S i (normal rd E σ σ') =
    ∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i l) * normal rd E (σ.erase l) σ' +
      ∑ k ∈ σ'.toFinset, MvPowerSeries.C (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * normal rd E σ (σ'.erase k)
@[expose] noncomputable def cL (i : X) (r : ℤ) : L :=
  Sum.elim (z0 fun n => (bet n r : ℚ) • Series.W (r - n) 0) (z0 fun n => (bet n r : ℚ) • Series.W 0 (r - n)) i
end GeneralPieces.GenF


