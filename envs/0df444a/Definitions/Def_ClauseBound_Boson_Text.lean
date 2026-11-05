-- Prove2me | Definitions.Def_ClauseBound_Boson_Text
-- name    : ClauseBound_Boson_Text
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:18:16.547604+00:00
-- url     : https://prove2.me/theorems/1e3735a8-3d6c-4ec7-8605-7fc2a9c8adf3
-- title:
--   Text
-- statement:
--   Definitions and structural lemmas for Text, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Boson
open Finset
end ClauseBound.Boson
namespace ClauseBound.Boson
open Finset MvPolynomial
abbrev Rg : Type := MvPolynomial ℕ ℤ
@[expose] noncomputable def mon (μ : Multiset ℕ) : Rg := monomial (Multiset.toFinsupp μ) 1
@[expose] noncomputable def coef (μ : Multiset ℕ) (f : Rg) : ℤ := f.coeff (Multiset.toFinsupp μ)
@[expose] noncomputable def nabPos (k : ℤ) (f : Rg) : Rg := k • pderiv k.toNat f
@[expose] noncomputable def nord (ks : List ℤ) (f : Rg) : Rg :=
  ((ks.filter fun k => decide (k < 0)).map fun k => (X (-k).toNat : Rg)).prod * (ks.filter fun k => decide (0 < k)).foldl (fun g k => nabPos k g) f
@[expose] def wt (a : List ℕ) (ks : List ℤ) : ℤ := (List.zipWith (fun (n : ℕ) (k : ℤ) => Ring.choose (-k - 1) (n - 1)) a ks).prod
@[expose] def win (M : ℕ) : Finset ℤ := ((Icc 1 M).image fun l : ℕ => -(l : ℤ)) ∪ (Icc 1 M).image fun k : ℕ => (k : ℤ)
@[expose] def tup (M : ℕ) : ℕ → Finset (List ℤ)
  | 0 => {[]}
  | q + 1 => (win M ×ˢ tup M q).image fun p => p.1 :: p.2
namespace Text
end Text
open Text
end ClauseBound.Boson


