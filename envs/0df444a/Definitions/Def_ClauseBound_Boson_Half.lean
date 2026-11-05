-- Prove2me | Definitions.Def_ClauseBound_Boson_Half
-- name    : ClauseBound_Boson_Half
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:21:13.616302+00:00
-- url     : https://prove2.me/theorems/36b4abb9-e6d4-4387-97c1-9269c6a80f25
-- title:
--   Half
-- statement:
--   Definitions and structural lemmas for Half, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Half.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_HalfSum
import Definitions.Def_ClauseBound_Rec_Number
import Theorems.Thm_ClauseBound_Boson_HalfSum_coe_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_pos_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_sum_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_zero_notMem_parts

set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Boson
open Finset
@[expose] def topK (μx : List ℕ) (h i : ℕ) (r : ℤ) : Ker := fun π σ =>
  (-1) ^ i * ((aFam μx).map fun c => c.1 * ((c.2.sum + h).choose i : ℤ) * op c.2 r π σ).sum
@[expose] def botK (μv : List ℕ) (h : ℕ) (r : ℤ) : Ker := fun π σ => ((h.factorial / zz (μv : Multiset ℕ) : ℕ) : ℤ) * op μv r π σ
namespace Half
open HalfSum (coe_lst sum_lst pos_lst zero_notMem_parts)
@[expose] def fL (A : FA) (h i : ℕ) (g : List ℕ → ℤ) : ℤ :=
  (-1) ^ i * (A.map fun c => c.1 * ((c.2.sum + h).choose i : ℤ) * g c.2).sum
@[expose] def eL (h : ℕ) : ℕ := h + (2 * h + (16 * h + 1) * h)
@[expose] def eR (h : ℕ) : ℕ := h * h + (16 * h + 1) * h
end Half
@[expose] def big (h : ℕ) : ℕ := 40 * (h + 1) ^ 2 + Nat.clog 2 (∑ E ∈ range (4 * h + 1), Partitions.p E)
namespace Half
end Half
variable {lam h : ℕ} (enc : Pieces.Bits lam → Nat.Partition h)
namespace Half
end Half
end ClauseBound.Boson


