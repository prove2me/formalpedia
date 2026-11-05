-- Prove2me | Definitions.Def_ClauseBound_Inst_CertHalf
-- name    : ClauseBound_Inst_CertHalf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:45:55.729263+00:00
-- url     : https://prove2.me/theorems/f950ce22-34ab-4b8c-a5a1-9cede64e9073
-- title:
--   Cert Half
-- statement:
--   Definitions and structural lemmas for Cert Half, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
@[expose] def StTopF : Prop := ∀ (α : Type) [Enc α] (pad : α → U) (W h i : α → ℕ) (flat : α → List (List ℕ)) (μ π σ : α → List ℕ) (r : α → ℤ),
  PolyT pad → Unary W → PolyT flat → Unary h → PolyT μ → Unary i → PolyT r → PolyT π → PolyT σ →
  PolyT fun x => topF (pad x) (W x) (flat x) (h x) (μ x) (i x) (r x) (π x) (σ x)
@[expose] def StBotF : Prop := ∀ (α : Type) [Enc α] (pad : α → U) (W h : α → ℕ) (flat : α → List (List ℕ)) (μ π σ : α → List ℕ) (r : α → ℤ),
  PolyT pad → Unary W → PolyT flat → Unary h → PolyT μ → PolyT r → PolyT π → PolyT σ →
  PolyT fun x => botF (pad x) (W x) (flat x) (h x) (μ x) (r x) (π x) (σ x)
def bodyT (pad : U) (tr top : Bool) (h : ℕ) (s : ℤ) (T : PT) (a b : List Bool) (j : ℕ) (τ : List ℕ) : ℤ :=
  bif top then
    (bif tr then topF pad (4 * h) T.flatten h (encF T h a) j (s - h + j) (encF T h b) τ
     else topF pad (4 * h) T.flatten h (encF T h a) j (s - h + j) τ (encF T h b))
  else
    (bif tr then botF pad (4 * h) T.flatten h (encF T h b) (h - s - j) τ (encF T h a)
     else botF pad (4 * h) T.flatten h (encF T h b) (h - s - j) (encF T h a) τ)
end ClauseBound.Inst.Half.Cert


