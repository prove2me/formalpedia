-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_CertOL
-- name    : ClauseBound_ParityChecks_CertOL
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:05:51.421736+00:00
-- url     : https://prove2.me/theorems/75dbf81c-d191-486b-b79b-d3c9c1768c29
-- title:
--   Cert OL
-- statement:
--   Definitions and structural lemmas for Cert OL, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Theorems.Thm_Groundwork_Unary_poly

set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]
@[expose] def StDec : Prop := ∀ (α : Type) [Enc α] (q : α → Par), QU q → ∀ (oA : α → List Chk → ℤ) (oB : α → List Chk → Chk → ℕ → ℕ → ℤ) (Ls : α → List Chk)
  (cur : α → Chk) (e : α → ℕ), (PolyT fun p : α × List Chk => oA p.1 p.2) → (PolyT fun p : α × List Chk × Chk × ℕ × ℕ => oB p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) →
  PolyT Ls → PolyT cur → Unary e → PolyT fun x => (q x).decide1 (oA x) (oB x) (Ls x) (cur x) (e x)
section
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
structure CU (pad : α → U) (i : α → Idx) (n Δ : α → ℕ) (q : α → Par) : Prop where
  pad : PolyT pad
  i : PolyT i
  n : Unary n
  Δ : Unary Δ
  q : QU q
structure Given (S : Solver Idx) : Prop where
  val : StCertValS
  mark : StCertMark
  adm : StCertAdm
  dec : StDec
  poly : S.Poly
variable (G : Given S) (k : ℕ) {pad : α → U} {i : α → Idx} {n Δ : α → ℕ} {q : α → Par} (hc : CU pad i n Δ q)
include G hc
end
end ClauseBound.ParityChecks.CertOL


