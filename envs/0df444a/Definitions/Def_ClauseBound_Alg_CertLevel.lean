-- Prove2me | Definitions.Def_ClauseBound_Alg_CertLevel
-- name    : ClauseBound_Alg_CertLevel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:11:56.729535+00:00
-- url     : https://prove2.me/theorems/6cc51040-8ddb-49d8-bfce-6c46058abbf4
-- title:
--   Cert Level
-- statement:
--   Definitions and structural lemmas for Cert Level, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
section
variable (hP : P.Keeps)
include hP
end
section
variable (hP : P.Keeps)
include hP
end
def clip (M : ℕ) (st : NState) : NState := (st.1, st.2.1, (min st.2.2.1 M, st.2.2.2))
def needCut (P : PiecesF) (M : ℕ) (b : U) (Kup lam B : ℕ) (sched : List Step) : Option ℕ :=
  (sched.foldl (fun o s => cap (List.replicate (100 * (b.length + 2)) ()) none (o.map fun st => needStep P (clip M st) s))
    (cap (List.replicate (100 * (b.length + 2)) ()) none (some ((List.replicate lam (), B), (1, 1), (Kup, 0))))).bind fun st =>
      if needFin (clip M st) ≤ b.length then some (needFin (clip M st)) else none
end ClauseBound.Alg.CertLevel


