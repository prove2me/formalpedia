-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Count
-- name    : ClauseBound_ParityChecks_Count
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:08:37.704265+00:00
-- url     : https://prove2.me/theorems/340f60f8-681e-46a5-b13c-6d73ad2b7d57
-- title:
--   Count
-- statement:
--   Definitions and structural lemmas for Count, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks
abbrev mkQ (ψ : Fml) (nb r i₀ β : ℕ) : Par := ⟨ψ.length, nb, r, i₀, β⟩
section
variable (hE : StEvW) (hSh : StShape) {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hC : S.Correct ok) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml)
  (nb r i₀ β : ℕ) (hok : ok i) (hK : 2 ≤ S.K i) (hW : WfL k n [ψ]) (hocc : ∀ v, (occ ψ v).length ≤ Δ) (hmΔ : ψ.length ≤ Δ * n) (hnb : 2 ≤ nb)
  (hLD : n < 2 * (nb * LD Δ)) (hr : r ≤ 6 * n) (hcap : β - 1 + r ≤ 11 * n) (hFit : FitsOL S k i n Δ pad.length)
include hE hSh hC hok hK hW hocc hmΔ hnb hLD hr hcap hFit
end
end ClauseBound.ParityChecks.Count


