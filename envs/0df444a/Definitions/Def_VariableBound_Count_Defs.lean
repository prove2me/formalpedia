-- Prove2me | Definitions.Def_VariableBound_Count_Defs
-- name    : VariableBound_Count_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:08:20.43641+00:00
-- url     : https://prove2.me/theorems/0d9090ed-2896-41c9-b5a3-38fa10c7e717
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_Params_Defs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace VariableBound
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def countD (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml) : ℕ :=
  let m := ψ.length
  let nb := nbD n Δ
  let β := beta n m nb
  let rb := rbD β
  let M := Mb β rb
  bif decide (m ≤ nb) then (evF S k pad i n Δ nb M (ψ, [])).toNat
  else (evF S k pad i n Δ nb M
    (ψ, searchD pad (fun L => evX S k pad i n Δ nb M β (ψ, L)) (Fld.famD m (Nat.log 2 nb)) m nb β rb (tbD m nb rb))).toNat
structure FitsD (k : ℕ) (i : Idx) (n Δ : ℕ) (F : ℕ) : Prop where
  net : 2 ^ needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) ≤ F
  prof : nPrMax (S.K i) n Δ ≤ F
  lists : 8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8 ≤ F
end
def StCountD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml),
  ok i → 2 ≤ S.K i → WfL k n [ψ] → (∀ v, (occ ψ v).length ≤ Δ) → ψ.length ≤ Δ * n → 2 ≤ Δ → 29 * LD Δ + 19 ≤ n → FitsD S k i n Δ pad.length →
  countD S k pad i n Δ ψ = nSat n ψ
def StCertCountD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly →
  PolyT fun x : U × U × Idx × (U × U) × Fml => countD S x.1.length x.2.1 x.2.2.1 x.2.2.2.1.1.length x.2.2.2.1.2.length x.2.2.2.2
end VariableBound


