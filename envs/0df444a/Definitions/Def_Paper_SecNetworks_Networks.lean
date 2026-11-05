-- Prove2me | Definitions.Def_Paper_SecNetworks_Networks
-- name    : Paper_SecNetworks_Networks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:54:33.259458+00:00
-- url     : https://prove2.me/theorems/64846eef-2f93-44fc-8554-304e658feda7
-- title:
--   Sec Networks Networks
-- statement:
--   Definitions and structural lemmas for Sec Networks Networks, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Networks.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Model
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
namespace Paper
open Groundwork Groundwork.Prog Finset
abbrev Network (J σ τ : Type*) := Groundwork.Network J σ τ
abbrev NetworkProcedures (C : Type) := PNet C
structure IsNetwork {C : Type} {g : ℕ} (Np : NetworkProcedures C) (c : C) (N : Network (Fin g) (List Bool) (List Bool))
    (P B τ S : ℕ) : Prop where
  sized : N.Sized P B
  presented : Np.Presents c N τ S
abbrev Tables (K : ℕ) := Inst (Fin K) (List Bool)
abbrev cliqueValue {K : ℕ} (lam : ℕ) (W : Tables K) : ℤ := Inst.ZW lam [] W
abbrev CliqueAlgorithm := Evaluator
abbrev CliqueAlgorithm.Within (E : CliqueAlgorithm) (K : ℕ) (e : ℝ) : Prop := E.Correct K e
abbrev CliqueAlgorithm.PolyTimeSteps (E : CliqueAlgorithm) : Prop := E.Keeps
def Achievable (K : ℕ) (e : ℝ) : Prop := ∃ E : CliqueAlgorithm, E.PolyTimeSteps ∧ E.Within K e
noncomputable def eStar : ℝ := sInf {e : ℝ | 0 ≤ e ∧ ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e}
section Grouping
variable {g K : ℕ}
abbrev groupedLength (K g U P : ℕ) : ℕ := Colouring.beta K g U P
end Grouping
section Algorithm
open NetE Stepped
variable {C : Type} {g K : ℕ}
abbrev grouping (hK : 0 < K) (x : ℕ) : Fin g → Fin K := chi hK x
abbrev groupedTables (Np : NetworkProcedures C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (hK0 : 0 < K) (x L : ℕ) :
    Tables K :=
  (N.merge (grouping hK0 x) [] []).toInst (mD K g Np c x L) (mdec K g Np c x)
end Algorithm
end Paper


