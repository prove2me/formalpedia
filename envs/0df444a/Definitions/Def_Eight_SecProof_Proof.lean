-- Prove2me | Definitions.Def_Eight_SecProof_Proof
-- name    : Eight_SecProof_Proof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:07:59.395853+00:00
-- url     : https://prove2.me/theorems/36b221ff-707c-4dfd-8ac2-f39ef11af767
-- title:
--   Sec Proof Proof
-- statement:
--   Definitions and structural lemmas for Sec Proof Proof, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Proof.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_CountKSat_Value
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace Eight
open Groundwork Groundwork.Prog Paper
@[expose] def SufficesSparse (δ M : ℝ) (S : StepMachine Formula ℤ → StepMachine (List Bool) Bool) : Prop :=
  (∀ Mc : StepMachine Formula ℤ, PolyTimeSteps Mc → PolyTimeSteps (S Mc)) ∧
  ∀ (Mc : StepMachine Formula ℤ) (A : ℕ),
    (∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) →
      ∃ (T : ℕ) (v : ℤ), Mc.Runs Φ T (A * size Φ ^ A) v ∧ (0 < v ↔ Φ.Sat) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ / (3 * M) * Φ.length)) →
    Paper.DecidesInSteps (S Mc) δ
end Eight


