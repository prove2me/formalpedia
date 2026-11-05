-- Prove2me | Definitions.Def_WidthK_Top_Sat
-- name    : WidthK_Top_Sat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:35:41.945543+00:00
-- url     : https://prove2.me/theorems/22425d77-c739-46b8-b5b9-2dcbd0a19ff1
-- title:
--   Sat
-- statement:
--   Definitions and structural lemmas for Sat, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/Sat.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_KSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
set_option autoImplicit false
section
namespace Groundwork.Prog.SatTopK
open Groundwork.Sparsify (leaves)
@[expose] public def decF (dec : List Bool → ℕ × Fml) (x : List Bool) : Fml := (dec x).2
@[expose] public def satMK (dec : List Bool → ℕ × Fml) (step : Fml → Option (Fml × Fml)) (root : Fml → Fml)
    (M : Stepped Fml ℤ) : Stepped (List Bool) Bool :=
  Stepped.mapIn (decF dec) (Stepped.ite hasNil (Stepped.const false)
    (Stepped.walk step root (Stepped.mapOut M posZ)))
@[expose] public def Sparsifies (k : ℕ) (ε : ℝ) (step : Fml → Option (Fml × Fml)) (root : Fml → Fml) (Dd Bl Sk : ℕ) : Prop :=
  ∀ (n : ℕ) (ψ : Fml), (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
    ((leaves step (Dd * n) (root ψ)).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves step (Dd * n) (root ψ),
      step x = none ∧ x.length ≤ Bl * n ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧
    (∀ v : ℕ × Bool → Prop, (∀ C ∈ ψ, ∃ a ∈ C, v a) ↔ ∃ x ∈ leaves step (Dd * n) (root ψ), ∀ C ∈ x, ∃ a ∈ C, v a) ∧
    ∀ i, ((Sparsify.round step)^[i] ([root ψ], [])).1.length ≤ Dd * n + 1 ∧
      ∀ x ∈ ((Sparsify.round step)^[i] ([root ψ], [])).1, x.length ≤ ψ.length * Sk ∧
        ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n
def cOf (P₁ P₂ Q A : ℕ) : ℕ := P₂ + A * P₁ ^ A + 2 * A + Q + 20
end Groundwork.Prog.SatTopK


