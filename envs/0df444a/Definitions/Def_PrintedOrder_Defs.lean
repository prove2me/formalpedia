-- Prove2me | Definitions.Def_PrintedOrder_Defs
-- name    : PrintedOrder_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:36:21.533889+00:00
-- url     : https://prove2.me/theorems/15f4726d-9db8-46d4-a47e-7de17ea3bf72
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitSat_Defs
import Definitions.Def_ThmCount_Defs
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Paper Eight.ViaGrouping SplitCount SplitSat
def Holds (a : ℕ → Bool) (ψ : Fml) : Prop := ∀ C ∈ ψ, ∃ t ∈ C, a t.1 = t.2
def StAddUp : Prop := ∀ (n : ℕ) (ψ : Fml) (L : List Fml), (L.Pairwise fun y z => ∀ a : ℕ → Bool, ¬(Holds a y ∧ Holds a z)) → (∀ a : ℕ → Bool, Holds a ψ ↔ ∃ y ∈ L, Holds a y) →
  cntN n ψ = (L.map fun y => cntN n y).sum
def StCovered : Prop := ∀ (θ : ℕ → ℕ) (k d : ℕ) (x : CNode) (a : ℕ → Bool), Holds a (leafF x) ↔ ∃ y ∈ leaves (stepC θ k) d x, Holds a (leafF y)
def StRootSame : Prop := ∀ (u : List Unit) (ψ : Fml) (a : ℕ → Bool), Holds a (leafF (rootPlain (u, ψ)).2) ↔ Holds a ψ
def StTreeAddsUp : Prop := ∀ (θ : ℕ → ℕ) (k d n : ℕ) (ψ : Fml),
  cntN n ψ = ((leaves (stepPlain (stepC θ k)) d (rootPlain (List.replicate n (), ψ))).map fun x => cntN n (leafF x.2)).sum
abbrev StStepAdds : Prop := CountKSat.StStepCount
def BoundsPlain (k : ℕ) (ε : ℝ) (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ) : Prop :=
  ∀ (n : ℕ) (ψ : Fml), (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
    ((leaves (stepPlain step) (Dd * n) (rootPlain (List.replicate n (), ψ))).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves (stepPlain step) (Dd * n) (rootPlain (List.replicate n (), ψ)), stepPlain step x = none ∧ x.1 = List.replicate n () ∧ (leafF x.2).length ≤ Bl * n ∧
      ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) ∧
    ∀ i, ((round (stepPlain step))^[i] ([rootPlain (List.replicate n (), ψ)], [])).1.length ≤ Dd * n + 1 ∧
      ∀ x ∈ ((round (stepPlain step))^[i] ([rootPlain (List.replicate n (), ψ)], [])).1, x.1 = List.replicate n () ∧ (leafF x.2).length ≤ (ψ.length + n) * Sk ∧
        ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n
def StBounds : Prop := ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∃ τ Dd Bl Sk : ℕ, BoundsPlain k ε (stepC (WidthK.theta τ) k) Dd Bl Sk
abbrev CountingAgain : Prop := SplitCount.ThreeSatStatement
def StThreeSatFamily : Prop := ∃ Ds : ℝ → StepMachine (List Unit × Fml) Bool, Sat3SubexpBy Ds ∧ ∀ δ₃ : ℝ, 0 < δ₃ → ∃ ℓ τ : ℕ, Ds δ₃ = core3 ℓ τ
def StHosted : Prop := ∀ Ds : ℝ → StepMachine (List Unit × Fml) Bool, Sat3SubexpBy Ds → ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ →
  ∃ (τ : ℕ) (δ₃ : ℝ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), 0 < δ₃ ∧ (∀ i, Finite (M.tm.Γ i)) ∧
    PolyTimeSteps (REDUCE k τ (Ds δ₃)) ∧ Decides (REDUCE k τ (Ds δ₃)) k δ c ∧ Simulates M (REDUCE k τ (Ds δ₃)) q ∧ SatK.DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
abbrev EthAndSethAgain : Prop := SplitSat.ThreeSatStatement
abbrev CountRateFromBoundInN : Prop := PaperSentences.CountRate (1 / 20)
end PrintedOrder


