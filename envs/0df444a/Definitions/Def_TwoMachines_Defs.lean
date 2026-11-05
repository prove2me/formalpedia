-- Prove2me | Definitions.Def_TwoMachines_Defs
-- name    : TwoMachines_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:43:56.723095+00:00
-- url     : https://prove2.me/theorems/f4f86b24-78b8-46f6-90d1-97a0853d767a
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_Wrap_Coding
import Definitions.Def_Wrap_Sim
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
import Theorems.Thm_CircuitLowerBound_Tab_Enc_step
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace TwoMachines
open Turing Groundwork Wrap
section
variable {M₁ M₂ : TM2ComputableAux Bool Bool}
def alt (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) : Stepped (List Bool) (List Bool) where
  σ := Rep × Rep
  init x := (K₁.init (pre₁ x), K₂.init (pre₂ x))
  step r := (K₁.step r.1, K₂.step r.2)
  out r := match K₁.out r.1 with
    | some y => some (post₁ y)
    | none => (K₂.out r.2).map post₂
def choose (K₁ : Coding M₁) (K₂ : Coding M₂) (test : List Bool → Bool) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) : Stepped (List Bool) (List Bool) :=
  Stepped.ite test (sim K₁ pre₁ post₁) (sim K₂ pre₂ post₂)
end
def start (M : TM2ComputableAux Bool Bool) (x : List Bool) : M.tm.Cfg := initList M.tm (x.map M.inputAlphabet.invFun)
def Hosts (X : Stepped (List Bool) (List Bool)) (N : TM2ComputableAux Bool Bool) (q : ℕ) : Prop :=
  ∀ (x : List Bool) (T S : ℕ) (w : List Bool), X.Runs x T S w → Outputs N x w (q * (T + 1) * (x.length + S + 1) ^ q)
def Alternates (M₁ M₂ : TM2ComputableAux Bool Bool) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) (q : ℕ) : Prop :=
  ∀ (x y₁ y₂ : List Bool) (t₁ t₂ : ℕ), Outputs M₁ (pre₁ x) y₁ t₁ → Outputs M₂ (pre₂ x) y₂ t₂ → post₁ y₁ = post₂ y₂ →
    Outputs N x (post₁ y₁) (q * (min t₁ t₂ + x.length + 1) ^ q)
def Chooses (M₁ M₂ : TM2ComputableAux Bool Bool) (test : List Bool → Bool) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) (q : ℕ) : Prop :=
  ∀ (x y : List Bool) (t : ℕ),
    (test x = true → Outputs M₁ (pre₁ x) y t → Outputs N x (post₁ y) (q * (t + x.length + 1) ^ q)) ∧
    (test x = false → Outputs M₂ (pre₂ x) y t → Outputs N x (post₂ y) (q * (t + x.length + 1) ^ q))
def EveryTwoMachinesCanBeAlternated : Prop :=
  ∀ M₁ M₂ : TM2ComputableAux Bool Bool, (∀ i, Finite (M₁.tm.Γ i)) → (∀ i, Finite (M₂.tm.Γ i)) →
    ∀ pre₁ pre₂ post₁ post₂ : List Bool → List Bool, PolyT pre₁ → PolyT pre₂ → PolyT post₁ → PolyT post₂ →
      ∃ (K₁ : Coding M₁) (K₂ : Coding M₂) (N : TM2ComputableAux Bool Bool) (q₀ q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
        Hosts (alt K₁ K₂ pre₁ pre₂ post₁ post₂) N q₀ ∧ Alternates M₁ M₂ pre₁ pre₂ post₁ post₂ N q
def EveryTwoMachinesCanBeChosenBetween : Prop :=
  ∀ M₁ M₂ : TM2ComputableAux Bool Bool, (∀ i, Finite (M₁.tm.Γ i)) → (∀ i, Finite (M₂.tm.Γ i)) →
    ∀ (test : List Bool → Bool) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool), PolyT test → PolyT pre₁ → PolyT pre₂ → PolyT post₁ → PolyT post₂ →
      ∃ (K₁ : Coding M₁) (K₂ : Coding M₂) (N : TM2ComputableAux Bool Bool) (q₀ q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
        Hosts (choose K₁ K₂ test pre₁ pre₂ post₁ post₂) N q₀ ∧ Chooses M₁ M₂ test pre₁ pre₂ post₁ post₂ N q
end TwoMachines


