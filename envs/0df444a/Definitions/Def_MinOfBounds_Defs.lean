-- Prove2me | Definitions.Def_MinOfBounds_Defs
-- name    : MinOfBounds_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:35:01.173417+00:00
-- url     : https://prove2.me/theorems/d95681cb-1b5e-401e-b2b5-e20f33bd7024
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_TwoMachines_Defs
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)
noncomputable def timeM (C k m : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * expM k m)⌋₊
def MeetsBoundInM (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → SatM.AllOccur φ → CountsWithin M k φ (timeM C k φ.length + C * (SatM.enc k φ).length ^ C)
def BoundInMSuffices : Prop :=
  ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), SatM.CountsTM M (SatM.bound (SatM.rPow (1 / 2)) C) → ∃ C' : ℕ, MeetsBoundInM M C'
def MeetsMinBound (N : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ numOcc φ →
    CountsOccWithinC N k φ (timeCor C k φ.length (numOcc φ) + C * (encC k φ).length ^ C)
def DecidesWithinMinBound (N : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ numOcc φ →
    DecidesWithinC N k φ (timeCor C k φ.length (numOcc φ) + C * (encC k φ).length ^ C)
def PropositionsUnfold : Prop :=
  (AppRunningTime.BoundInM ↔ ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ SatM.CountsTM M (SatM.bound (SatM.rPow (1 / 2)) C)) ∧
  (ThmVariablesB ↔ ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ThmVariablesBFor M C) ∧
  (CorMinCompact ↔ ∃ (N : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧ MeetsMinBound N C)
def renamedCode (k : ℕ) {V : ℕ} (φ : CNF V) : List Bool := VariableBound.Rename.encN (List.replicate k ()) (VariableBound.Rename.renF (Groundwork.Decode.toN φ))
def RenamedCodeIsTheCodeOfARenaming : Prop :=
  ∀ (k V : ℕ) (φ : CNF V), ∃ φ' : CNF (numOcc φ),
    renamedCode k φ = SatM.enc k φ' ∧
    Groundwork.Decode.toN φ' = VariableBound.Rename.renL (VariableBound.Rename.occL (Groundwork.Decode.toN φ)) (Groundwork.Decode.toN φ) ∧
    (VariableBound.Rename.occL (Groundwork.Decode.toN φ)).Nodup ∧ (∀ v : ℕ, v ∈ VariableBound.Rename.occL (Groundwork.Decode.toN φ) ↔ ∃ i : Fin V, i.val = v ∧ Occurs φ i) ∧
    φ'.length = φ.length ∧ (SatK.IsKCNF k φ → SatK.IsKCNF k φ') ∧ SatM.AllOccur φ' ∧ SatK.numSat φ' = numSatOcc φ
def RenamesTheVariablesThatOccur (pre : List Bool → List Bool) : Prop :=
  ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → pre (encC k φ) = renamedCode k φ
def RenamingFrontEndExists : Prop := ∃ pre : List Bool → List Bool, PolyT pre ∧ RenamesTheVariablesThatOccur pre
def BothComputeTheSameNumber : Prop :=
  ∀ (M₁ : TM2ComputableAux Bool Bool) (C₁ : ℕ), MeetsBoundInM M₁ C₁ → ∀ (M₂ : TM2ComputableAux Bool Bool) (C₂ : ℕ), ThmVariablesBFor M₂ C₂ →
    ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ numOcc φ →
      Outputs M₁ (renamedCode k φ) (SatK.binary (numOcc φ) (numSatOcc φ)) (timeM C₁ k φ.length + C₁ * (renamedCode k φ).length ^ C₁) ∧
      Outputs M₂ (renamedCode k φ) (SatK.binary (numOcc φ) (numSatOcc φ)) (timeN C₂ k (numOcc φ))
def RenamedCodeIsPolynomial : Prop :=
  ∃ a : ℕ, ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → (renamedCode k φ).length ≤ a * (encC k φ).length ^ a
def OverheadGoesIntoC : Prop :=
  ∀ C₁ C₂ q a : ℕ, ∃ C : ℕ, ∀ k m n L L₁ : ℕ, 1 ≤ k → 2 ≤ m → 4 ≤ n → 1 ≤ L → L₁ ≤ a * L ^ a →
    q * (min (timeM C₁ k m + C₁ * L₁ ^ C₁) (timeN C₂ k n) + L + 1) ^ q ≤ timeCor C k m n + C * L ^ C
def EveryAlternationMeetsMinBound : Prop :=
  ∀ pre : List Bool → List Bool, RenamesTheVariablesThatOccur pre →
    ∀ (M₁ : TM2ComputableAux Bool Bool) (C₁ : ℕ), MeetsBoundInM M₁ C₁ → ∀ (M₂ : TM2ComputableAux Bool Bool) (C₂ : ℕ), ThmVariablesBFor M₂ C₂ →
      ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Alternates M₁ M₂ pre pre id id N q → ∃ C : ℕ, MeetsMinBound N C
def EveryAlternationDecidesWithinMinBound : Prop :=
  ∀ pre : List Bool → List Bool, RenamesTheVariablesThatOccur pre →
    ∀ (M₁ : TM2ComputableAux Bool Bool) (C₁ : ℕ), MeetsBoundInM M₁ C₁ → ∀ (M₂ : TM2ComputableAux Bool Bool) (C₂ : ℕ), ThmVariablesBFor M₂ C₂ →
      ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Alternates M₁ M₂ pre pre Wrap.someBit Wrap.someBit N q → ∃ C : ℕ, DecidesWithinMinBound N C
def MinBoundFromTheTwoTheorems : Prop :=
  ∀ (M₁ : TM2ComputableAux Bool Bool) (C₁ : ℕ), (∀ i, Finite (M₁.tm.Γ i)) → MeetsBoundInM M₁ C₁ →
    ∀ (M₂ : TM2ComputableAux Bool Bool) (C₂ : ℕ), (∀ i, Finite (M₂.tm.Γ i)) → ThmVariablesBFor M₂ C₂ →
      (∃ (pre : List Bool → List Bool) (K₁ : Coding M₁) (K₂ : Coding M₂) (N : TM2ComputableAux Bool Bool) (q₀ q : ℕ), PolyT pre ∧ RenamesTheVariablesThatOccur pre ∧ (∀ i, Finite (N.tm.Γ i)) ∧
          Hosts (alt K₁ K₂ pre pre id id) N q₀ ∧ Alternates M₁ M₂ pre pre id id N q) ∧
        ∀ pre : List Bool → List Bool, RenamesTheVariablesThatOccur pre → ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Alternates M₁ M₂ pre pre id id N q → ∃ C : ℕ, MeetsMinBound N C
def DecidingFromTheTwoTheorems : Prop :=
  ∀ (M₁ : TM2ComputableAux Bool Bool) (C₁ : ℕ), (∀ i, Finite (M₁.tm.Γ i)) → MeetsBoundInM M₁ C₁ →
    ∀ (M₂ : TM2ComputableAux Bool Bool) (C₂ : ℕ), (∀ i, Finite (M₂.tm.Γ i)) → ThmVariablesBFor M₂ C₂ →
      (∃ (pre : List Bool → List Bool) (K₁ : Coding M₁) (K₂ : Coding M₂) (N : TM2ComputableAux Bool Bool) (q₀ q : ℕ), PolyT pre ∧ RenamesTheVariablesThatOccur pre ∧ (∀ i, Finite (N.tm.Γ i)) ∧
          Hosts (alt K₁ K₂ pre pre Wrap.someBit Wrap.someBit) N q₀ ∧ Alternates M₁ M₂ pre pre Wrap.someBit Wrap.someBit N q) ∧
        ∀ pre : List Bool → List Bool, RenamesTheVariablesThatOccur pre → ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ),
          Alternates M₁ M₂ pre pre Wrap.someBit Wrap.someBit N q → ∃ C : ℕ, DecidesWithinMinBound N C
def TheTwoTheoremsImplyMinBound : Prop := AppRunningTime.BoundInM → ThmVariablesB → CorMinCompact
def MinBoundIsTheMainTheorem : Prop := ∀ (N : TM2ComputableAux Bool Bool) (C : ℕ), MeetsMinBound N C ↔ CountsCompactKCNFWithinMinBound N C
end MinOfBounds


