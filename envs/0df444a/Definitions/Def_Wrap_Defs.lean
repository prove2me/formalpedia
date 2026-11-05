-- Prove2me | Definitions.Def_Wrap_Defs
-- name    : Wrap_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:45:35.306621+00:00
-- url     : https://prove2.me/theorems/ab1f1940-0df6-4a3c-8fc6-2b52ea02e1d8
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_UniformInKStatement
import Definitions.Def_ToTuring_PolyT
set_option autoImplicit false
section
section
namespace Wrap
open Turing Groundwork
open scoped NNReal
def Outputs (M : TM2ComputableAux Bool Bool) (x y : List Bool) (t : ℕ) : Prop :=
  Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some (y.map M.outputAlphabet.invFun)) t)
def Wraps (M : TM2ComputableAux Bool Bool) (pre post : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) (q : ℕ) : Prop :=
  ∀ (x y : List Bool) (t : ℕ), Outputs M (pre x) y t → Outputs N x (post y) (q * (t + x.length + 1) ^ q)
def EveryMachineCanBeWrapped : Prop :=
  ∀ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) → ∀ pre post : List Bool → List Bool, PolyT pre → PolyT post →
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧ Wraps M pre post N q
def pad4 {n : ℕ} (φ : Sat3.CNF n) : Sat3.CNF (n + 4) :=
  (φ.map fun C => C.map fun l => (Fin.castAdd 4 l.1, l.2)) ++ (List.finRange 4).map fun j => [(Fin.natAdd n j, true)]
def Pad4KeepsSatAndMeetsSideConditions : Prop :=
  ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ →
    SatK.IsKCNF 3 (pad4 φ) ∧ (pad4 φ).length = φ.length + 4 ∧ 4 ≤ MainTheoremForms.numOcc (pad4 φ) ∧ MainTheoremForms.numOcc (pad4 φ) ≤ n + 4 ∧
      (Sat3.Satisfiable (pad4 φ) ↔ Sat3.Satisfiable φ)
def MapsPlainToPaddedCompact (pre : List Bool → List Bool) : Prop :=
  ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → pre (Sat3.enc φ) = MainTheoremForms.encC 3 (pad4 φ)
def IsFrontEnd (pre : List Bool → List Bool) : Prop := PolyT pre ∧ MapsPlainToPaddedCompact pre
def FrontEndExists : Prop := ∃ pre : List Bool → List Bool, IsFrontEnd pre
def someBit (w : List Bool) : List Bool := [w.any id]
def CountsCompactKCNFWithinMinBound (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k V : ℕ) (φ : Sat3.CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ MainTheoremForms.numOcc φ →
    MainTheoremForms.CountsOccWithinC M k φ (MainTheoremForms.timeMin C k φ.length (MainTheoremForms.numOcc φ) + C * (MainTheoremForms.encC k φ).length ^ C)
def DecidesEveryDelta (N : TM2ComputableAux Bool Bool) : Prop :=
  ∀ δ : ℝ≥0, 0 < δ → ∃ c : ℕ, Sat3.DecidesTM N fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊
def DecidesAtRateInN (N : TM2ComputableAux Bool Bool) : Prop :=
  ∃ c : ℕ, Sat3.DecidesTM N (SatM.boundNK (SatK.rN 1 (1 / 2)) c 3)
def EveryWrapperOfACounterDecidesEveryDelta : Prop :=
  ∀ pre : List Bool → List Bool, MapsPlainToPaddedCompact pre → ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), CountsCompactKCNFWithinMinBound M C →
    ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wraps M pre someBit N q → DecidesEveryDelta N
def EveryWrapperOfACounterDecidesAtRateInN : Prop :=
  ∀ pre : List Bool → List Bool, MapsPlainToPaddedCompact pre → ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), CountsCompactKCNFWithinMinBound M C →
    ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wraps M pre someBit N q → DecidesAtRateInN N
def LastStepsArePolynomialTime : Prop := PolyT (id : List Bool → List Bool) ∧ PolyT someBit
def CounterCanBeWrappedAndEveryWrapperDecides : Prop :=
  ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) → CountsCompactKCNFWithinMinBound M C →
    (∃ (pre : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) (q : ℕ), IsFrontEnd pre ∧ (∀ i, Finite (N.tm.Γ i)) ∧ Wraps M pre someBit N q) ∧
      ∀ pre : List Bool → List Bool, MapsPlainToPaddedCompact pre → ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wraps M pre someBit N q → DecidesEveryDelta N ∧ DecidesAtRateInN N
def OneMachineEveryDeltaAndETHFails : Prop := Sat3.SubexpTM ∧ Sat3.ThmEveryDelta ∧ ¬ Sat3.ETH_TM ∧ PaperSentences.ThmEveryDelta ∧ ¬ PaperSentences.ETH
def CountingBoundImpliesFailureOfETH : Prop := MainTheoremForms.MainTheoremCompact → OneMachineEveryDeltaAndETHFails
end Wrap


