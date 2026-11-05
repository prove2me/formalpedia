-- Prove2me | Definitions.Def_MainTheoremFormsStatement
-- name    : MainTheoremFormsStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:27:28.511225+00:00
-- url     : https://prove2.me/theorems/299d2b86-7260-43ea-9ef4-50233faf7c20
-- title:
--   Main Theorem Forms Statement
-- statement:
--   Definitions and structural lemmas for Main Theorem Forms Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/MainTheoremFormsStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInKStatement
set_option autoImplicit false
section
section
namespace MainTheoremForms
open Turing
open Sat3 (CNF)
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 x
noncomputable def expM (k m : ℕ) : ℝ := (k : ℝ) * m / Real.sqrt (lg m)
noncomputable def expN (k n : ℕ) : ℝ := (k : ℝ) ^ 2 * n * lg (lg n) / Real.sqrt (lg n)
def CountsWithin (M : TM2ComputableAux Bool Bool) (k : ℕ) {n : ℕ} (φ : CNF n) (t : ℕ) : Prop :=
  Nonempty (TM2OutputsInTime M.tm ((SatM.enc k φ).map M.inputAlphabet.invFun)
    (some ((SatK.binary n (SatK.numSat φ)).map M.outputAlphabet.invFun)) t)
noncomputable def timeMin (C k m n : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * min (expM k m) (expN k n))⌋₊
noncomputable def timeN (C k n : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * expN k n)⌋₊
noncomputable def timeCor (C k m n : ℕ) : ℕ := ⌊min ((2 : ℝ) ^ ((C : ℝ) * expM k m)) ((2 : ℝ) ^ ((C : ℝ) * expN k n))⌋₊
def MainTheoremFor (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ n → SatM.AllOccur φ →
    CountsWithin M k φ (timeMin C k φ.length n)
def MainTheoremAllOccur : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ MainTheoremFor M C
def ThmVariablesBFor (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 4 ≤ n → SatK.IsKCNF k φ →
    CountsWithin M k φ (timeN C k n)
def ThmVariablesB : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ThmVariablesBFor M C
def ClauseCountStmt : Prop := ∀ (k n : ℕ) (φ : CNF n), SatK.IsKCNF k φ → φ.length ≤ (2 * n + 1) ^ k
def CorMinFor (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ n → SatM.AllOccur φ →
    CountsWithin M k φ (timeCor C k φ.length n)
def CorMinAllOccur : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ CorMinFor M C
def CorMinIsMainTheoremStmt : Prop := ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), CorMinFor M C ↔ MainTheoremFor M C
def TogetherAllOccur : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ MainTheoremFor M C ∧ ThmVariablesBFor M C ∧ CorMinFor M C
noncomputable def timeMin3 (C m n : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * min ((m : ℝ) / Real.sqrt (lg m)) ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)))⌋₊
def Occurs {N : ℕ} (φ : CNF N) (i : Fin N) : Prop := ∃ C ∈ φ, ∃ l ∈ C, l.1 = i
noncomputable def numOcc {N : ℕ} (φ : CNF N) : ℕ := Nat.card {i : Fin N // Occurs φ i}
noncomputable def numSatOcc {N : ℕ} (φ : CNF N) : ℕ :=
  Nat.card {a : {i : Fin N // Occurs φ i} → Bool // ∀ C ∈ φ, ∃ l ∈ C, ∃ h : Occurs φ l.1, a ⟨l.1, h⟩ = l.2}
def CountsOccWithin (M : TM2ComputableAux Bool Bool) (k : ℕ) {N : ℕ} (φ : CNF N) (t : ℕ) : Prop :=
  Nonempty (TM2OutputsInTime M.tm ((SatM.enc k φ).map M.inputAlphabet.invFun)
    (some ((SatK.binary (numOcc φ) (numSatOcc φ)).map M.outputAlphabet.invFun)) t)
def AllOccurStmt : Prop := ∀ (n : ℕ) (φ : CNF n), SatM.AllOccur φ → numOcc φ = n ∧ numSatOcc φ = SatK.numSat φ
def encC (k : ℕ) {N : ℕ} (φ : CNF N) : List Bool :=
  List.replicate k true ++ false :: (List.replicate (Nat.log2 (2 * N) + 1) true ++ false :: φ.flatMap fun C => (List.range k).flatMap fun j =>
    (List.range (Nat.log2 (2 * N) + 1)).map (Sat3.slot C[j]?).testBit)
def LengthEncCStmt : Prop := ∀ (k N : ℕ) (φ : CNF N), (encC k φ).length = k + (Nat.log2 (2 * N) + 1) + 2 + φ.length * (k * (Nat.log2 (2 * N) + 1))
def CountsOccWithinC (M : TM2ComputableAux Bool Bool) (k : ℕ) {N : ℕ} (φ : CNF N) (t : ℕ) : Prop :=
  Nonempty (TM2OutputsInTime M.tm ((encC k φ).map M.inputAlphabet.invFun)
    (some ((SatK.binary (numOcc φ) (numSatOcc φ)).map M.outputAlphabet.invFun)) t)
def DecidesWithinC (M : TM2ComputableAux Bool Bool) (k : ℕ) {N : ℕ} (φ : CNF N) (t : ℕ) : Prop :=
  ∃ b : Bool, (b = true ↔ Sat3.Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((encC k φ).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)
def MainTheoremCompact : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ numOcc φ →
      CountsOccWithinC M k φ (timeMin C k φ.length (numOcc φ) + C * (encC k φ).length ^ C)
def CorMinCompact : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ numOcc φ →
      CountsOccWithinC M k φ (timeCor C k φ.length (numOcc φ) + C * (encC k φ).length ^ C)
end MainTheoremForms


