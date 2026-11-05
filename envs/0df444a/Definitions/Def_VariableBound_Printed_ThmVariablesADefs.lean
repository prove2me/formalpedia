-- Prove2me | Definitions.Def_VariableBound_Printed_ThmVariablesADefs
-- name    : VariableBound_Printed_ThmVariablesADefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:31:28.433259+00:00
-- url     : https://prove2.me/theorems/22014168-cf43-448d-9ae0-9834ce360671
-- title:
--   Thm Variables ADefs
-- statement:
--   Definitions and structural lemmas for Thm Variables ADefs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/ThmVariablesADefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_VariableBound_Params_Defs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace MainTheoremForms
open Turing Groundwork PaddedDescent.F ClauseBound.Alg
open Sat3 (CNF)
def Precision (e : ℕ → ℝ) (slU : U → U) (C : ℕ) : Prop :=
  PolyT slU ∧ (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) ∧ ∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C
noncomputable def expVariablesA (k n : ℕ) (e : ℝ) : ℝ := (k : ℝ) ^ 2 * e * n * lg (k / e)
noncomputable def timeVariablesA (C k n : ℕ) (e : ℝ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * expVariablesA k n e)⌋₊
noncomputable def timeVariablesAAlpha (C k n : ℕ) (α' : ℝ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * ((k : ℝ) ^ 2 * n * lg (lg n) / lg n ^ α'))⌋₊
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx) {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
def IsLevel (n l : ℕ) : Prop := S.K (Q.idx l) ^ 17 ≤ n ∧ n < S.K (Q.idx (l + 1)) ^ 17
def ThmVariablesAFor (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k n l : ℕ) (φ : CNF n), IsLevel S Q n l → 3 ≤ k → (k : ℝ) ^ 4 ≤ lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariablesA C k n (e l))
end
def ThmVariablesA : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ), Precision e slU C →
    ∃ (M : TM2ComputableAux Bool Bool) (C' : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ThmVariablesAFor S Q M C'
def ThmVariablesAInParticular : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (α' : ℝ) (c : ℕ), 0 < α' → (∀ l : ℕ, e l ≤ c / lg (S.K (Q.idx l)) ^ α') →
    ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), ThmVariablesAFor S Q M C →
      ∃ C' : ℕ, ∀ (k n : ℕ) (φ : CNF n), S.K (Q.idx 0) ^ 17 ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariablesAAlpha C' k n α')
def StepSparsifyFactsStmt : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (k n l : ℕ), IsLevel S Q n l → 1 ≤ k → (k : ℝ) ^ 4 ≤ lg n →
    lg n / (17 * C₀) < lg (S.K (Q.idx l)) ∧ lg (k / e l) ≤ (C₀ + 1 / 4) * lg (lg n)
def StepSparsifyLargeStmt : Prop :=
  ∀ C₀ : ℕ, ∃ n₁ : ℕ, ∀ (k n : ℕ) (e : ℝ), n₁ ≤ n → (k : ℝ) ^ 4 ≤ lg n → 1 / lg n ^ C₀ ≤ e → (k : ℝ) * lg n ≤ e * n
def StepSparsifySmallStmt : Prop :=
  ∀ C₀ n₁ : ℕ, ∃ c : ℕ, ∀ (k n : ℕ) (e : ℝ), 2 ≤ n → n < n₁ → 3 ≤ k → 1 / lg n ^ C₀ ≤ e → e ≤ 1 → (n : ℝ) ≤ c * expVariablesA k n e ∧ (k : ℝ) * lg n ≤ c * expVariablesA k n e
def SettingN0Stmt : Prop :=
  ∀ C₀ : ℕ, 1 ≤ C₀ → ∃ n₀ : ℕ, ∀ n k Δ : ℕ, n₀ ≤ n → (k : ℝ) ^ 4 ≤ lg n → 2 ≤ Δ → (Δ : ℝ) ≤ lg n ^ (4 * k * C₀) →
    lg Δ ≤ 4 * k * C₀ * lg (lg n) ∧ 4 * (k : ℝ) * C₀ * lg (lg n) ≤ 4 * C₀ * lg n ^ (1 / 4 : ℝ) * lg (lg n) ∧
    (Δ : ℝ) ≤ (n : ℝ) ^ (1 / (40 * C₀ : ℝ)) ∧ 2 * lg (2 * Δ) ≤ n ∧
    ∀ m nb rb : ℕ, nb < m → m ≤ Δ * n → AppVariables.IsNb n Δ nb → AppVariables.IsRb (AppVariables.beta n m nb) rb → rb ≤ 10 * n ∧ AppVariables.Mb (AppVariables.beta n m nb) rb ≤ 14 * n
end MainTheoremForms


