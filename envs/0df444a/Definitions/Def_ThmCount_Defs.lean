-- Prove2me | Definitions.Def_ThmCount_Defs
-- name    : ThmCount_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:53:33.621481+00:00
-- url     : https://prove2.me/theorems/06caace1-c9d2-4c19-8974-05d02f4489fe
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_Wrap_Defs
import Definitions.Def_SparsificationLemma_Cal_Defs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace ThmCount
open Turing Groundwork PaperSentences
def MapsToPadded (pre : List Bool → List Bool) : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF 3 φ → pre (SatK.enc 3 φ) = SatM.enc 3 (Wrap.pad4 φ)
def StFrontEnd : Prop := ∃ pre : List Bool → List Bool, PolyT pre ∧ MapsToPadded pre
def dropFour (y : List Bool) : List Bool := y.take (y.length - 4)
def StPadKeepsCount : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF 3 φ →
  SatK.IsKCNF 3 (Wrap.pad4 φ) ∧ SatK.numSat (Wrap.pad4 φ) = SatK.numSat φ ∧ dropFour (SatK.binary (n + 4) (SatK.numSat (Wrap.pad4 φ))) = SatK.binary n (SatK.numSat φ)
def StInputLength : Prop := ∃ a d : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF 3 φ → (SatK.enc 3 φ).length ≤ a * (n + 2) ^ d
def StRates : Prop := ∀ C q a d : ℕ, ∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
  (q : ℝ) * ((2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) + (a : ℝ) * ((n : ℝ) + 2) ^ d + 1) ^ q ≤ (2 : ℝ) ^ (C' * (n / lg n ^ ((1 : ℝ) / 20)))
def StLastStep : Prop := PolyT dropFour
def StFromVariablesB : Prop := ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), MainTheoremForms.ThmVariablesBFor M C → ∀ pre : List Bool → List Bool, MapsToPadded pre →
  ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wrap.Wraps M pre dropFour N q →
    ∃ (C' : ℝ) (t : ℕ → ℕ), SatK.CountsTM 3 N t ∧ ∀ n : ℕ, 2 ≤ n → (t n : ℝ) ≤ (2 : ℝ) ^ (C' * (n / lg n ^ ((1 : ℝ) / 20)))
def StCanBeWrappedAndEveryWrapperCounts : Prop := ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) → MainTheoremForms.ThmVariablesBFor M C →
  (∃ (pre : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) (q : ℕ), PolyT pre ∧ MapsToPadded pre ∧ (∀ i, Finite (N.tm.Γ i)) ∧ Wrap.Wraps M pre dropFour N q) ∧
  ∀ pre : List Bool → List Bool, MapsToPadded pre → ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wrap.Wraps M pre dropFour N q →
    ∃ (C' : ℝ) (t : ℕ → ℕ), SatK.CountsTM 3 N t ∧ ∀ n : ℕ, 2 ≤ n → (t n : ℝ) ≤ (2 : ℝ) ^ (C' * (n / lg n ^ ((1 : ℝ) / 20)))
def StTheorem : Prop := MainTheoremForms.ThmVariablesB → CountRate (1 / 20)
def StMEps : Prop := ∃ A : ℝ, ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 →
  ((2 + 4 * SparsificationLemma.Cal.alphaC 3 ε * (32 * SparsificationLemma.Cal.alphaC 3 ε) : ℕ) : ℝ) ≤ A * ((ε : ℝ) ^ (-2 : ℝ) * lg (1 / (ε : ℝ)) ^ 2)
def StMEpsClauses : Prop := ∃ A : ℝ, ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 → ∀ (n : ℕ) (φ : Groundwork.Sparsify.PFml), SparsificationLemma.IsKCNF 3 n φ →
  ∀ Φ ∈ SparsificationLemma.Cal.sparsify 3 n ε φ, (Φ.length : ℝ) ≤ (A * ((ε : ℝ) ^ (-2 : ℝ) * lg (1 / (ε : ℝ)) ^ 2) + 2) * n
def StRemarkTime : Prop := ∃ C : ℝ, CountsInTime 3 4 fun n => (2 : ℝ) ^ (C * (n * lg (lg n) ^ ((2 : ℝ) / 3) / lg n ^ ((1 : ℝ) / 6)))
end ThmCount


