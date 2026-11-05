-- Prove2me | Definitions.Def_Suffices_Defs
-- name    : Suffices_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:14:05.971688+00:00
-- url     : https://prove2.me/theorems/f34a7497-76ff-4560-b845-0cc113223387
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_Exits_Defs
import Definitions.Def_Eight_SecProof_Proof
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
def satLoop (τ : ℕ) (Mc : StepMachine Formula ℤ) : StepMachine (List Bool) Bool :=
  Stepped.mapIn (decU 3) (Stepped.ite (fun p => hasNil p.2) (Stepped.const false) (walkUntil (rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ))))
def DecidesSparse (δ' : ℝ) (M : ℕ) (Mc : StepMachine Formula ℤ) (A : ℕ) : Prop :=
  ∀ (n : ℕ) (Φ : Formula), Φ.Is3CNF n → Φ.length ≤ M * n →
    ∃ (T : ℕ) (v : ℤ), Mc.Runs Φ T (A * (size Φ + n) ^ A) v ∧ (0 < v ↔ Φ.Sat) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) + A * ((n : ℝ) + 1) ^ A
def SufficesPrinted (δ : ℝ) (M : ℕ) (S : StepMachine Formula ℤ → StepMachine (List Bool) Bool) : Prop :=
  (∀ Mc : StepMachine Formula ℤ, PolyTimeSteps Mc → PolyTimeSteps (S Mc)) ∧
  ∀ (Mc : StepMachine Formula ℤ) (A : ℕ), DecidesSparse (δ / (3 * M)) M Mc A → Paper.DecidesInSteps (S Mc) δ
def StPrintedGivesSparse : Prop := ∀ (δ : ℝ) (M : ℕ) (S : StepMachine Formula ℤ → StepMachine (List Bool) Bool), SufficesPrinted δ M S → Eight.SufficesSparse δ (M : ℝ) S
def StLoopRuns : Prop := ∀ (ε : ℝ) (M τ : ℕ), Enumerates ε M τ → ∃ c : ℕ, ∀ (Mc : StepMachine Formula ℤ) (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → [] ∉ φ → ∀ (v : Formula → ℤ) (t Sm : ℕ),
  (∀ Φ ∈ tested (fun Φ => posZ (v Φ)) (produced τ n (Decode.toN φ)), Mc.Runs Φ t Sm (v Φ)) →
  (satLoop τ Mc).Runs (Sat3.enc φ) ((tested (fun Φ => posZ (v Φ)) (produced τ n (Decode.toN φ))).length * (t + 2) + depth τ n + 2) (c * ((Sat3.enc φ).length + 1) ^ c + Sm)
    ((produced τ n (Decode.toN φ)).any fun Φ => posZ (v Φ))
def StTotal : Prop := ∀ (δ : ℝ) (A D : ℕ), 0 < δ → ∃ c : ℕ, ∀ (n N : ℕ) (x : ℝ), (N : ℝ) ≤ (2 : ℝ) ^ (δ / 3 * n) → x ≤ δ / 3 * n →
  (N : ℝ) * (A * (2 : ℝ) ^ x + A * ((n : ℝ) + 1) ^ A + 3) + D * n + 2 ≤ c * (2 : ℝ) ^ (δ * n)
def StSuffices : Prop := ∀ (δ : ℝ) (M τ : ℕ), 0 < δ → 1 ≤ M → Enumerates (δ / 3) M τ → SufficesPrinted δ M (satLoop τ)
def StLoopRunsOf : Prop := StWalkUntil → StLoopRuns
def StSufficesOf : Prop := StLoopRuns → StTotal → StFoldUntilPoly → StSuffices
end Suffices


