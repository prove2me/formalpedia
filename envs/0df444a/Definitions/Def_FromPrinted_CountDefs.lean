-- Prove2me | Definitions.Def_FromPrinted_CountDefs
-- name    : FromPrinted_CountDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:30:35.382081+00:00
-- url     : https://prove2.me/theorems/7d611282-c613-463c-b430-95534dd2be38
-- title:
--   Count Defs
-- statement:
--   Definitions and structural lemmas for Count Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/CountDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_Printed_Programs
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SplitCount
namespace FromPrinted.SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog Paper CountKSat GraphProblems Eight Eight.ViaGrouping Eight.Width Occ
def countThree (ℓ : ℕ) : StepMachine (List Unit × Fml) ℕ := timesFreeAfter (Printed.COUNT ℓ)
def engineSplit (step : CNode → Option (CNode × CNode)) (ℓ : ℕ) : StepMachine (List Unit × Fml) (List Bool) := engineBy step (countThree ℓ)
def ENGINEsplit (k ℓ τ : ℕ) : StepMachine (List Unit × Fml) (List Bool) := engineSplit (stepC (WidthK.theta τ) k) ℓ
def COUNTsplit (k ℓ τ : ℕ) : StepMachine (List Bool) (List Bool) := Stepped.mapIn (decU k) (ENGINEsplit k ℓ τ)
def StComputesZ : Prop := ∀ (δ' : ℝ), 0 < δ' → δ' ≤ 1 → ∀ (K : ℕ) (M : Printed.CliqueMachine) (Cc : ℕ), 2 ≤ K → 72 / δ' ≤ K → Printed.AchievedBy M Cc K (δ' / 12) →
  ∃ A : ℕ, ComputesZ (Printed.networkOnSteps (3 * K ^ 8) (Printed.groupingMachine K (3 * K ^ 8) M) (Printed.formulaProcs (3 * K ^ 8) 3)) δ' A
def withFirstLine (Cnt : StepMachine Fml ℤ) : StepMachine Fml ℤ := Stepped.ite (fun Φ : Fml => Φ.isEmpty) (Stepped.const 1) Cnt
def StFirstLine : Prop := ∀ (Cnt : StepMachine Fml ℤ) (δ' : ℝ) (A : ℕ), ComputesZ Cnt δ' A → ∃ A' : ℕ, ComputesZ (withFirstLine Cnt) δ' A'
def StCountIsNetworkMachine : Prop := ∀ ℓ : ℕ, Printed.COUNT ℓ = withFirstLine (Printed.networkOnSteps (3 * levelK ℓ ^ 8) (Printed.groupingMachine (levelK ℓ) (3 * levelK ℓ ^ 8) (Printed.CLIQUE ℓ)) (Printed.formulaProcs (3 * levelK ℓ ^ 8) 3))
def StStepOne : Prop := ∀ (δ' : ℝ), 0 < δ' → δ' ≤ 1 → ∀ ℓ : ℕ, 72 / δ' ≤ levelK ℓ → Eight.Level.levelE ℓ ≤ δ' / 12 → ∃ A : ℕ, CountsThree (countThree ℓ) δ' A
def StCountsAt : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ), SparsifiesPlain k (δ / 3) step Dd Bl Sk →
  ∀ ℓ : ℕ, 72 / deltaPrime δ (max k 3) Bl ≤ levelK ℓ → Eight.Level.levelE ℓ ≤ deltaPrime δ (max k 3) Bl / 12 → ∃ c : ℕ, Serves (engineSplit step ℓ) k δ c
def StCountsWithAnyCliqueAlgorithm : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ), SparsifiesPlain k (δ / 3) step Dd Bl Sk →
  ∀ (K : ℕ) (M : Printed.CliqueMachine) (Cc : ℕ), 2 ≤ K → 72 / deltaPrime δ (max k 3) Bl ≤ K → Printed.AchievedBy M Cc K (deltaPrime δ (max k 3) Bl / 12) →
  ∃ c : ℕ, Serves (engineBy step (timesFreeAfter (Printed.networkOnSteps (3 * K ^ 8) (Printed.groupingMachine K (3 * K ^ 8) M) (Printed.formulaProcs (3 * K ^ 8) 3)))) k δ c
def StEngineCounts : Prop := EngineCounts ENGINEsplit
def StCOUNTsplitCounts : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (COUNTsplit k ℓ τ) ∧
  ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    ∃ T : ℕ, (COUNTsplit k ℓ τ).Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) (SatK.binary n (SatK.numSat φ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
def StTiedTM : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (COUNTsplit k ℓ τ) ∧
  (∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    ∃ T : ℕ, (COUNTsplit k ℓ τ).Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) (SatK.binary n (SatK.numSat φ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) ∧
  (∀ (x w : List Bool) (T S : ℕ), (COUNTsplit k ℓ τ).Runs x T S w →
    Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some (w.map M.outputAlphabet.invFun)) (q * (T + 1) * (x.length + S + 1) ^ q))) ∧
  SatK.CountsTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
abbrev ThreeSatStatement : Prop := PaperSentences.CorCounting
end FromPrinted.SplitCount


