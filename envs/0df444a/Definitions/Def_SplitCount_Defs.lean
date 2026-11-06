-- Prove2me | Definitions.Def_SplitCount_Defs
-- name    : SplitCount_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:22:55.115205+00:00
-- url     : https://prove2.me/theorems/02801add-a39a-40d8-b5e7-fd235dbc25c8
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_Occ_Defs
import Definitions.Def_Eight_Cor_WidthProg
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_CountKSat_Interfaces
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog Paper CountKSat GraphProblems Eight Eight.ViaGrouping Eight.Width Occ
abbrev NNode : Type := List Unit × CNode
def rootPlain (p : List Unit × Fml) : NNode := (p.1, (rootP p.2, []))
def stepPlain (step : CNode → Option (CNode × CNode)) (x : NNode) : Option (NNode × NNode) := (step x.2).map fun lh => ((x.1, lh.1), (x.1, lh.2))
def leafPlain (x : NNode) : List Unit × Fml := (x.1, leafF x.2)
def timesFreeAfter (Cnt : StepMachine Fml ℤ) : StepMachine (List Unit × Fml) ℕ := Stepped.bind (Stepped.mapIn Prod.snd Cnt) (Stepped.ofFun timesFree)
def countThree (ℓ : ℕ) : StepMachine (List Unit × Fml) ℕ := timesFreeAfter (COUNTp ℓ)
def engineBy (step : CNode → Option (CNode × CNode)) (D : StepMachine (List Unit × Fml) ℕ) : StepMachine (List Unit × Fml) (List Bool) :=
  Stepped.bind
    (Stepped.ite (fun p => hasNil p.2) (Stepped.const 0) (walkSum (stepPlain step) rootPlain (Stepped.mapIn leafPlain (Stepped.mapIn widthP D))))
    (Stepped.ofFun outW)
def engineSplit (step : CNode → Option (CNode × CNode)) (ℓ : ℕ) : StepMachine (List Unit × Fml) (List Bool) := engineBy step (countThree ℓ)
def ENGINEsplit (k ℓ τ : ℕ) : StepMachine (List Unit × Fml) (List Bool) := engineSplit (stepC (WidthK.theta τ) k) ℓ
def COUNTsplit (k ℓ τ : ℕ) : StepMachine (List Bool) (List Bool) := Stepped.mapIn (decU k) (ENGINEsplit k ℓ τ)
def ComputesZ (Cnt : StepMachine Fml ℤ) (δ' : ℝ) (A : ℕ) : Prop := ∀ Φ : Fml, (∀ C ∈ Φ, C.length ≤ 3) →
  ∃ T : ℕ, Cnt.Runs Φ T (A * size Φ ^ A) ((Eight.numSat Φ : ℕ) : ℤ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)
def CountsThree (D : StepMachine (List Unit × Fml) ℕ) (δ' : ℝ) (A : ℕ) : Prop := ∀ (n : ℕ) (Φ : Fml), (∀ C ∈ Φ, C.length ≤ 3) → Below n Φ →
  ∃ T : ℕ, D.Runs (List.replicate n (), Φ) T (A * (n + size Φ + 1) ^ A) (cntN n Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)
def StStepOneFor : Prop := ∀ (Cnt : StepMachine Fml ℤ) (δ' : ℝ) (A : ℕ), 0 ≤ δ' → ComputesZ Cnt δ' A → ∃ A' : ℕ, CountsThree (timesFreeAfter Cnt) δ' A'
def StComputesZ : Prop := ∀ (δ' : ℝ), 0 < δ' → δ' ≤ 1 → ∀ (K : ℕ) (E : Paper.CliqueAlgorithm), 2 ≤ K → 72 / δ' ≤ K → E.Within K (δ' / 12) →
  ∃ A : ℕ, ComputesZ ((netAlg K (3 * K ^ 8) E).app (satProcs (3 * K ^ 8) 3)) δ' A
def StCountIsNetworkMachine : Prop := ∀ ℓ : ℕ, COUNTp ℓ = (netAlg (levelK ℓ) (3 * levelK ℓ ^ 8) (CLIQUEp ℓ)).app (satProcs (3 * levelK ℓ ^ 8) 3)
def StStepOne : Prop := ∀ (δ' : ℝ), 0 < δ' → δ' ≤ 1 → ∀ ℓ : ℕ, 72 / δ' ≤ levelK ℓ → Eight.Level.levelE ℓ ≤ δ' / 12 → ∃ A : ℕ, CountsThree (countThree ℓ) δ' A
def SparsifiesPlain (k : ℕ) (ε : ℝ) (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ) : Prop :=
  ∀ (n : ℕ) (ψ : Fml), (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
    ((leaves (stepPlain step) (Dd * n) (rootPlain (List.replicate n (), ψ))).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves (stepPlain step) (Dd * n) (rootPlain (List.replicate n (), ψ)), stepPlain step x = none ∧ x.1 = List.replicate n () ∧ (leafF x.2).length ≤ Bl * n ∧
      ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) ∧
    cntN n ψ = ((leaves (stepPlain step) (Dd * n) (rootPlain (List.replicate n (), ψ))).map fun x => cntN n (leafF x.2)).sum ∧
    ∀ i, ((round (stepPlain step))^[i] ([rootPlain (List.replicate n (), ψ)], [])).1.length ≤ Dd * n + 1 ∧
      ∀ x ∈ ((round (stepPlain step))^[i] ([rootPlain (List.replicate n (), ψ)], [])).1, x.1 = List.replicate n () ∧ (leafF x.2).length ≤ (ψ.length + n) * Sk ∧
        ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n
def StDisjoint : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ) (x l h : CNode), stepC θ k x = some (l, h) → ∀ a : ℕ → Bool,
  ((∀ C ∈ leafF x, ∃ t ∈ C, a t.1 = t.2) ↔ ((∀ C ∈ leafF l, ∃ t ∈ C, a t.1 = t.2) ∨ (∀ C ∈ leafF h, ∃ t ∈ C, a t.1 = t.2))) ∧
  ¬((∀ C ∈ leafF l, ∃ t ∈ C, a t.1 = t.2) ∧ (∀ C ∈ leafF h, ∃ t ∈ C, a t.1 = t.2))
def StDisjointLeaves : Prop := ∀ (θ : ℕ → ℕ) (k d : ℕ) (x : CNode),
  (leaves (stepC θ k) d x).Pairwise fun y z => ∀ a : ℕ → Bool, ¬((∀ C ∈ leafF y, ∃ t ∈ C, a t.1 = t.2) ∧ (∀ C ∈ leafF z, ∃ t ∈ C, a t.1 = t.2))
def StStepTwo : Prop := ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∃ τ Dd Bl Sk : ℕ, SparsifiesPlain k ε (stepC (WidthK.theta τ) k) Dd Bl Sk
def StStepThree : Prop := ∀ (w n : ℕ) (Ψ : Fml), (∀ C ∈ Ψ, C.length ≤ w) → Below n Ψ →
  (∀ C ∈ (widthP (List.replicate n (), Ψ)).2, C.length ≤ 3) ∧ Below (widthP (List.replicate n (), Ψ)).1.length (widthP (List.replicate n (), Ψ)).2 ∧ (widthP (List.replicate n (), Ψ)).2.Nodup ∧
  (widthP (List.replicate n (), Ψ)).1.length ≤ n + (w - 3) * Ψ.length ∧ (widthP (List.replicate n (), Ψ)).2.length ≤ Ψ.length + 3 * ((w - 3) * Ψ.length) ∧
  cntN (widthP (List.replicate n (), Ψ)).1.length (widthP (List.replicate n (), Ψ)).2 = cntN n Ψ
noncomputable def deltaPrime (δ : ℝ) (w Bl : ℕ) : ℝ := min (δ / (3 * ((1 + 3 * ((w : ℝ) - 3)) * ((Bl : ℝ) + 1)))) 1
def StSuffices : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ), SparsifiesPlain k (δ / 3) step Dd Bl Sk →
  ∀ (D : StepMachine (List Unit × Fml) ℕ) (δ' : ℝ) (A : ℕ), 0 ≤ δ' → δ' * ((1 + 3 * (((max k 3 : ℕ) : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3 → CountsThree D δ' A →
  ∃ c : ℕ, Serves (engineBy step D) k δ c
def StCountsAt : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ), SparsifiesPlain k (δ / 3) step Dd Bl Sk →
  ∀ ℓ : ℕ, 72 / deltaPrime δ (max k 3) Bl ≤ levelK ℓ → Eight.Level.levelE ℓ ≤ deltaPrime δ (max k 3) Bl / 12 → ∃ c : ℕ, Serves (engineSplit step ℓ) k δ c
def StCert : Prop := (∀ Cnt : StepMachine Fml ℤ, PolyTimeSteps Cnt → PolyTimeSteps (timesFreeAfter Cnt)) ∧
  ∀ (step : CNode → Option (CNode × CNode)) (D : StepMachine (List Unit × Fml) ℕ), PolyT step → PolyTimeSteps D → PolyTimeSteps (engineBy step D)
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
end SplitCount


