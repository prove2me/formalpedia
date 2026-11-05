-- Prove2me | Definitions.Def_PairsToBound_Defs
-- name    : PairsToBound_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:40:25.757645+00:00
-- url     : https://prove2.me/theorems/6c4a4cf8-88e9-4a9e-8c83-0961bad33e24
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_RecursionWithPieces_Defs
import Definitions.Def_TwoMachines_Defs
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_GeneralPieces_Num_Between
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)
def NumberBetween {Idx : Type} [Enc Idx] (S : Solver Idx) {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) (num : U × U → ℕ × ℕ) : Prop :=
  PolyT num ∧ ∀ l : ℕ,
    e l ≤ ((num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).1 : ℝ) / ((num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).2 : ℝ) ∧
    ((num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).1 : ℝ) / ((num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).2 : ℝ) ≤ 2 * e l
def TheRecursionHasLevels : Prop :=
  ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces ρ c P A val → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
    ∃ Q : (solverOf (GeneralPieces.Tied.recOf P val c)).Seq (Levels.Gen.e ρ x₀) C₀,
      (solverOf (GeneralPieces.Tied.recOf P val c)).Poly ∧
      (∀ l : ℕ, (solverOf (GeneralPieces.Tied.recOf P val c)).K (Q.idx l) = Levels.Gen.K x₀ l) ∧ Q.pick = ClauseBound.Gen.Pick.pick (GeneralPieces.Tied.recOf P val c) x₀
def fractionHalf (p : U × U) : ℕ × ℕ := (GeneralPieces.Between.num p.1.length, GeneralPieces.Between.den p.1.length)
def ThePairsSatisfyTheHypothesis : Prop :=
  ∀ c : ℕ, ∃ C₀ Cp : ℕ, ∀ (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces (1 / Real.sqrt 2) c P₀ A val →
    ∃ Q : (RecursionWithPieces.solverAB P₀ val c).Seq (Levels.Gen.e (1 / Real.sqrt 2) (GeneralPieces.x₀Of c)) C₀,
      (RecursionWithPieces.solverAB P₀ val c).Poly ∧
      (∀ l : ℕ, (RecursionWithPieces.solverAB P₀ val c).K (Q.idx l) = Levels.Gen.K (GeneralPieces.x₀Of c) l) ∧ Q.pick = RecursionWithPieces.pickAB P₀ val c ∧
      NumberBetween (RecursionWithPieces.solverAB P₀ val c) Q fractionHalf ∧
      Precision (Levels.Gen.e (1 / Real.sqrt 2) (GeneralPieces.x₀Of c)) RecursionWithPieces.prec Cp
def ThetaOfThePairs : Prop :=
  ∀ x₀ l : ℕ, 18 ≤ x₀ →
    1 / 2 * (1 / Real.sqrt 2) ^ l ≤ Levels.Gen.e (1 / Real.sqrt 2) x₀ l ∧ Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ 0.85 * (1 / Real.sqrt 2) ^ l ∧
    (x₀ : ℝ) * 2 ^ l ≤ lg (Levels.Gen.K x₀ l) ∧ lg (Levels.Gen.K x₀ l) ≤ (3 * x₀ + 6) * 2 ^ l ∧
    1 / 2 * Real.sqrt x₀ / Real.sqrt (lg (Levels.Gen.K x₀ l)) ≤ Levels.Gen.e (1 / Real.sqrt 2) x₀ l ∧
    Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ 0.85 * Real.sqrt (3 * x₀ + 6) / Real.sqrt (lg (Levels.Gen.K x₀ l))
def MainRegimeBound : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (a : ℕ), (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
    ∀ (M : TM2ComputableAux Bool Bool) (C' : ℕ), ThmVariablesAFor S Q M C' →
      ∃ C : ℕ, ∀ (k n : ℕ) (φ : CNF n), S.K (Q.idx 0) ^ 17 ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeN C k n)
def widthOr3 {n : ℕ} (φ : CNF n) : ℕ := (φ.map List.length).foldr max 3
def WidthOr3Stmt : Prop :=
  ∀ (n : ℕ) (φ : CNF n), 3 ≤ widthOr3 φ ∧ (φ.Nodup → SatK.IsKCNF (widthOr3 φ) φ) ∧
    ∀ k : ℕ, 1 ≤ k → SatK.IsKCNF k φ → widthOr3 φ ≤ max k 3 ∧ widthOr3 φ ^ 2 ≤ 9 * k ^ 2
def TheBoundIncreasesWithTheWidth : Prop :=
  (∀ C k k' n : ℕ, 4 ≤ n → k ≤ k' → timeN C k n ≤ timeN C k' n) ∧
  ∀ (C k k' n : ℕ) (e : ℝ), 3 ≤ k → k ≤ k' → 0 < e → e ≤ 1 → timeVariablesA C k n e ≤ timeVariablesA C k' n e
def RewritesAtWidthOr3 (pre : List Bool → List Bool) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → pre (SatM.enc k φ) = SatM.enc (widthOr3 φ) φ
def TestsTheMainRegime (K₀ : ℕ) (test : List Bool → Bool) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → (test (SatM.enc k φ) = true ↔ K₀ ^ 17 ≤ n ∧ ((widthOr3 φ : ℕ) : ℝ) ^ 4 ≤ lg n)
def FrontEndAndTestExist : Prop :=
  (∃ pre : List Bool → List Bool, PolyT pre ∧ RewritesAtWidthOr3 pre) ∧ ∀ K₀ : ℕ, ∃ test : List Bool → Bool, PolyT test ∧ TestsTheMainRegime K₀ test
def TriesAllWithin (Mb : TM2ComputableAux Bool Bool) (c : ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 2 ≤ n → SatK.IsKCNF k φ → CountsWithin Mb k φ (2 ^ (c * n) * n ^ (c * k))
def Computes (M : TM2ComputableAux Bool Bool) (f : List Bool × U → List Bool) (e : List Bool → ℕ) (q : ℕ) : Prop :=
  ∀ x : List Bool, Outputs M x (f (x, PaddedDescent.pad (e x))) (q * (x.length + 2 ^ e x + 1) ^ q)
def exhaust (p : List Bool × U) : List Bool := CountKSat.outW (fmlOf p.1, UniformInK.bruteU p)
def EveryExhaustiveMachineTriesAll : Prop :=
  ∀ (Mb : TM2ComputableAux Bool Bool) (qb : ℕ), Computes Mb exhaust (fun x => (fmlOf x).1.length) qb → ∃ c : ℕ, TriesAllWithin Mb c
def ExhaustiveMachineExists : Prop :=
  ∃ (Mb : TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (Mb.tm.Γ i)) ∧ TriesAllWithin Mb c ∧ Computes Mb exhaust (fun x => (fmlOf x).1.length) q
def ClauseCountPowStmt : Prop := ∀ k n : ℕ, 3 ≤ n → (2 * n + 1) ^ k ≤ n ^ (2 * k)
def FallBackIsWithinTheBound : Prop :=
  (∀ n : ℕ, 4 ≤ n → lg n ≤ n / Real.sqrt (lg n) ∧ (n : ℝ) / Real.sqrt (lg n) ≤ n * lg (lg n) / Real.sqrt (lg n)) ∧
  (∀ k n : ℕ, 1 ≤ k → 4 ≤ n → (k : ℝ) * lg n ≤ expN k n) ∧
  (∀ k n : ℕ, 4 ≤ n → lg n < (k : ℝ) ^ 4 → (n : ℝ) * lg (lg n) ≤ expN k n ∧ (n : ℝ) ≤ n * lg (lg n)) ∧
  (∀ K₀ n : ℕ, 2 ≤ K₀ → 4 ≤ n → n < K₀ ^ 17 → (n : ℝ) / Real.sqrt (17 * lg K₀) ≤ n * lg (lg n) / Real.sqrt (lg n))
def EveryChoiceMeetsThmVariablesB : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (a : ℕ), (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
    ∀ (M : TM2ComputableAux Bool Bool) (C' : ℕ), ThmVariablesAFor S Q M C' → ∀ (Mb : TM2ComputableAux Bool Bool) (c : ℕ), TriesAllWithin Mb c →
      ∀ (pre : List Bool → List Bool) (test : List Bool → Bool), RewritesAtWidthOr3 pre → TestsTheMainRegime (S.K (Q.idx 0)) test →
        ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Chooses M Mb test pre id id id N q → ∃ C : ℕ, ThmVariablesBFor N C
def ThmVariablesBFromThmVariablesA : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (a : ℕ), (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
    ∀ (M : TM2ComputableAux Bool Bool) (C' : ℕ), (∀ i, Finite (M.tm.Γ i)) → ThmVariablesAFor S Q M C' →
      (∃ (Mb : TM2ComputableAux Bool Bool) (c qb : ℕ) (pre : List Bool → List Bool) (test : List Bool → Bool) (K₁ : Coding M) (K₂ : Coding Mb) (N : TM2ComputableAux Bool Bool) (q₀ q : ℕ),
          (∀ i, Finite (Mb.tm.Γ i)) ∧ TriesAllWithin Mb c ∧ Computes Mb exhaust (fun x => (fmlOf x).1.length) qb ∧
          PolyT pre ∧ RewritesAtWidthOr3 pre ∧ PolyT test ∧ TestsTheMainRegime (S.K (Q.idx 0)) test ∧
          (∀ i, Finite (N.tm.Γ i)) ∧ Hosts (choose K₁ K₂ test pre id id id) N q₀ ∧ Chooses M Mb test pre id id id N q) ∧
        ∀ (Mb : TM2ComputableAux Bool Bool) (c : ℕ), TriesAllWithin Mb c →
          ∀ (pre : List Bool → List Bool) (test : List Bool → Bool), RewritesAtWidthOr3 pre → TestsTheMainRegime (S.K (Q.idx 0)) test →
            ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Chooses M Mb test pre id id id N q → ∃ C : ℕ, ThmVariablesBFor N C
def ThmVariablesAImpliesThmVariablesB : Prop := ThmVariablesA → AppRunningTime.ThmHalfPieces → ThmVariablesB
end PairsToBound


