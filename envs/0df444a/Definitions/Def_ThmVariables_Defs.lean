-- Prove2me | Definitions.Def_ThmVariables_Defs
-- name    : ThmVariables_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:46:26.343524+00:00
-- url     : https://prove2.me/theorems/5cd56d01-6809-4ad2-ab96-bd6e93e283da
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CliqueLevelsStatement
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_RecursionToBound_Defs
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count


set_option autoImplicit false
section
section
namespace ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
open Sat3 (CNF)
def IsLevel (K : ℕ → ℕ) (n l : ℕ) : Prop := K l ^ 17 ≤ n ∧ n < K (l + 1) ^ 17
structure Hypothesis (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) : Prop where
  /-- «let K_ℓ ≥ 2 be integers and e_ℓ reals with K_ℓ < K_(ℓ+1) ≤ K_ℓ^C₀ and (log K_ℓ)^(−C₀) ≤ e_ℓ ≤
  1» -/
  levels : Levels K e C₀
  /-- «K_ℓ … can be computed from ℓ in time polynomial in K_ℓ» -/
  computesK : ComputesLevels K kf
  /-- «… and a number in [e_ℓ, 2e_ℓ]» -/
  number : CliqueLevels.NumberBetween K e num
  /-- E is an algorithm: each of its steps is computed in polynomial time -/
  steps : E.PolyTimeSteps
  /-- «one deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to tables with |W_w| <
  2^B, outputs the value of the (K_ℓ, λ)-clique within 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{C₀K_ℓ²} operations» -/
  solves : Solves E K e C₀
def Conclusion (K : ℕ → ℕ) (e : ℕ → ℝ) (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k n l : ℕ) (φ : CNF n), IsLevel K n l → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariablesA C k n (e l))
def PartA : Prop :=
  ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ) (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ),
    Hypothesis K e C₀ kf num E → ∃ (M : TM2ComputableAux Bool Bool) (C' : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Conclusion K e M C'
def InParticular : Prop :=
  ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ), Levels K e C₀ → ∀ (α' : ℝ) (c : ℕ), 0 < α' → (∀ l : ℕ, e l ≤ c / MainTheoremForms.lg (K l) ^ α') →
    ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), Conclusion K e M C →
      ∃ C' : ℕ, ∀ (k n : ℕ) (φ : CNF n), K 0 ^ 17 ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariablesAAlpha C' k n α')
def PartAForEveryMachine : Prop :=
  ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) [QueryMachine.IsPolyQ E], Hypothesis K e C₀ kf num E →
    ∃ n₀ : ℕ, ∀ n₁ : ℕ, n₀ ≤ n₁ →
      (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
        PairsToBound.Computes M (RecursionToBound.count (solverOfMachine E num C₀) n₁ (pickOf kf (K 0)) (cutFraction num)) (RecursionToBound.expo (solverOfMachine E num C₀) n₁ (pickOf kf (K 0)) (cutFraction num)) q) ∧
      ∀ (M : TM2ComputableAux Bool Bool) (q : ℕ),
        PairsToBound.Computes M (RecursionToBound.count (solverOfMachine E num C₀) n₁ (pickOf kf (K 0)) (cutFraction num)) (RecursionToBound.expo (solverOfMachine E num C₀) n₁ (pickOf kf (K 0)) (cutFraction num)) q →
          ∃ C' : ℕ, Conclusion K e M C'
def PartAForEveryMachineFrom : Prop := SolverOfMachineLevels → RecursionToBound.ThmVariablesAForEveryMachine → PartAForEveryMachine
def PartAFromEveryMachine : Prop := PartAForEveryMachine → PartA
def SolverFromMachine : Prop :=
  ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ) (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ),
    Hypothesis K e C₀ kf num E → ∃ (Idx : Type) (_ : Enc Idx) (S : Solver Idx) (C₀' : ℕ) (Q : S.Seq (cutNumber K num) C₀'), S.Poly ∧ ∀ l : ℕ, S.K (Q.idx l) = K l
def BoundAtANumberBetween : Prop :=
  ∀ (C k n : ℕ) (e e' : ℝ), 1 ≤ k → 0 < e → e ≤ e' → e' ≤ 2 * e → e' ≤ 1 → timeVariablesA C k n e' ≤ timeVariablesA (2 * C) k n e
def PartAFromThePaddingString : Prop := SolverFromMachine → RecursionToBound.ThmVariablesAWithNumberBetween → PartA
end ThmVariables


