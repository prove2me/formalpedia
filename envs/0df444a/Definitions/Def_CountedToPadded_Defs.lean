-- Prove2me | Definitions.Def_CountedToPadded_Defs
-- name    : CountedToPadded_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:33:25.168652+00:00
-- url     : https://prove2.me/theorems/8da23bfc-ef13-4bd3-bd3b-a8eccdf71c7c
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CliqueLevelsStatement
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_PaddedDescent_F_Data
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace QueryMachines.Bridge
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels
section runFor
variable {α β : Type}
def stay (N : Stepped α β) (s : N.σ) : N.σ := if (N.out s).isSome then s else N.step s
def cutAt {γ : Type} [Enc γ] (room : ℕ) (x : Option γ) : Option γ := if len x ≤ room then x else none
def runFor (N : Stepped α β) [Enc N.σ] (fuel : U) (room : ℕ) (a : α) : Option β :=
  (fuel.foldl (fun (s : Option N.σ) _ => cutAt room (s.map (stay N))) (cutAt room (some (N.init a)))).bind N.out
end runFor
def RunForIsRight : Prop := ∀ (α β : Type) (N : Stepped α β) [Enc N.σ] [Carried N.σ] (a : α) (T S : ℕ) (b : β) (fuel : U) (room : ℕ),
  N.Runs a T S b → T ≤ fuel.length → 7 * S + 2 ≤ room → runFor N fuel room a = some b
def EveryWordIsCompared : Prop := ∀ (α : Type) [Enc α], PolyT fun p : U × α => decide (len p.2 ≤ p.1.length)
def RunForPoly : Prop := ∀ (α β : Type) [Enc α] [Enc β] (N : Stepped α β) [IsPolyT N], PolyT fun p : (U × U) × α => runFor N p.1.1 p.1.2.length p.2
def RunForPolyFrom : Prop := EveryWordIsCompared → RunForPoly
def entry (T : Tab) (x : TableQuery) : ℤ := (T.getD x.1 []).getD (ofWord x.2) 0
def lookup : Stepped (Tab × TableQuery) ℤ := Stepped.ofFun fun p => entry p.1 p.2
def bitsOfTables (T : Tab) : ℕ := (T.flatten.map fun z => z.natAbs.size).foldr max 1
def TablesValue : Prop := ∀ (K lam : ℕ) (T : Tab), 2 ≤ K → 1 ≤ lam → (clique K lam fun w z => entry T (w.val, z)).value = zval K (unary lam, T)
def BitsOfTablesFacts : Prop := ∀ (T : Tab), 1 ≤ bitsOfTables T ∧ (∀ x : TableQuery, |entry T x| < 2 ^ bitsOfTables T) ∧
  ∀ (K lam B : ℕ) (lu : U), WFe K lam B (lu, T) → bitsOfTables T ≤ B + 1
section solver
variable (M : QueryMachine TableQuery ℤ (U × U × U) ℤ)
def onTables : Stepped (Tab × (U × U × U)) ℤ := M.plug lookup
abbrev OnTablesState : Type := Tab × (M.σ ⊕ (M.σ × ((Tab × TableQuery) ⊕ ℤ)))
def ceilMul (a b n : ℕ) : ℕ := if b ≤ a then n else (a * n + b - 1) / b
def needOf (num : U × U → ℕ × ℕ) (C₀ : ℕ) (x : (U × U) × U × U) : ℕ :=
  ceilMul (num x.1).1 (num x.1).2 (x.1.2.length ^ 2 * x.2.1.length) + C₀ * x.1.2.length ^ 2 * Nat.size (x.1.2.length * (x.2.1.length + x.2.2.length + 1)) + 2
def solverOfMachine [QueryMachine.IsPolyQ M] (num : U × U → ℕ × ℕ) (C₀ : ℕ) : Solver (U × U) where
  K i := i.2.length
  run x := (@runFor _ _ (onTables M) (inferInstanceAs (Enc (OnTablesState M))) x.1 (7 * x.1.length + 14 * len x.2.2.2 + 2) (x.2.2.2, (x.2.1.1, x.2.2.1, unary (bitsOfTables x.2.2.2)))).getD 0
  need := needOf num C₀
  needC x := if needOf num C₀ x.2 ≤ x.1.length then some (needOf num C₀ x.2) else none
end solver
def pickOf (kf : U × U → Option U) (K₀ : ℕ) (b : U) : U × (U × U) :=
  ((List.range (b.length + 1)).filterMap fun l => (kf (b.take l, b)).map fun k => (b.take l, (b.take l, k))).getLast?.getD ([], ([], unary K₀))
def cutFraction (num : U × U → ℕ × ℕ) (p : U × U) : ℕ × ℕ := (min (num p).1 (num p).2, (num p).2)
def CutNumberFacts : Prop := ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (num : U × U → ℕ × ℕ), Levels K e C₀ → NumberBetween K e num →
  PolyT (cutFraction num) ∧ ∀ l : ℕ, 0 < cutNumber K num l ∧ e l ≤ cutNumber K num l ∧ cutNumber K num l ≤ 2 * e l ∧ cutNumber K num l ≤ 1 ∧
    ((cutFraction num (unary l, unary (K l))).1 : ℝ) / ((cutFraction num (unary l, unary (K l))).2 : ℝ) = cutNumber K num l
def PrecisionCarriesOver : Prop := ∀ (e e' : ℕ → ℝ) (slU : U → U) (C : ℕ), MainTheoremForms.Precision e slU C → (∀ l : ℕ, e l ≤ e' l ∧ e' l ≤ 2 * e l ∧ e' l ≤ 1) → MainTheoremForms.Precision e' slU (2 * C)
def NeedSuffices : Prop := ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (num : U × U → ℕ × ℕ), Levels K e C₀ → NumberBetween K e num → ∀ l lam B : ℕ, 1 ≤ lam →
  4 * bound (cutNumber K num l) (K l) C₀ lam (B + 1) ≤ (2 : ℝ) ^ needOf num C₀ ((unary l, unary (K l)), unary lam, unary B)
def NeedIsSmall : Prop := ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (num : U × U → ℕ × ℕ), Levels K e C₀ → NumberBetween K e num → ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
  (needOf num C₀ ((unary l, unary (K l)), unary lam, unary B) : ℝ) ≤
    cutNumber K num l * (K l : ℝ) ^ 2 * lam + ((2 * C₀ + 1 : ℕ) : ℝ) * (K l : ℝ) ^ 2 * Real.logb 2 (K l * (lam + B))
def SolverOfMachinePoly : Prop := ∀ (M : QueryMachine TableQuery ℤ (U × U × U) ℤ) [QueryMachine.IsPolyQ M] (num : U × U → ℕ × ℕ) (C₀ : ℕ), PolyT num → (solverOfMachine M num C₀).Poly
def SolverOfMachinePolyFrom : Prop := RunForPoly → SolverOfMachinePoly
def PickOfFacts : Prop := ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : U × U → Option U), Levels K e C₀ → ComputesLevels K kf →
  PolyT (pickOf kf (K 0)) ∧ ∀ b : U, (pickOf kf (K 0) b).2 = (unary (pickOf kf (K 0) b).1.length, unary (K (pickOf kf (K 0) b).1.length)) ∧
    (K 0 ≤ b.length → K (pickOf kf (K 0) b).1.length ≤ b.length) ∧ b.length < K ((pickOf kf (K 0) b).1.length + 1)
def SolverOfMachineLevels : Prop :=
  ∀ (M : QueryMachine TableQuery ℤ (U × U × U) ℤ) [QueryMachine.IsPolyQ M] (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : U × U → Option U) (num : U × U → ℕ × ℕ),
    Solves M K e C₀ → Levels K e C₀ → ComputesLevels K kf → NumberBetween K e num →
      (solverOfMachine M num C₀).Poly ∧
      ∃ Q : (solverOfMachine M num C₀).Seq (cutNumber K num) (2 * C₀ + 1),
        (∀ l : ℕ, Q.idx l = (unary l, unary (K l))) ∧ (∀ l : ℕ, (solverOfMachine M num C₀).K (Q.idx l) = K l) ∧ Q.pick = pickOf kf (K 0)
def SolverOfMachineLevelsFrom : Prop :=
  StPlug → RunForIsRight → TablesValue → BitsOfTablesFacts → CutNumberFacts → NeedSuffices → NeedIsSmall → SolverOfMachinePoly → PickOfFacts → SolverOfMachineLevels
end QueryMachines.Bridge


