-- Prove2me | Definitions.Def_Printed_Programs
-- name    : Printed_Programs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:29:58.057064+00:00
-- url     : https://prove2.me/theorems/70ac25f4-3787-4bc5-a55b-8e9b8767eb7b
-- title:
--   Programs
-- statement:
--   Definitions and structural lemmas for Programs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Programs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedStatement
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Value_Defs
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines
abbrev CliqueMachine : Type 1 := QueryMachine TableQuery ℤ (List Unit × List Unit) ℤ
abbrev NetMachine : Type 1 := QueryMachine NetQuery ℤ NetInput ℤ
def toTable (x : IQ) : TableQuery := (x.1, x.2.flatten)
def toLists (K lam : ℕ) (x : TableQuery) : IQ := (x.1, (List.range K).map fun u => if u = x.1 then [] else copyAt lam x.1 u x.2)
def askTable {C : Type} [HasSize C] : QueryMachine TableQuery ℤ (C × IQ) ℤ := QueryMachine.query fun x => toTable x.2
def bruteMachine (K : ℕ) : CliqueMachine :=
  QueryMachine.sumRange (bruteBound K fun c : List Unit × List Unit => c.1.length)
    (QueryMachine.prodRange (Function.const _ K) (QueryMachine.mapIn (bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC) askTable))
structure ProcsQ (Q A C : Type) : Type 1 where
  P : C → ℕ
  B : C → ℕ
  len : C → ℕ → ℕ
  cap : C → ℕ → ℕ → ℕ
  mem : QueryMachine Q A (C × WQ) Bool
  W : QueryMachine Q A (C × WQ) ℤ
  Ψ : QueryMachine Q A (C × PsiQ) ℤ
  f : QueryMachine Q A (C × FQ) ℤ
variable {Q A C : Type}
def ProcsQ.under (Np : ProcsQ Q A C) : Procs C :=
  { P := Np.P, B := Np.B, len := Np.len, cap := Np.cap, mem := Np.mem.toStepped, W := Np.W.toStepped, Ψ := Np.Ψ.toStepped, f := Np.f.toStepped }
def ProcsQ.close (Np : ProcsQ Q A C) (O : Q → Option A) : Procs C :=
  { P := Np.P, B := Np.B, len := Np.len, cap := Np.cap, mem := Np.mem.close O, W := Np.W.close O, Ψ := Np.Ψ.close O, f := Np.f.close O }
def dist {X Y : Type} (p : C × (X ⊕ Y)) : (C × X) ⊕ (C × Y) := match p.2 with | .inl x => .inl (p.1, x) | .inr y => .inr (p.1, y)
def ProcsQ.answer (Np : ProcsQ Q A C) : QueryMachine Q A (C × NetQuery) ℤ :=
  QueryMachine.branch dist (QueryMachine.mapOut Np.mem fun b => if b = true then 1 else 0) (QueryMachine.branch dist Np.W (QueryMachine.branch dist Np.Ψ Np.f))
def answerOf (Np : Procs C) : Stepped (C × NetQuery) ℤ :=
  Stepped.branch dist (Stepped.mapOut Np.mem fun b => if b = true then 1 else 0) (Stepped.branch dist Np.W (Stepped.branch dist Np.Ψ Np.f))
def inputOf (g : ℕ) (P B : ℕ) (len : ℕ → ℕ) (cap : ℕ → ℕ → ℕ) : NetInput :=
  ((unary P, unary B), ((List.range g).map fun a => unary (len a), (List.range g).map fun a => (List.range g).map fun b => if a = b then [] else unary (cap a b)))
def networkOn [HasSize C] (g : ℕ) (NM : NetMachine) (Np : ProcsQ Q A C) : QueryMachine Q A C ℤ :=
  QueryMachine.mapIn (fun c => (c, inputOf g (Np.P c) (Np.B c) (Np.len c) (Np.cap c))) (NM.subst Np.answer)
def networkOnSteps [HasSize C] (g : ℕ) (NM : NetMachine) (Np : Procs C) : Stepped C ℤ :=
  Stepped.mapIn (fun c => (c, inputOf g (Np.P c) (Np.B c) (Np.len c) (Np.cap c))) (NM.plug (answerOf Np))
section Table
variable [HasSize C] (K g : ℕ) (Np : ProcsQ Q A C)
def wQ : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (qW K g Np.under.toPaperNetwork) Np.mem) (QueryMachine.mapIn (qW K g Np.under.toPaperNetwork) Np.W)
def psiQ : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (qW K g Np.under.toPaperNetwork) Np.mem)
    (QueryMachine.gated (QueryMachine.mapIn (qMb K g Np.under) Np.mem) (QueryMachine.mapIn (qPsi K g Np.under) Np.Ψ))
def fQ : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (qW K g Np.under.toPaperNetwork) Np.mem) (QueryMachine.mapIn (qF K g Np.under.toPaperNetwork) Np.f)
def termQ : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ :=
  QueryMachine.ite (isOne K g) (QueryMachine.const 1) (QueryMachine.ite (isW g) (wQ K g Np) (QueryMachine.ite (isPsi K g) (psiQ K g Np) (fQ K g Np)))
def tableQ : QueryMachine Q A (X0 C) ℤ :=
  QueryMachine.ite (validB K g Np.under.toPaperNetwork) (QueryMachine.sumRange (nStates K g Np.under.toPaperNetwork) (QueryMachine.prodRange (nPairs g) (termQ K g Np))) (QueryMachine.const 0)
end Table
def asked : ProcsQ NetQuery ℤ NetInput where
  P c := c.1.1.length
  B c := c.1.2.length
  len c a := (c.2.1.getD a []).length
  cap c a b := ((c.2.2.getD a []).getD b []).length
  mem := QueryMachine.mapOut (QueryMachine.query fun x => Sum.inl x.2) fun v => decide (v ≠ 0)
  W := QueryMachine.query fun x => Sum.inr (Sum.inl x.2)
  Ψ := QueryMachine.query fun x => Sum.inr (Sum.inr (Sum.inl x.2))
  f := QueryMachine.query fun x => Sum.inr (Sum.inr (Sum.inr x.2))
def bitsOut (K g P B : ℕ) : ℕ := (2 * (g * P) + (K - 1)) / K + g ^ 2 * B
def groupingMachine (K g : ℕ) (M : CliqueMachine) : NetMachine :=
  QueryMachine.optBind (QueryMachine.lift (Exits.search K g asked.under))
    (QueryMachine.mapIn (fun cx : NetInput × ℕ => (cx, (unary (lamP K g asked.under cx), unary (bitsOut K g (asked.P cx.1) (asked.B cx.1)))))
      (M.subst (QueryMachine.mapIn (fun y : (NetInput × ℕ) × TableQuery => (y.1, toLists K (lamP K g asked.under y.1) y.2)) (tableQ K g asked))))
    zeroOf
def sideWQ {C : Type} [HasSize C] (g : ℕ) (tr : Bool) (lam : C → ℕ) : QueryMachine TableQuery ℤ ((C × ℕ) × WQ) ℤ :=
  QueryMachine.ite (sideChk g tr lam) (QueryMachine.prodRange (sideG g) (QueryMachine.mapIn (sideQuery g tr lam) askTable)) (QueryMachine.const 0)
def gridProcs (g : ℕ) (tr : Bool) : ProcsQ TableQuery ℤ ((List Unit × List Unit) × ℕ) where
  P c := g ^ 3 * c.1.1.length
  B c := g * c.1.2.length + g ^ 2 * c.1.1.length + 1
  len c _ := nMemb g g tr * (g * g) * c.1.1.length
  cap c a b := capG eightF g g tr 0 c.1.1.length c.2 a b
  mem := QueryMachine.lift (Stepped.mapIn (fun _ => ()) (Stepped.const true))
  W := sideWQ g tr fun c : List Unit × List Unit => c.1.length
  Ψ := QueryMachine.lift (Stepped.ofFun fun x => gridPsi g tr x.1.1.1.length x.1.2 x.2)
  f := QueryMachine.lift (Stepped.ofFun fun x => gridFf eightF [] g g tr 0 x.1.1.1.length x.1.2 x.2)
def levelMachine (K g : ℕ) (M : CliqueMachine) : CliqueMachine :=
  QueryMachine.bind
    (QueryMachine.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
      (QueryMachine.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOn g (groupingMachine K g M) (gridProcs g false)) (networkOn g (groupingMachine K g M) (gridProcs g true))))
    (QueryMachine.lift (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ)))
def CLIQUE : ℕ → CliqueMachine
  | 0 => bruteMachine (levelK 0)
  | ℓ + 1 => levelMachine (levelK ℓ) (levelG ℓ) (CLIQUE ℓ)
def NETWORK (ℓ : ℕ) : NetMachine := groupingMachine (levelK ℓ) (levelG ℓ) (CLIQUE ℓ)
def formulaProcs (g k : ℕ) : Procs Fml := { satProcs g k with B := fun _ => 1 }
def COUNT (ℓ : ℕ) : StepMachine Paper.Formula ℤ :=
  Stepped.ite (fun Φ : Paper.Formula => Φ.isEmpty) (Stepped.const 1) (networkOnSteps (levelG ℓ) (NETWORK ℓ) (formulaProcs (levelG ℓ) 3))
def SAT (ℓ τ : ℕ) : StepMachine (List Bool) Bool := Suffices.satLoop τ (COUNT ℓ)
def StBrute : Prop := ∀ K : ℕ, 2 ≤ K → (bruteMachine K).PolyTimeSteps ∧ ∃ Cc : ℕ, AchievedBy (bruteMachine K) Cc K (1 / 2)
def StEntryCost : Prop := ∀ K g : ℕ, ∃ c₁ : ℕ, ∀ (hK0 : 0 < K), 0 < g → ∀ (N : Net g) (P B τ : ℕ), N.Is P B → 1 ≤ τ →
  ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * L),
      (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K L (γ.val, Θ)) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (c₁ * (P + B) ^ c₁)
        ((Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x L).W γ Θ) ∧
      |(Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x L).W γ Θ| < 2 ^ bitsOut K g P B
def StGroupingTied : Prop := ∀ (K : ℕ) (e : ℝ) (M : CliqueMachine) (Cc : ℕ), 2 ≤ K → 0 ≤ e → AchievedBy M Cc K e →
  ∃ C₁ : ℕ, ComputesNetworks (groupingMachine K (3 * K ^ 8) M) C₁ (3 * K ^ 8) K e
def StGroupingTiedOf : Prop := Eight.ViaGrouping.StSearch → Exits.StSearchStops → StEntryCost → Value.StValueEqualsZ → QueryMachines.StSubst → StGroupingTied
def StGroupingPoly : Prop := ∀ (K g : ℕ) (M : CliqueMachine), M.PolyTimeSteps → (groupingMachine K g M).PolyTimeSteps
def StOnProcedures : Prop := ∀ (NM : NetMachine) (C₁ g K : ℕ) (e : ℝ), ComputesNetworks NM C₁ g K e →
  ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), SecNetworks.IsNetwork Np c N P B τ S →
    ∃ T : ℕ, (networkOnSteps g NM Np).Runs c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ
def StBothNetworks : Prop := ∀ g : ℕ, 1 ≤ g → ∃ a : ℕ, ∀ (tr : Bool) (lam B : ℕ) (W : ℕ → List Bool → ℤ) (y : ℕ), 1 ≤ lam → 1 ≤ B → (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) → y < (tOf lam + 1) ^ nRect g →
  (levelNetP g tr lam y fun w θ => W w.val (List.ofFn θ).flatten).Is (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) ∧
  inputOf g ((gridProcs g tr).P ((unary lam, unary B), y)) ((gridProcs g tr).B ((unary lam, unary B), y)) ((gridProcs g tr).len ((unary lam, unary B), y)) ((gridProcs g tr).cap ((unary lam, unary B), y))
    = netInput (levelNetP g tr lam y fun w θ => W w.val (List.ofFn θ).flatten) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) ∧
  ∀ (x : NetQuery) (v : ℤ), netOracle (levelNetP g tr lam y fun w θ => W w.val (List.ofFn θ).flatten) x = some v →
    (gridProcs g tr).answer.Within (tables (g * g) lam W) QueryMachine.unitCost (((unary lam, unary B), y), x) (a * (B + lam) ^ a) (a * (B + lam) ^ a) v
def StLevelTied : Prop := ∀ (K : ℕ) (e : ℝ) (M : CliqueMachine) (Cc : ℕ), 2 ≤ K → 0 ≤ e → AchievedBy M Cc K e →
  ∃ Cc' : ℕ, AchievedBy (levelMachine K (3 * K ^ 8) M) Cc' ((3 * K ^ 8) ^ 2) ((Eight.rho + 2 / K) * e + 2 / K)
def StLevelPoly : Prop := ∀ (K g : ℕ) (M : CliqueMachine), M.PolyTimeSteps → (levelMachine K g M).PolyTimeSteps
def StClique : Prop := ∀ ℓ : ℕ, (CLIQUE ℓ).PolyTimeSteps ∧ ∃ Cc : ℕ, AchievedBy (CLIQUE ℓ) Cc (levelK ℓ) (Level.levelE ℓ)
def StCountCost : Prop := ∀ (δ' : ℝ) (ℓ : ℕ), 0 < δ' → δ' ≤ 1 → 72 / δ' ≤ levelK ℓ → Level.levelE ℓ ≤ δ' / 12 →
  PolyTimeSteps (COUNT ℓ) ∧ ∃ A : ℕ, ∀ Φ : Paper.Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, (COUNT ℓ).Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)
def StAlgorithm : Prop := ∀ (δ : ℝ) (Mc τ : ℕ) (hδ' : 0 < δ / (3 * (Mc : ℝ))), 0 < δ → δ ≤ 1 → 1 ≤ Mc → Enumerate.Enumerates (δ / 3) Mc τ →
  PolyTimeSteps (SAT (Level.firstLevel hδ') τ) ∧ Paper.DecidesInSteps (SAT (Level.firstLevel hδ') τ) δ
def StDecides : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (SAT ℓ τ) ∧ Paper.DecidesInSteps (SAT ℓ τ) δ
def StProofNamed : Prop := ∀ (δ : ℝ) (Mc τ K : ℕ) (M : CliqueMachine) (Cc : ℕ), 0 < δ → δ ≤ 1 → 1 ≤ Mc → Enumerate.Enumerates (δ / 3) Mc τ → 72 / (δ / (3 * (Mc : ℝ))) ≤ K → M.PolyTimeSteps → AchievedBy M Cc K (δ / (3 * (Mc : ℝ)) / 12) →
  PolyTimeSteps (Suffices.satLoop τ (networkOnSteps (3 * K ^ 8) (groupingMachine K (3 * K ^ 8) M) (formulaProcs (3 * K ^ 8) 3))) ∧
    Paper.DecidesInSteps (Suffices.satLoop τ (networkOnSteps (3 * K ^ 8) (groupingMachine K (3 * K ^ 8) M) (formulaProcs (3 * K ^ 8) 3))) δ
structure EndStatements : Prop where
  mono : StMono
  half : StHalf
  answerEachQuery : StAnswerEachQuery
  groupingLemma : GroupingLemma
  levelProposition : LevelProposition
  eStarZero : EStarZero
  everyEta : StEveryEta
  clique : StClique
  enumeration : Enumerate.StEnumeration
  proofNamed : StProofNamed
  algorithm : StAlgorithm
  decides : StDecides
  through_eStar : Sat3.ThmEveryDelta
  by_algorithm : Sat3.ThmEveryDelta
end Printed


