-- Prove2me | Definitions.Def_NamesInOrder_Defs
-- name    : NamesInOrder_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:59:20.205915+00:00
-- url     : https://prove2.me/theorems/90cb84b3-5c2b-4a6d-8f7e-85732a176bdb
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_GeneralDefs
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace NamesInOrder
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound MainRoute
open Sat3 (CNF)
def VariablesAreFew : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), SatK.IsKCNF k φ → SatM.AllOccur φ → n ≤ k * φ.length
def CodeIsShort : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
    (SatM.enc k φ).length = k + n + 2 + φ.length * (k * (Nat.log2 (2 * n) + 1)) ∧
    (SatM.AllOccur φ → (SatM.enc k φ).length ≤ 6 * (k * φ.length) ^ 2) ∧
    (SatM.enc k φ).length ≤ k * (2 * n + 1) ^ (k + 3)
def PolynomialIsBelowTheBoundInM : Prop :=
  ∀ c : ℕ, ∃ c' : ℕ, ∀ k m : ℕ, 1 ≤ k → 2 ≤ m → c * (6 * (k * m) ^ 2) ^ c ≤ timeM c' k m
def PolynomialIsBelowTheBoundInN : Prop :=
  ∀ c : ℕ, ∃ c' : ℕ, ∀ k n : ℕ, 1 ≤ k → 4 ≤ n → c * (k * (2 * n + 1) ^ (k + 3)) ^ c ≤ timeN c' k n
def PolynomialIsBelowTheBound : Prop :=
  ∀ c : ℕ, ∃ c' : ℕ, ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ n → SatM.AllOccur φ →
    c * (SatM.enc k φ).length ^ c ≤ timeMin c' k φ.length n
def AlternationCostGoesIntoC : Prop :=
  ∀ C₁ C₂ q : ℕ, ∃ C : ℕ, ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ n → SatM.AllOccur φ →
    q * (min (timeM C₁ k φ.length) (timeN C₂ k n) + (SatM.enc k φ).length + 1) ^ q ≤ timeMin C k φ.length n
def MeetsBoundInMAlone (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → SatM.AllOccur φ → CountsWithin M k φ (timeM C k φ.length)
def BoundInMWithoutThePolynomial : Prop :=
  ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), MeetsBoundInM M C → ∃ C' : ℕ, MeetsBoundInMAlone M C'
def EveryDirectAlternationMeetsTheBound : Prop :=
  ∀ (M₁ : TM2ComputableAux Bool Bool) (C₁ : ℕ), MeetsBoundInMAlone M₁ C₁ → ∀ (M₂ : TM2ComputableAux Bool Bool) (C₂ : ℕ), ThmVariablesBFor M₂ C₂ →
    ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Alternates M₁ M₂ id id id id N q → ∃ C : ℕ, CorMinFor N C ∧ MainTheoremFor N C
def AssembledDirectly (fa : List Bool × U → List Bool) (ea : List Bool → ℕ) (fm : List Bool × U → List Bool) (em : List Bool → ℕ) (K₀ : ℕ) (N : TM2ComputableAux Bool Bool) : Prop :=
  ∃ (M₁ M₂ : TM2ComputableAux Bool Bool) (q₁ q : ℕ), ChosenAsPrinted fa ea K₀ M₂ ∧ Computes M₁ fm em q₁ ∧ Alternates M₁ M₂ id id id id N q
def BuiltDirectly (fa : List Bool × U → List Bool) (ea : List Bool → ℕ) (fm : List Bool × U → List Bool) (em : List Bool → ℕ) (K₀ : ℕ) (N : TM2ComputableAux Bool Bool) : Prop :=
  ∃ (Ma Mb M₂ M₁ : TM2ComputableAux Bool Bool) (qa qb q₂ q₂' q₁ q q' : ℕ) (pre : List Bool → List Bool) (test : List Bool → Bool) (Ka : Coding Ma) (Kb : Coding Mb) (K₁ : Coding M₁) (K₂ : Coding M₂),
    (∀ i, Finite (Ma.tm.Γ i)) ∧ (∀ i, Finite (Mb.tm.Γ i)) ∧ (∀ i, Finite (M₂.tm.Γ i)) ∧ (∀ i, Finite (M₁.tm.Γ i)) ∧ (∀ i, Finite (N.tm.Γ i)) ∧
    PolyT pre ∧ PolyT test ∧
    Computes Ma fa ea qa ∧ Computes Mb exhaust (fun x => (fmlOf x).1.length) qb ∧
    RewritesAtWidthOr3 pre ∧ TestsTheMainRegime K₀ test ∧ Hosts (choose Ka Kb test pre id id id) M₂ q₂' ∧ Chooses Ma Mb test pre id id id M₂ q₂ ∧
    Computes M₁ fm em q₁ ∧ Hosts (alt K₁ K₂ id id id id) N q' ∧ Alternates M₁ M₂ id id id id N q
def BuiltIsAssembledDirectly : Prop :=
  ∀ (fa : List Bool × U → List Bool) (ea : List Bool → ℕ) (fm : List Bool × U → List Bool) (em : List Bool → ℕ) (K₀ : ℕ) (N : TM2ComputableAux Bool Bool),
    BuiltDirectly fa ea fm em K₀ N → AssembledDirectly fa ea fm em K₀ N ∧ ∀ i, Finite (N.tm.Γ i)
def OnEverySolver : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ n₀ : ℕ, ∀ a : ℕ, (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) → ∀ n₁ : ℕ, n₀ ≤ n₁ →
      (∀ (M₁ : TM2ComputableAux Bool Bool) (q₁ : ℕ), Computes M₁ (AM S Q.pick) (eM S Q.pick) q₁ → ∃ C₁ : ℕ, MeetsBoundInMAlone M₁ C₁) ∧
      (∀ N : TM2ComputableAux Bool Bool, AssembledDirectly (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) (AM S Q.pick) (eM S Q.pick) (S.K (Q.idx 0)) N → ∃ C : ℕ, CorMinFor N C ∧ MainTheoremFor N C) ∧
      ∃ N : TM2ComputableAux Bool Bool, BuiltDirectly (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) (AM S Q.pick) (eM S Q.pick) (S.K (Q.idx 0)) N
def ForAllPieces : Prop :=
  ∀ (c : ℕ) (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), GeneralPieces.Tied.IsPiecesB c P₀ A val → ∃ n₀ : ℕ, ∀ n₁ : ℕ, n₀ ≤ n₁ →
    (∀ (M₁ : TM2ComputableAux Bool Bool) (q₁ : ℕ), Computes M₁ (fnM c P₀ val) (padExpM c P₀ val) q₁ → ∃ C₁ : ℕ, MeetsBoundInMAlone M₁ C₁) ∧
    (∀ N : TM2ComputableAux Bool Bool, AssembledDirectly (fnN c P₀ val n₁) (padExpN c P₀ val n₁) (fnM c P₀ val) (padExpM c P₀ val) (Levels.Gen.K (GeneralPieces.x₀Of c) 0) N → ∃ C : ℕ, CorMinFor N C ∧ MainTheoremFor N C) ∧
    ∃ N : TM2ComputableAux Bool Bool, BuiltDirectly (fnN c P₀ val n₁) (padExpN c P₀ val n₁) (fnM c P₀ val) (padExpM c P₀ val) (Levels.Gen.K (GeneralPieces.x₀Of c) 0) N
def MainTheoremHolds : Prop := MainTheoremAllOccur
def BoundInMHolds : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ MeetsBoundInMAlone M C
def CorMinHolds : Prop := CorMinAllOccur
def GeneralFormFollows : Prop :=
  ∀ (N : TM2ComputableAux Bool Bool) (C : ℕ), MainTheoremFor N C → ∀ ren : List Bool → List Bool, RenamesTheVariablesThatOccur ren →
    ∀ (N' : TM2ComputableAux Bool Bool) (q : ℕ), Wraps N ren id N' q → ∃ C' : ℕ, MeetsMinBound N' C' ∧ CountsCompactKCNFWithinMinBound N' C'
def GeneralFormFollowsAsPropositions : Prop := MainTheoremAllOccur → MainTheoremCompact
end NamesInOrder


