-- Prove2me | Definitions.Def_MainRoute_Defs
-- name    : MainRoute_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:55:55.213717+00:00
-- url     : https://prove2.me/theorems/0edb05cc-32a9-46e5-811f-ff5a3d35a8c9
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_GeneralPieces_Tied_BoundDefs
import Definitions.Def_RecursionToBound_Defs
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace MainRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
section
variable (c : ℕ) (P₀ : PiecesF) (val : AppRunningTime.ValQ → ℤ) (n₁ : ℕ)
def fnN : List Bool × U → List Bool := RecursionToBound.count (RecursionWithPieces.solverAB P₀ val c) n₁ (RecursionWithPieces.pickAB P₀ val c) fractionHalf
def padExpN : List Bool → ℕ := RecursionToBound.expo (RecursionWithPieces.solverAB P₀ val c) n₁ (RecursionWithPieces.pickAB P₀ val c) fractionHalf
def fnM : List Bool × U → List Bool := AM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c)
def padExpM : List Bool → ℕ := eM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c)
end
def BoundInMForEveryMachine : Prop :=
  ∀ (c : ℕ) (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces (1 / Real.sqrt 2) c P₀ A val →
    (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Computes M (fnM c P₀ val) (padExpM c P₀ val) q) ∧
    ∀ (M : TM2ComputableAux Bool Bool) (q : ℕ), Computes M (fnM c P₀ val) (padExpM c P₀ val) q → ∃ C : ℕ, MeetsBoundInM M C
def ChosenAsPrinted (fa : List Bool × U → List Bool) (ea : List Bool → ℕ) (K₀ : ℕ) (M₂ : TM2ComputableAux Bool Bool) : Prop :=
  ∃ (Ma Mb : TM2ComputableAux Bool Bool) (qa qb q₂ : ℕ) (pre : List Bool → List Bool) (test : List Bool → Bool),
    Computes Ma fa ea qa ∧ Computes Mb exhaust (fun x => (fmlOf x).1.length) qb ∧
    RewritesAtWidthOr3 pre ∧ TestsTheMainRegime K₀ test ∧ Chooses Ma Mb test pre id id id M₂ q₂
def AssembledAsPrinted (fa : List Bool × U → List Bool) (ea : List Bool → ℕ) (fm : List Bool × U → List Bool) (em : List Bool → ℕ) (K₀ : ℕ) (post : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) : Prop :=
  ∃ (M₁ M₂ : TM2ComputableAux Bool Bool) (q₁ q : ℕ) (ren : List Bool → List Bool),
    ChosenAsPrinted fa ea K₀ M₂ ∧ Computes M₁ fm em q₁ ∧ RenamesTheVariablesThatOccur ren ∧ Alternates M₁ M₂ ren ren post post N q
def BuiltAsPrinted (fa : List Bool × U → List Bool) (ea : List Bool → ℕ) (fm : List Bool × U → List Bool) (em : List Bool → ℕ) (K₀ : ℕ) (post : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) : Prop :=
  ∃ (Ma Mb M₂ M₁ : TM2ComputableAux Bool Bool) (qa qb q₂ q₂' q₁ q q' : ℕ) (pre ren : List Bool → List Bool) (test : List Bool → Bool) (Ka : Coding Ma) (Kb : Coding Mb) (K₁ : Coding M₁) (K₂ : Coding M₂),
    (∀ i, Finite (Ma.tm.Γ i)) ∧ (∀ i, Finite (Mb.tm.Γ i)) ∧ (∀ i, Finite (M₂.tm.Γ i)) ∧ (∀ i, Finite (M₁.tm.Γ i)) ∧ (∀ i, Finite (N.tm.Γ i)) ∧
    PolyT pre ∧ PolyT test ∧ PolyT ren ∧
    Computes Ma fa ea qa ∧ Computes Mb exhaust (fun x => (fmlOf x).1.length) qb ∧
    RewritesAtWidthOr3 pre ∧ TestsTheMainRegime K₀ test ∧ Hosts (choose Ka Kb test pre id id id) M₂ q₂' ∧ Chooses Ma Mb test pre id id id M₂ q₂ ∧
    Computes M₁ fm em q₁ ∧ RenamesTheVariablesThatOccur ren ∧ Hosts (alt K₁ K₂ ren ren post post) N q' ∧ Alternates M₁ M₂ ren ren post post N q
end MainRoute


