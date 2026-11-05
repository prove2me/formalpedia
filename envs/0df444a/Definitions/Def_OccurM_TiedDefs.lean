-- Prove2me | Definitions.Def_OccurM_TiedDefs
-- name    : OccurM_TiedDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:36:07.076718+00:00
-- url     : https://prove2.me/theorems/86fe5d6e-6862-4521-b407-855791bbf171
-- title:
--   Tied Defs
-- statement:
--   Definitions and structural lemmas for Tied Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/TiedDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_GeneralPieces_Tied_BoundDefs
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Definitions.Def_Wrap_Defs
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur
open Sat3 (CNF)
def Prepares (pre : List Bool → List Bool) : Prop :=
  ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → ∃ ψ : CNF (numOcc φ), SatK.IsKCNF k ψ ∧ SatM.AllOccur ψ ∧ ψ.length = φ.length ∧
    SatK.numSat ψ = numSatOcc φ ∧ pre (encC k φ) = SatM.enc k ψ
def PreparesUnary (pre : List Bool → List Bool) : Prop :=
  ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → ∃ ψ : CNF (numOcc φ), SatK.IsKCNF k ψ ∧ SatM.AllOccur ψ ∧ ψ.length = φ.length ∧
    SatK.numSat ψ = numSatOcc φ ∧ pre (SatM.enc k φ) = SatM.enc k ψ
def PreparationStmt : Prop := Prepares VariableBound.Rename.rencC ∧ PolyT VariableBound.Rename.rencC ∧ PreparesUnary VariableBound.Rename.renc ∧ PolyT VariableBound.Rename.renc
def prepA {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (p : List Bool × U) : List Bool := AM S pick (VariableBound.Rename.rencC p.1, p.2)
def prepE {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (x : List Bool) : ℕ := eM S pick (VariableBound.Rename.rencC x)
structure TopOccur {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (α : ℝ) : Prop where
  /-- both functions are polynomial-time -/
  poly_A : PolyT (prepA S pick)
  poly_e : PolyT (prepE S pick)
  /-- the function returns the number of satisfying assignments, as assignments of the n variables
  that occur, in n + 1 bits, if the pad has 2^prepE units -/
  correct : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ prepE S pick (encC k φ) ≤ pad.length →
    prepA S pick (encC k φ, pad) = SatK.binary (numOcc φ) (numSatOcc φ)
  /-- the exponent is O(k·m/(log m)^α), the O not depending on k -/
  rate : ∃ G : ℕ, ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → (prepE S pick (encC k φ) : ℝ) ≤ G * expClauses α k φ.length
  /-- one machine computes, on every input x, the named function at (x, 2^{prepE x} units) within
  q·(|x| + 2^{prepE x} + 1)^q steps, and it counts within the printed bound -/
  machine : ∃ (M : TM2ComputableAux Bool Bool) (q C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    (∀ x : List Bool, Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
      (some ((prepA S pick (x, pad (prepE S pick x))).map M.outputAlphabet.invFun)) (q * (x.length + 2 ^ prepE S pick x + 1) ^ q))) ∧
    CountsFor α M C
def prepAUnary {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (p : List Bool × U) : List Bool := AM S pick (VariableBound.Rename.renc p.1, p.2)
def prepEUnary {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (x : List Bool) : ℕ := eM S pick (VariableBound.Rename.renc x)
structure TopOccurUnary {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (α : ℝ) : Prop where
  poly_A : PolyT (prepAUnary S pick)
  poly_e : PolyT (prepEUnary S pick)
  correct : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ prepEUnary S pick (SatM.enc k φ) ≤ pad.length →
    prepAUnary S pick (SatM.enc k φ, pad) = SatK.binary (numOcc φ) (numSatOcc φ)
  rate : ∃ G : ℕ, ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → (prepEUnary S pick (SatM.enc k φ) : ℝ) ≤ G * expClauses α k φ.length
  machine : ∃ (M : TM2ComputableAux Bool Bool) (q C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    (∀ x : List Bool, Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
      (some ((prepAUnary S pick (x, pad (prepEUnary S pick x))).map M.outputAlphabet.invFun)) (q * (x.length + 2 ^ prepEUnary S pick x + 1) ^ q))) ∧
    CountsUnaryFor α M C
def TopOccurOfTopStmt : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (α : ℝ), 0 ≤ α → α ≤ 1 →
  GeneralPieces.Tied.TopM S pick (SatM.rPow α) → TopOccur S pick α ∧ TopOccurUnary S pick α
def CountsFromPiecesTied : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces ρ c P A val →
  18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → TopOccur (solverOf (GeneralPieces.Tied.recOf P val c)) (Pick.pick (GeneralPieces.Tied.recOf P val c) x₀) (AppRunningTime.alpha' ρ) ∧
    TopOccurUnary (solverOf (GeneralPieces.Tied.recOf P val c)) (Pick.pick (GeneralPieces.Tied.recOf P val c) x₀) (AppRunningTime.alpha' ρ)
def BoundInClausesTied : Prop := ∃ (c : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), GeneralPieces.Tied.IsPiecesB c P A val ∧
  TopOccur (solverOf (GeneralPieces.Tied.recOf P val c)) (Pick.pick (GeneralPieces.Tied.recOf P val c) (GeneralPieces.x₀Of c)) (1 / 2) ∧
  TopOccurUnary (solverOf (GeneralPieces.Tied.recOf P val c)) (Pick.pick (GeneralPieces.Tied.recOf P val c) (GeneralPieces.x₀Of c)) (1 / 2)
def UntieStmt : Prop := (CountsFromPiecesTied → CountsFromPieces ∧ CountsUnaryFromPieces) ∧ (BoundInClausesTied → BoundInClauses)
def EveryWrapperCounts : Prop :=
  ∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ pre : List Bool → List Bool, Prepares pre → ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), SatM.CountsTM M (SatM.bound (SatM.rPow α) C) →
    ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wrap.Wraps M pre id N q → ∃ C' : ℕ, CountsFor α N C'
def EveryWrapperCountsUnary : Prop :=
  ∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ pre : List Bool → List Bool, PreparesUnary pre → ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), SatM.CountsTM M (SatM.bound (SatM.rPow α) C) →
    ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Wrap.Wraps M pre id N q → ∃ C' : ℕ, CountsUnaryFor α N C'
end OccurM


