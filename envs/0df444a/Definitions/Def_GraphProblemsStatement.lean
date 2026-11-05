-- Prove2me | Definitions.Def_GraphProblemsStatement
-- name    : GraphProblemsStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:40:40.317171+00:00
-- url     : https://prove2.me/theorems/c435c987-bdbe-420a-8d45-43d5151ff4e4
-- title:
--   Graph Problems Statement
-- statement:
--   Definitions and structural lemmas for Graph Problems Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/GraphProblemsStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Set.Card
set_option autoImplicit false
section
section
namespace GraphProblems
open Turing
variable {n : ℕ}
def unary (m : ℕ) : List Bool := List.replicate m true ++ [false]
open Classical in
/-- The n² entries of the adjacency matrix, row by row. -/
noncomputable def matrix (G : SimpleGraph (Fin n)) : List Bool :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => decide (G.Adj u v)
noncomputable def code (G : SimpleGraph (Fin n)) : List Bool := unary n ++ matrix G
noncomputable def codeWith (G : SimpleGraph (Fin n)) (s : ℕ) : List Bool := unary n ++ (unary s ++ matrix G)
def IsDominating (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop := ∀ v, v ∈ S ∨ ∃ u ∈ S, G.Adj v u
noncomputable def numIndepSets (G : SimpleGraph (Fin n)) (s : ℕ) : ℕ := {S : Finset (Fin n) | G.IsNIndepSet s S}.ncard
noncomputable def numCliques (G : SimpleGraph (Fin n)) (s : ℕ) : ℕ := {S : Finset (Fin n) | G.IsNClique s S}.ncard
noncomputable def numVertexCovers (G : SimpleGraph (Fin n)) (s : ℕ) : ℕ :=
  {S : Finset (Fin n) | G.IsVertexCover (S : Set (Fin n)) ∧ S.card = s}.ncard
noncomputable def numDominatingSets (G : SimpleGraph (Fin n)) (s : ℕ) : ℕ := {S : Finset (Fin n) | IsDominating G S ∧ S.card = s}.ncard
noncomputable def numColorings (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ := Nat.card (G.Coloring (Fin k))
def Outputs (M : TM2ComputableAux Bool Bool) (x y : List Bool) (T : ℕ) : Prop :=
  Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some (y.map M.outputAlphabet.invFun)) T)
def CountsInTime (f : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℕ) (δ : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → Outputs M (codeWith G s) (Nat.bits (f n G s)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
def DecidesInTime (p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop) (δ : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ b : Bool, (b = true ↔ p n G s) ∧ Outputs M (codeWith G s) [b] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
def CountsColoringsInTime (k : ℕ) (δ : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), Outputs M (code G) (Nat.bits (numColorings G k)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
def DecidesColoringInTime (k : ℕ) (δ : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ b : Bool, (b = true ↔ G.Colorable k) ∧ Outputs M (code G) [b] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
def CorGraphsCount : Prop := ∀ δ : ℝ, 0 < δ →
  CountsInTime (fun _ G s => numIndepSets G s) δ ∧
  CountsInTime (fun _ G s => numCliques G s) δ ∧
  CountsInTime (fun _ G s => numVertexCovers G s) δ ∧
  CountsInTime (fun _ G s => numDominatingSets G s) δ ∧
  ∀ k : ℕ, 3 ≤ k → CountsColoringsInTime k δ
def CorGraphsDecide : Prop := ∀ δ : ℝ, 0 < δ →
  DecidesInTime (fun n G s => ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) δ ∧
  DecidesInTime (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ ∧
  DecidesInTime (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ ∧
  DecidesInTime (fun n G s => ∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) δ ∧
  ∀ k : ℕ, 3 ≤ k → DecidesColoringInTime k δ
def CorGraphs : Prop := CorGraphsCount ∧ CorGraphsDecide
end GraphProblems


