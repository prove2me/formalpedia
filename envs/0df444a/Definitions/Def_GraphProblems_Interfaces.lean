-- Prove2me | Definitions.Def_GraphProblems_Interfaces
-- name    : GraphProblems_Interfaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:52:25.601397+00:00
-- url     : https://prove2.me/theorems/b81943cb-a3cc-45cd-a5b3-2ed4157c2b42
-- title:
--   Interfaces
-- statement:
--   Definitions and structural lemmas for Interfaces, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Interfaces.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Defs
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_StepMachines_Math_SparsifyTree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
section
section
namespace GraphProblems
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
def Shaped (w N : ℕ) (ψ : Fml) : Prop := ∀ C ∈ ψ, C.length ≤ w ∧ ∀ l ∈ C, l.1 < N
def StRead1 : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)), read1 (code G) = (List.replicate n (), matrix G)
def StRead2 : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), read2 (codeWith G s) = (List.replicate n (), s, matrix G)
def StAdj : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (u v : Fin n), adjB n (matrix G) u v = true ↔ G.Adj u v
def StMatrixLength : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (matrix G).length = n * n
def StIndep : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), cntS n s (indepF n (matrix G)) = numIndepSets G s
def StDom : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), cntS n s (domF n (matrix G)) = numDominatingSets G s
def StColor : Prop := ∀ (k n : ℕ) (G : SimpleGraph (Fin n)), cntN (n * k) (colorF k n (matrix G)) = numColorings G k
def StShapeColor : Prop := ∀ (k n : ℕ) (m : List Bool), Shaped (max k 2) (n * k) (colorF k n m)
def StDecide : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
  ((∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) ↔ numIndepSets G s ≠ 0) ∧
  ((∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) ↔ numCliques G s ≠ 0) ∧
  ((∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) ↔ numVertexCovers G s ≠ 0) ∧
  ((∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) ↔ numDominatingSets G s ≠ 0)
def StDecideColor : Prop := ∀ (k n : ℕ) (G : SimpleGraph (Fin n)), G.Colorable k ↔ numColorings G k ≠ 0
def StSized : Prop := ∀ (w : ℕ) (δ : ℝ), 0 < δ → ∃ Z : Stepped (List Unit × ℕ × Fml) ℕ, Nonempty (IsPolyT Z) ∧ ∃ c : ℕ,
  ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped w n ψ →
    ∃ T : ℕ, Z.Runs (List.replicate n (), s, ψ) T (c * (n + ψ.length + 2) ^ c) (cntS n s ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
def ShortensD (w : ℕ) (ε : ℝ) : Prop := ∀ (n s : ℕ) (m : List Bool),
  ((leaves (stepD w) (2 * n) (rootD (List.replicate n (), s, m))).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
  (∀ x ∈ leaves (stepD w) (2 * n) (rootD (List.replicate n (), s, m)), stepD w x = none ∧ x.1 = (List.replicate n (), s) ∧
    Shaped w n (leafD x).2.2 ∧ (leafD x).2.2.length ≤ 3 * n) ∧
  cntS n s (domF n m) = ((leaves (stepD w) (2 * n) (rootD (List.replicate n (), s, m))).map fun x => cntS n s (leafD x).2.2).sum ∧
  ∀ i, ((round (stepD w))^[i] ([rootD (List.replicate n (), s, m)], [])).1.length ≤ 2 * n + 1 ∧
    ∀ x ∈ ((round (stepD w))^[i] ([rootD (List.replicate n (), s, m)], [])).1, x.1 = (List.replicate n (), s) ∧
      x.2.1.length ≤ n ∧ (∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) ∧ x.2.2.length ≤ 2 * n ∧ Shaped w n x.2.2
def StShortens : Prop := ∀ ε : ℝ, 0 < ε → ∃ w : ℕ, 1 ≤ w ∧ ShortensD w ε
def StCertRead : Prop := PolyT read1 ∧ PolyT read2
def StCertForm : Prop :=
  PolyT (fun a : List Unit × List Bool => indepF a.1.length a.2) ∧ PolyT (fun a : List Unit × List Bool => cliqueF a.1.length a.2) ∧
  PolyT (fun a : List Unit × List Bool => coverF a.1.length a.2) ∧ ∀ k : ℕ, PolyT (fun a : List Unit × List Bool => colorF k a.1.length a.2)
def StCertBlock : Prop := ∀ b : ℕ, PolyT fun p : (List Unit × ℕ × Fml) × ℕ => blockF b p.1.1.length p.1.2.1 p.2 p.1.2.2
def StCertDom : Prop := (∀ w : ℕ, PolyT (stepD w)) ∧ PolyT rootD ∧ PolyT leafD
end GraphProblems


