-- Prove2me | Definitions.Def_Complement_Defs
-- name    : Complement_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:31:14.201902+00:00
-- url     : https://prove2.me/theorems/0669c235-bf6e-44a3-be7d-fda925d6b50e
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SizeCircuit_Defs
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems
def StCliques : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), (∀ S : Finset (Fin n), G.IsNClique s S ↔ Gᶜ.IsNIndepSet s S) ∧ numCliques G s = numIndepSets Gᶜ s
def StCovers : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
  (∀ S : Finset (Fin n), (G.IsVertexCover (S : Set (Fin n)) ∧ S.card = s) ↔ G.IsNIndepSet (n - s) Sᶜ) ∧ numVertexCovers G s = numIndepSets G (n - s)
def complMatrix (n : ℕ) (m : List Bool) : List Bool := (pairs n).map fun p => p.1 != p.2 && !adjB n m p.1 p.2
def StComplMatrix : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)), complMatrix n (matrix G) = matrix Gᶜ
def StComplCert : Prop := PolyT fun a : List Unit × List Bool => complMatrix a.1.length a.2
def readClique (x : List Bool) : List Unit × ℕ × Fml := ((read2 x).1, (read2 x).2.1, indepF (read2 x).1.length (complMatrix (read2 x).1.length (read2 x).2.2))
def readCover (x : List Bool) : List Unit × ℕ × Fml := ((read2 x).1, (read2 x).1.length - (read2 x).2.1, indepF (read2 x).1.length (read2 x).2.2)
def StReaders : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
  (readClique (codeWith G s) = (List.replicate n (), s, indepF n (matrix Gᶜ)) ∧ cntS n s (indepF n (matrix Gᶜ)) = numCliques G s) ∧
  (readCover (codeWith G s) = (List.replicate n (), n - s, indepF n (matrix G)) ∧ cntS n (n - s) (indepF n (matrix G)) = numVertexCovers G s)
def StReadersCert : Prop := PolyT readClique ∧ PolyT readCover
def StCounts : Prop := ∀ (Z : Stepped (List Unit × ℕ × Fml) ℕ) (δ : ℝ) (c : ℕ),
  (∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped 2 n ψ → ∃ T : ℕ, Z.Runs (List.replicate n (), s, ψ) T (c * (n + ψ.length + 2) ^ c) (cntS n s ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) →
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
    (∃ T : ℕ, (Stepped.mapIn readClique Z).Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (numCliques G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) ∧
    (∃ T : ℕ, (Stepped.mapIn readCover Z).Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (numVertexCovers G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n))
def StIndepAlone : Prop := PolyT (fun a : List Unit × List Bool => indepF a.1.length a.2) ∧ ∀ (n : ℕ) (m : List Bool), Shaped 2 n (indepF n m) ∧ (indepF n m).length ≤ n * n
def StFromSized : Prop := StSized → ∀ δ : ℝ, 0 < δ → ∃ Z : Stepped (List Unit × ℕ × Fml) ℕ,
  Nonempty (IsPolyT (Stepped.mapIn readClique Z)) ∧ Nonempty (IsPolyT (Stepped.mapIn readCover Z)) ∧ ∃ c : ℕ,
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
    (∃ T : ℕ, (Stepped.mapIn readClique Z).Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (numCliques G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) ∧
    (∃ T : ℕ, (Stepped.mapIn readCover Z).Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (numVertexCovers G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n))
def StFromGamma : Prop := ∀ (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (a : ℕ), SizeCircuit.TestsSize gates a →
  ∀ (δ δE : ℝ), 0 < δ → 0 ≤ δE → δE * ((a : ℝ) + 1) ≤ δ →
  ∀ (E : Stepped (List Unit × Fml) (List Bool)) (c : ℕ), Eight.Serves E (max 2 3) δE c →
  ∃ c' : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
    (∃ T : ℕ, (Stepped.mapIn (readF indepF) (SizeCircuit.sizedBy gates E)).Runs (codeWith G s) T (c' * (n + n * n + 2) ^ c') (numIndepSets G s) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n)) ∧
    (∃ T : ℕ, (Stepped.mapIn readClique (SizeCircuit.sizedBy gates E)).Runs (codeWith G s) T (c' * (n + n * n + 2) ^ c') (numCliques G s) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n)) ∧
    (∃ T : ℕ, (Stepped.mapIn readCover (SizeCircuit.sizedBy gates E)).Runs (codeWith G s) T (c' * (n + n * n + 2) ^ c') (numVertexCovers G s) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n))
def StOnTuringMachines : Prop := StSized → ∀ δ : ℝ, 0 < δ →
  CountsInTime (fun _ G s => numCliques G s) δ ∧ CountsInTime (fun _ G s => numVertexCovers G s) δ ∧
  DecidesInTime (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ ∧
  DecidesInTime (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ
end Complement


