-- Prove2me | Definitions.Def_FromPrinted_GraphDefs
-- name    : FromPrinted_GraphDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:48:37.871564+00:00
-- url     : https://prove2.me/theorems/d8602263-8151-41a1-86ca-11ee9fc75b67
-- title:
--   Graph Defs
-- statement:
--   Definitions and structural lemmas for Graph Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/GraphDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_CountDefs
import Definitions.Def_Consequences_Defs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Consequences
namespace FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount SizeCircuit Complement
def SIZED (w ℓ τ : ℕ) : StepMachine (List Unit × ℕ × Fml) ℕ := sizedBy sizeGates (ENGINEsplit (max w 3) ℓ τ)
def StSetsCounted : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ c : ℕ,
  (PolyTimeSteps (Stepped.mapIn (readF indepF) (SIZED 2 ℓ τ)) ∧ CountsGraph (Stepped.mapIn (readF indepF) (SIZED 2 ℓ τ)) (fun _ G s => numIndepSets G s) δ c) ∧
  (PolyTimeSteps (Stepped.mapIn readClique (SIZED 2 ℓ τ)) ∧ CountsGraph (Stepped.mapIn readClique (SIZED 2 ℓ τ)) (fun _ G s => numCliques G s) δ c) ∧
  (PolyTimeSteps (Stepped.mapIn readCover (SIZED 2 ℓ τ)) ∧ CountsGraph (Stepped.mapIn readCover (SIZED 2 ℓ τ)) (fun _ G s => numVertexCovers G s) δ c)
def DOMcount (w ℓ τ : ℕ) : StepMachine (List Bool) ℕ := Stepped.mapIn read2 (walkSum (stepD w) rootD (Stepped.mapIn leafD (SIZED w ℓ τ)))
def StDominatingCounted : Prop := ∀ δ : ℝ, 0 < δ → ∃ w ℓ τ c : ℕ, ShortensD w (δ / 2) ∧ PolyTimeSteps (DOMcount w ℓ τ) ∧ CountsGraph (DOMcount w ℓ τ) (fun _ G s => numDominatingSets G s) δ c
def StColoringsCounted : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ ℓ τ c : ℕ, PolyTimeSteps (Stepped.mapIn (readC k) (ENGINEsplit (max k 2) ℓ τ)) ∧
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ T : ℕ, (Stepped.mapIn (readC k) (ENGINEsplit (max k 2) ℓ τ)).Runs (code G) T (c * (n + 2) ^ c) (SatK.binary (n * k) (numColorings G k)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
def StAlgoRuns : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ c : ℕ, PolyTimeSteps (ENGINEsplit 3 ℓ τ) ∧
  ∀ (a₀ : ℕ) (g : CircuitLowerBound.MCode → ℕ) (F : (CircuitLowerBound.MCode × List Unit × ℕ) × List CircuitLowerBound.GateD → List Unit × ENP.Cnf) (fb : List Unit → Bool), CircuitLowerBound.Alg.FormOK a₀ g F → ∀ x : List Bool,
    ∃ (T : ℕ) (b : Bool), (CircuitLowerBound.Alg.algo (ENGINEsplit 3 ℓ τ) F fb).Runs x T (c * ((CircuitLowerBound.Alg.pre F fb x).1.length + 2) ^ c) b ∧ (b = true ↔ ¬ENP.Sat (CircuitLowerBound.Alg.pre F fb x).2) ∧
      (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * (CircuitLowerBound.Alg.pre F fb x).1.length)
abbrev GraphsByCounting : Prop := GraphProblems.CorGraphs
abbrev Circuits : Prop := ENP.CorCircuits ∧ ENP.CorCircuits' ∧ ENP.CorCircuitsInf
end FromPrinted.Consequences


