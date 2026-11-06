-- Prove2me | Definitions.Def_SizeCircuit_Defs
-- name    : SizeCircuit_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:24:18.78177+00:00
-- url     : https://prove2.me/theorems/8fd28f00-04fd-4606-8996-9ec49d9395b5
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_Eight_Cor_Defs
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight
def gateClauses (i : ℕ) (g : GateD) : Fml :=
  [[(g.2.1, true), (g.2.2, true), (i, g.1.1)], [(g.2.1, true), (g.2.2, false), (i, g.1.2.1)],
   [(g.2.1, false), (g.2.2, true), (i, g.1.2.2.1)], [(g.2.1, false), (g.2.2, false), (i, g.1.2.2.2)]]
def wiresFormula (n : ℕ) (K : List GateD) : Fml := (K.zipIdx).flatMap fun gt => gateClauses (n + gt.2) gt.1
def formulaOf (n : ℕ) (K : List GateD) : Fml := wiresFormula n K ++ [[(n + K.length - 1, true)]]
def Holds (a : ℕ → Bool) (ψ : Fml) : Prop := ∀ C ∈ ψ, ∃ l ∈ C, a l.1 = l.2
def StForces : Prop := ∀ (a : ℕ → Bool) (i : ℕ) (g : GateD), (Holds a (gateClauses i g) ↔ a i = g.toGate.op (a g.2.1) (a g.2.2)) ∧ ∀ C ∈ gateClauses i g, C.length ≤ 3
def StUniqueExtension : Prop := ∀ (n : ℕ) (K : List GateD), WF n K → K ≠ [] → ∀ x : Fin n → Bool,
  (∃! b : Fin (n + K.length) → Bool, (∀ i : Fin n, b (Fin.castAdd K.length i) = x i) ∧ Holds (ext b) (wiresFormula n K)) ∧
  ∀ b : Fin (n + K.length) → Bool, (∀ i : Fin n, b (Fin.castAdd K.length i) = x i) → Holds (ext b) (wiresFormula n K) →
    ext b (n + K.length - 1) = ENP.eval (toC K) (List.ofFn x)
def TestsSize (gates : ℕ → ℕ → List GateD) (a : ℕ) : Prop := ∀ n s : ℕ, 1 ≤ n →
  gates n s ≠ [] ∧ (gates n s).length ≤ a * (n + 1) ∧ WF n (gates n s) ∧ ∀ x : List Bool, x.length = n → (ENP.eval (toC (gates n s)) x = true ↔ x.count true = s)
def CertGates (gates : ℕ → ℕ → List GateD) : Prop := PolyT fun p : List Unit × ℕ => gates p.1.length p.2
def gamma (gates : ℕ → ℕ → List GateD) (n s : ℕ) : Fml := if n = 0 then (if s = 0 then [] else [[]]) else formulaOf n (gates n s)
def numVars (gates : ℕ → ℕ → List GateD) (n s : ℕ) : ℕ := if n = 0 then 0 else n + (gates n s).length
def StGamma : Prop := ∀ (gates : ℕ → ℕ → List GateD) (a : ℕ), TestsSize gates a → ∀ n s : ℕ, 1 ≤ n →
  Shaped 3 (n + (gates n s).length) (formulaOf n (gates n s)) ∧ n + (gates n s).length ≤ (a + 1) * (n + 1) ∧ (formulaOf n (gates n s)).length ≤ 4 * a * (n + 1) + 1 ∧
  ∀ x : Fin n → Bool,
    ((Finset.univ.filter fun i => x i = true).card = s →
      ∃! b : Fin (n + (gates n s).length) → Bool, (∀ i : Fin n, b (Fin.castAdd (gates n s).length i) = x i) ∧ Holds (ext b) (formulaOf n (gates n s))) ∧
    ((Finset.univ.filter fun i => x i = true).card ≠ s →
      ¬∃ b : Fin (n + (gates n s).length) → Bool, (∀ i : Fin n, b (Fin.castAdd (gates n s).length i) = x i) ∧ Holds (ext b) (formulaOf n (gates n s)))
def StGammaCount : Prop := ∀ (gates : ℕ → ℕ → List GateD) (a : ℕ), TestsSize gates a → ∀ (n s : ℕ) (ψ : Fml), (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) →
  cntN (numVars gates n s) (ψ ++ gamma gates n s) = cntS n s ψ
def withGamma (gates : ℕ → ℕ → List GateD) (p : List Unit × ℕ × Fml) : List Unit × Fml :=
  (List.replicate (numVars gates p.1.length p.2.1) (), (p.2.2 ++ gamma gates p.1.length p.2.1).dedup)
def sizedBy (gates : ℕ → ℕ → List GateD) (E : Stepped (List Unit × Fml) (List Bool)) : Stepped (List Unit × ℕ × Fml) ℕ :=
  Stepped.mapOut (Stepped.mapIn (withGamma gates) E) ofWord
def StSizedBy : Prop := ∀ (gates : ℕ → ℕ → List GateD) (a : ℕ), TestsSize gates a → ∀ (w : ℕ) (δ δE : ℝ), 0 < δ → 0 ≤ δE → δE * ((a : ℝ) + 1) ≤ δ →
  ∀ (E : Stepped (List Unit × Fml) (List Bool)) (c : ℕ), Serves E (max w 3) δE c →
  ∃ c' : ℕ, ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped w n ψ →
    ∃ T : ℕ, (sizedBy gates E).Runs (List.replicate n (), s, ψ) T (c' * (n + ψ.length + 2) ^ c') (cntS n s ψ) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n)
def StSizedCert : Prop := ∀ (gates : ℕ → ℕ → List GateD), CertGates gates → ∀ (E : Stepped (List Unit × Fml) (List Bool)), Nonempty (IsPolyT E) → Nonempty (IsPolyT (sizedBy gates E))
def StCircuitExists : Prop := ∃ (gates : ℕ → ℕ → List GateD) (a : ℕ), TestsSize gates a ∧ CertGates gates
def StSizedFromEngine : Prop := StEngine → ∀ (gates : ℕ → ℕ → List GateD) (a : ℕ), TestsSize gates a → CertGates gates →
  ∀ (w : ℕ) (δ : ℝ), 0 < δ → ∃ (E : Stepped (List Unit × Fml) (List Bool)) (δE : ℝ) (c : ℕ),
    Nonempty (IsPolyT E) ∧ 0 ≤ δE ∧ δE * ((a : ℝ) + 1) ≤ δ ∧ Serves E (max w 3) δE c ∧ Nonempty (IsPolyT (sizedBy gates E)) ∧
    ∃ c' : ℕ, ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped w n ψ →
      ∃ T : ℕ, (sizedBy gates E).Runs (List.replicate n (), s, ψ) T (c' * (n + ψ.length + 2) ^ c') (cntS n s ψ) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n)
def StSizedFromEngines : Prop := ∀ En : ℕ → ℕ → ℕ → Stepped (List Unit × Fml) (List Bool), Eight.ViaGrouping.EngineCounts En →
  ∀ (gates : ℕ → ℕ → List GateD) (a : ℕ), TestsSize gates a → CertGates gates → ∀ (w : ℕ) (δ : ℝ), 0 < δ →
  ∃ ℓ τ : ℕ, Nonempty (IsPolyT (sizedBy gates (En (max w 3) ℓ τ))) ∧ ∃ c' : ℕ, ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped w n ψ →
    ∃ T : ℕ, (sizedBy gates (En (max w 3) ℓ τ)).Runs (List.replicate n (), s, ψ) T (c' * (n + ψ.length + 2) ^ c') (cntS n s ψ) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n)
def StSizedViaGamma : Prop := StEngine → StSized
end SizeCircuit


