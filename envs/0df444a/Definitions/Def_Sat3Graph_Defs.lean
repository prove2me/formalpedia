-- Prove2me | Definitions.Def_Sat3Graph_Defs
-- name    : Sat3Graph_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:36:11.351853+00:00
-- url     : https://prove2.me/theorems/be0c5b3e-33ea-4462-b9a8-a10f42609bf6
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_Complement_Defs
import Definitions.Def_SplitSat_Defs
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_GraphProblems_ColorTM
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement SplitSat
def askSized (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (D : StepMachine (List Unit × Fml) Bool) : StepMachine (List Unit × ℕ × Fml) Bool :=
  Stepped.mapIn (fun p => widthP (withGamma gates p)) D
def StAskSized : Prop := ∀ (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (a : ℕ), TestsSize gates a → ∀ (w B : ℕ) (δ δ₃ : ℝ), 0 < δ → 0 ≤ δ₃ → δ₃ * ((a : ℝ) + 1 + B) ≤ δ →
  ∀ (D : StepMachine (List Unit × Fml) Bool) (c : ℕ), Decides3 D δ₃ c →
  ∃ c' : ℕ, ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped w n ψ → (w - 3) * ψ.length ≤ B * (n + 1) →
    ∃ (T : ℕ) (b : Bool), (askSized gates D).Runs (List.replicate n (), s, ψ) T (c' * (n + 2) ^ c') b ∧ (b = true ↔ cntS n s ψ ≠ 0) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n)
def DecidesGraph (Ms : StepMachine (List Bool) Bool) (p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop) (δ : ℝ) (c : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ (T : ℕ) (b : Bool), Ms.Runs (codeWith G s) T (c * (n + 2) ^ c) b ∧ (b = true ↔ p n G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
def INDEP (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (D : StepMachine (List Unit × Fml) Bool) : StepMachine (List Bool) Bool := Stepped.mapIn (readF indepF) (askSized gates D)
def CLIQUE (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (D : StepMachine (List Unit × Fml) Bool) : StepMachine (List Bool) Bool := Stepped.mapIn readClique (askSized gates D)
def COVER (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (D : StepMachine (List Unit × Fml) Bool) : StepMachine (List Bool) Bool := Stepped.mapIn readCover (askSized gates D)
def DOM (w : ℕ) (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (D : StepMachine (List Unit × Fml) Bool) : StepMachine (List Bool) Bool :=
  Stepped.mapIn read2 (Stepped.walk (stepD w) rootD (Stepped.mapIn leafD (askSized gates D)))
def COLOR (k : ℕ) (D : StepMachine (List Unit × Fml) Bool) : StepMachine (List Bool) Bool := Stepped.mapIn (fun x => widthP (readC k x)) D
def StSets : Prop := ∀ (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (a : ℕ), TestsSize gates a → ∀ (δ δ₃ : ℝ), 0 < δ → 0 ≤ δ₃ → δ₃ * ((a : ℝ) + 1) ≤ δ →
  ∀ (D : StepMachine (List Unit × Fml) Bool) (c : ℕ), Decides3 D δ₃ c → ∃ c' : ℕ,
    DecidesGraph (INDEP gates D) (fun n G s => ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) δ c' ∧
    DecidesGraph (CLIQUE gates D) (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ c' ∧
    DecidesGraph (COVER gates D) (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ c'
def StDominating : Prop := ∀ (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (a : ℕ), TestsSize gates a → ∀ (w : ℕ) (δ δ₃ : ℝ), 0 < δ → 0 ≤ δ₃ → ShortensD w (δ / 2) → δ₃ * ((a : ℝ) + 1 + 3 * ((w - 3 : ℕ) : ℝ)) ≤ δ / 2 →
  ∀ (D : StepMachine (List Unit × Fml) Bool) (c : ℕ), Decides3 D δ₃ c → ∃ c' : ℕ,
    DecidesGraph (DOM w gates D) (fun n G s => ∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) δ c'
def StColoring : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ (δ δ₃ : ℝ), 0 < δ → 0 ≤ δ₃ → δ₃ * (2 * (k : ℝ) - 3) ≤ δ →
  ∀ (D : StepMachine (List Unit × Fml) Bool) (c : ℕ), Decides3 D δ₃ c → ∃ c' : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∃ (T : ℕ) (b : Bool), (COLOR k D).Runs (code G) T (c' * (n + 2) ^ c') b ∧ (b = true ↔ G.Colorable k) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n)
def StCert : Prop := ∀ (gates : ℕ → ℕ → List CircuitLowerBound.GateD), CertGates gates → ∀ D : StepMachine (List Unit × Fml) Bool, PolyTimeSteps D →
  PolyTimeSteps (INDEP gates D) ∧ PolyTimeSteps (CLIQUE gates D) ∧ PolyTimeSteps (COVER gates D) ∧ (∀ w : ℕ, PolyTimeSteps (DOM w gates D)) ∧ ∀ k : ℕ, PolyTimeSteps (COLOR k D)
def HostedFor (Ms : StepMachine (List Bool) Bool) (p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop) (δ : ℝ) : Prop :=
  ∃ (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Simulates M Ms q ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ b : Bool, (b = true ↔ p n G s) ∧ Outputs M (codeWith G s) [b] ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
end Sat3Graph


