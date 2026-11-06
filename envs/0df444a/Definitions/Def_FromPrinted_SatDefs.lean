-- Prove2me | Definitions.Def_FromPrinted_SatDefs
-- name    : FromPrinted_SatDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:51:40.26856+00:00
-- url     : https://prove2.me/theorems/2c67ef1b-e8e3-4146-ae9a-a11d0944433d
-- title:
--   Sat Defs
-- statement:
--   Definitions and structural lemmas for Sat Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SatDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_SplitSat_Defs
import Definitions.Def_FreeCode_Defs
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Consequences_Defs
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight Eight.ViaGrouping Eight.Width SplitSat
namespace FromPrinted.SplitSat
def core3 (ℓ τ : ℕ) : StepMachine (List Unit × Fml) Bool :=
  Stepped.ite (fun p => hasNil p.2) (Stepped.const false) (Exits.walkUntil (Enumerate.rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut (Printed.COUNT ℓ) posZ)))
def StCore3Eq : Prop := ∀ ℓ τ : ℕ, Printed.SAT ℓ τ = Stepped.mapIn (decU 3) (core3 ℓ τ)
def StCore3 : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (core3 ℓ τ) ∧ ∃ c : ℕ, Decides3 (core3 ℓ τ) δ c
def SATsplit (k τ ℓ₃ τ₃ : ℕ) : StepMachine (List Bool) Bool := REDUCE k τ (core3 ℓ₃ τ₃)
def StSATsplit : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ τ ℓ₃ τ₃ : ℕ, PolyTimeSteps (SATsplit k τ ℓ₃ τ₃) ∧ ∃ c : ℕ, Decides (SATsplit k τ ℓ₃ τ₃) k δ c
def StTiedTM : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (τ ℓ₃ τ₃ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (SATsplit k τ ℓ₃ τ₃) ∧ Decides (SATsplit k τ ℓ₃ τ₃) k δ c ∧
  Simulates M (SATsplit k τ ℓ₃ τ₃) q ∧
  SatK.DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
def StTiedThreeTM : Prop := ∀ δ : ℝ, 0 < δ → ∃ (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Printed.SAT ℓ τ) ∧ Decides (Printed.SAT ℓ τ) 3 δ c ∧ Simulates M (Printed.SAT ℓ τ) q ∧ SatK.DecidesTM 3 M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
abbrev ThreeSatStatement : Prop := PaperSentences.CorEth
end FromPrinted.SplitSat
end
section
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper FreeCode
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
namespace FromPrinted.FreeCode
def StTiedThree : Prop := ∀ δ : ℝ, 0 < δ → ∃ (dec : List Bool → List Unit × Fml) (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec (core3 ℓ τ)) ∧ DecidesFree (Stepped.mapIn dec (core3 ℓ τ)) 3 δ c ∧
  Simulates M (Stepped.mapIn dec (core3 ℓ τ)) q ∧ SatFree.DecidesTM 3 M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
def StTied : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (dec : List Bool → List Unit × Fml) (τ ℓ₃ τ₃ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) ∧ DecidesFree (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) k δ c ∧
  Simulates M (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) q ∧ SatFree.DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
end FromPrinted.FreeCode
end
section
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement Sat3Graph
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
namespace FromPrinted.Sat3Graph
def StWithThreeSatMachine : Prop := ∀ (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (a : ℕ), TestsSize gates a → CertGates gates → ∀ (δ : ℝ), 0 < δ → ∀ k : ℕ, 3 ≤ k → ∃ ℓ τ w c : ℕ,
  (PolyTimeSteps (INDEP gates (core3 ℓ τ)) ∧ PolyTimeSteps (CLIQUE gates (core3 ℓ τ)) ∧ PolyTimeSteps (COVER gates (core3 ℓ τ)) ∧
    PolyTimeSteps (DOM w gates (core3 ℓ τ)) ∧ PolyTimeSteps (COLOR k (core3 ℓ τ))) ∧
  DecidesGraph (INDEP gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) δ c ∧
  DecidesGraph (CLIQUE gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ c ∧
  DecidesGraph (COVER gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ c ∧
  DecidesGraph (DOM w gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) δ c ∧
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ (T : ℕ) (b : Bool), (COLOR k (core3 ℓ τ)).Runs (code G) T (c * (n + 2) ^ c) b ∧ (b = true ↔ G.Colorable k) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
def StTiedTM : Prop := ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k → ∃ (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (a ℓ τ w c : ℕ), TestsSize gates a ∧ CertGates gates ∧
  (PolyTimeSteps (INDEP gates (core3 ℓ τ)) ∧ DecidesGraph (INDEP gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) δ c ∧
    HostedFor (INDEP gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) δ) ∧
  (PolyTimeSteps (CLIQUE gates (core3 ℓ τ)) ∧ DecidesGraph (CLIQUE gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ c ∧
    HostedFor (CLIQUE gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ) ∧
  (PolyTimeSteps (COVER gates (core3 ℓ τ)) ∧ DecidesGraph (COVER gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ c ∧
    HostedFor (COVER gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ) ∧
  (PolyTimeSteps (DOM w gates (core3 ℓ τ)) ∧ DecidesGraph (DOM w gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) δ c ∧
    HostedFor (DOM w gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) δ) ∧
  (PolyTimeSteps (COLOR k (core3 ℓ τ)) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ (T : ℕ) (b : Bool), (COLOR k (core3 ℓ τ)).Runs (code G) T (c * (n + 2) ^ c) b ∧ (b = true ↔ G.Colorable k) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) ∧
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Simulates M (COLOR k (core3 ℓ τ)) q ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ b : Bool, (b = true ↔ G.Colorable k) ∧ Outputs M (code G) [b] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊)
abbrev ThreeSatStatement : Prop := GraphProblems.CorGraphsDecide
end FromPrinted.Sat3Graph
end
section
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SizeCircuit Complement
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
namespace FromPrinted.Consequences
def StVerifier : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ τ ℓ₃ τ₃ c : ℕ,
  PolyTimeSteps (SATsplit k τ ℓ₃ τ₃) ∧ Decides (SATsplit k τ ℓ₃ τ₃) k δ c ∧ PolyTimeSteps (verifier (SATsplit k τ ℓ₃ τ₃)) ∧
  ∀ (n : ℕ) (ψ : Eight.DNF n), Eight.IsKDNF k ψ → ∀ w : List Bool,
    ∃ (T : ℕ) (b : Bool), (verifier (SATsplit k τ ℓ₃ τ₃)).Runs (Eight.withWitness w (SatK.enc k ψ)) T (c * ((SatK.enc k ψ).length + 1) ^ c) [b] ∧
      (b = true ↔ Eight.Tautology ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
def SATsmall (k ℓ τ : ℕ) : StepMachine (List Bool) Bool := Stepped.mapIn (decU k) (core3 ℓ τ)
def StSmallWidths : Prop := ∀ (k : ℕ), 1 ≤ k → k ≤ 3 → ∀ δ : ℝ, 0 < δ → ∃ ℓ τ c : ℕ, PolyTimeSteps (SATsmall k ℓ τ) ∧ Decides (SATsmall k ℓ τ) k δ c
abbrev NsethFalse : Prop := ¬ Eight.NSETH_TM
end FromPrinted.Consequences
end


