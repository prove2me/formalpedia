-- Prove2me | Definitions.Def_FreeCode_Defs
-- name    : FreeCode_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:27:44.905121+00:00
-- url     : https://prove2.me/theorems/3f81e061-950c-4f03-95c2-1ddcf3bfd9b0
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Definitions.Def_SplitSat_Defs
import Definitions.Def_PaddedDescent_BrutePad
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace FreeCode
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper SplitSat
def Reads (dec : List Bool → List Unit × Fml) : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), dec (SatFree.enc φ) = (List.replicate n (), Decode.toN φ)
def StReader : Prop := ∃ dec : List Bool → List Unit × Fml, PolyT dec ∧ Reads dec
def StLength : Prop := ∀ k : ℕ, ∃ a d : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ → (SatFree.enc φ).length + 1 ≤ a * (n + 2) ^ d
def DecidesFree (Ms : StepMachine (List Bool) Bool) (w : ℕ) (δ : ℝ) (c : ℕ) : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF w φ →
  ∃ (T : ℕ) (b : Bool), Ms.Runs (SatFree.enc φ) T (c * (n + 2) ^ c) b ∧ (b = true ↔ Sat3.Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
def StBehindReader : Prop := ∀ (dec : List Bool → List Unit × Fml), Reads dec → ∀ (w : ℕ) (D : StepMachine (List Unit × Fml) Bool) (δ : ℝ) (c : ℕ), DecidesW w D δ c → DecidesFree (Stepped.mapIn dec D) w δ c
def bruteCore : StepMachine (List Unit × Fml) Bool :=
  Stepped.mapOut (Stepped.sumRange (fun p : List Unit × Fml => 2 ^ p.1.length) (Stepped.ofFun fun q : (List Unit × Fml) × ℕ => ((PaddedDescent.satAt q.1.2 q.2).toNat : ℤ))) fun v => decide (0 < v)
def StBrute : Prop := ∃ (dec : List Bool → List Unit × Fml) (M : Turing.TM2ComputableAux Bool Bool) (q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec bruteCore) ∧
  (∀ k : ℕ, ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    ∃ (T : ℕ) (b : Bool), (Stepped.mapIn dec bruteCore).Runs (SatFree.enc φ) T (c * (n + 2) ^ c) b ∧ (b = true ↔ Sat3.Satisfiable φ) ∧ T ≤ c * 2 ^ n) ∧
  Simulates M (Stepped.mapIn dec bruteCore) q ∧ ∀ k : ℕ, ∃ c : ℕ, SatFree.DecidesTM k M fun n => c * (n + 2) ^ c * 2 ^ n
def StTiedThree : Prop := ∀ δ : ℝ, 0 < δ → ∃ (dec : List Bool → List Unit × Fml) (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec (core3 ℓ τ)) ∧ DecidesFree (Stepped.mapIn dec (core3 ℓ τ)) 3 δ c ∧
  Simulates M (Stepped.mapIn dec (core3 ℓ τ)) q ∧ SatFree.DecidesTM 3 M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
def StTied : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (dec : List Bool → List Unit × Fml) (τ ℓ₃ τ₃ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) ∧ DecidesFree (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) k δ c ∧
  Simulates M (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) q ∧ SatFree.DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
end FreeCode


