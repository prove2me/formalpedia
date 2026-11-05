-- Prove2me | Definitions.Def_StepMachines_Prog_Spec
-- name    : StepMachines_Prog_Spec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:23:00.102127+00:00
-- url     : https://prove2.me/theorems/5995c851-7797-4a6a-a6b0-147d75781bf9
-- title:
--   Spec
-- statement:
--   Definitions and structural lemmas for Spec, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Spec.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Prog_Brute
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
section
namespace Groundwork.Prog
open Finset
public abbrev IQ : Type := ℕ × List (List Bool)
@[expose] public def ServesInst {C : Type} (R : Stepped (C × IQ) ℤ) (c : C) {K : ℕ} (ℓ B t S : ℕ)
    (Rm : Inst (Fin K) (List Bool)) : Prop :=
  ∀ (v : Fin K) (θ : Fin K → List Bool), (∀ u, u ≠ v → (θ u).length = ℓ) → θ v = [] →
    R.Runs (c, v.1, List.ofFn θ) t S (Rm v θ) ∧ |Rm v θ| ≤ 2 ^ B
public structure Evaluator : Type 2 where
  app : {C : Type} → [HasSize C] → (C → ℕ) → Stepped (C × IQ) ℤ → Stepped C ℤ
@[expose] public def Evaluator.Correct (E : Evaluator) (K : ℕ) (ε : ℝ) : Prop :=
  ∃ A : ℕ, ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin K) (List Bool)), 1 ≤ lam c → 1 ≤ t → ServesInst R c (lam c) B t S Rm →
    ∃ T : ℕ, (E.app lam R).Runs c T (S + A * (size c + B + lam c) ^ A) (Inst.ZW (lam c) [] Rm) ∧
      (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (K : ℝ) ^ 2 * lam c) * ((B : ℝ) + lam c) ^ A * t
public abbrev WQ : Type := ℕ × List Bool
public abbrev FQ : Type := (ℕ × ℕ) × (List Bool × List Bool)
public structure PNet (C : Type) : Type 1 where
  n : C → ℕ → ℕ
  cap : C → ℕ → ℕ → ℕ
  W : Stepped (C × WQ) ℤ
  f : Stepped (C × FQ) ℤ
public structure PNet.Presents {C : Type} (Np : PNet C) (c : C) {g : ℕ} (N : Network (Fin g) (List Bool) (List Bool))
    (t S : ℕ) : Prop where
  S_eq : ∀ a : Fin g, N.S a = words (Np.n c a)
  c_eq : ∀ a b : Fin g, a ≠ b → N.c a b = Np.cap c a b
  lab_eq : ∀ a b : Fin g, a ≠ b → N.lab a b = words (Np.cap c a b)
  W_runs : ∀ (a : Fin g) (z : List Bool), z.length = Np.n c a → Np.W.Runs (c, (a.val, z)) t S (N.W a z)
  f_runs : ∀ (a b : Fin g) (z θ : List Bool), a ≠ b → z.length = Np.n c a → θ.length = Np.cap c a b →
    Np.f.Runs (c, ((a.val, b.val), (z, θ))) t S (N.f a b z θ)
public structure NetEvaluator : Type 2 where
  app : {C : Type} → [HasSize C] → PNet C → Stepped C ℤ
@[expose] public def NetEvaluator.Correct (NE : NetEvaluator) (g K : ℕ) (ε b : ℝ) : Prop :=
  ∃ A : ℕ, ∀ (C : Type) [HasSize C] (Np : PNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool))
    (P B t S : ℕ), 1 ≤ P → 1 ≤ t → Np.Presents c N t S → N.Sized P B →
    ∃ T : ℕ, (NE.app Np).Runs c T (S + A * (size c + P + B) ^ A) N.value ∧
      (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A * t
end Groundwork.Prog


