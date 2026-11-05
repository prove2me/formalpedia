-- Prove2me | Definitions.Def_GivenStatement
-- name    : GivenStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:41:52.552276+00:00
-- url     : https://prove2.me/theorems/6085db4c-8c8d-42cf-bada-36c1265302ca
-- title:
--   Given Statement
-- statement:
--   Definitions and structural lemmas for Given Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/GivenStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_Printed_CodingDefs
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {Q A C : Type}
structure PolyTimeProcs [Enc Q] [Enc A] [Enc C] (Np : ProcsQ Q A C) : Prop where
  P : Unary Np.P
  B : Unary Np.B
  len : Unary fun p : C × ℕ => Np.len p.1 p.2
  cap : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2
  mem : Np.mem.PolyTimeSteps
  W : Np.W.PolyTimeSteps
  Ψ : Np.Ψ.PolyTimeSteps
  f : Np.f.PolyTimeSteps
def IsGivenNetwork [Enc Q] [Enc A] [Enc C] {g : ℕ} (Np : ProcsQ Q A C) (O : Q → Option A) (c : C) (N : Net g) (P B τ S : ℕ) : Prop :=
  SecNetworks.IsNetwork (Np.close O) c N P B τ S ∧ PolyTimeProcs Np
def ofProcs (Np : Procs C) : ProcsQ Unit Unit C :=
  { P := Np.P, B := Np.B, len := Np.len, cap := Np.cap, mem := QueryMachine.lift Np.mem, W := QueryMachine.lift Np.W, Ψ := QueryMachine.lift Np.Ψ, f := QueryMachine.lift Np.f }
def noTable : Unit → Option Unit := fun _ => none
def StOnGiven : Prop := ∀ (NM : NetMachine) (C₁ g K : ℕ) (e : ℝ), ComputesNetworks NM C₁ g K e →
  ∀ (Q A C : Type) [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (Np : ProcsQ Q A C) (O : Q → Option A) (c : C) (N : Net g) (P B τ S : ℕ), IsGivenNetwork Np O c N P B τ S →
    (NM.PolyTimeSteps → (networkOn g NM Np).PolyTimeSteps) ∧
    ∃ T : ℕ, (networkOn g NM Np).Within O QueryMachine.unitCost c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ
def StGridGiven : Prop := ∀ g : ℕ, 1 ≤ g → ∃ a : ℕ, ∀ (tr : Bool) (c : List Unit × List Unit) (lam B : ℕ) (W : ℕ → List Bool → ℤ) (y : ℕ), c.1.length = lam → c.2.length = B → 1 ≤ lam →
  (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) → y < (tOf lam + 1) ^ nRect g →
  IsGivenNetwork (gridProcs g tr) (tables (g * g) lam W) (c, y) (levelNetP g tr lam y (listTables (g * g) W)) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) (a * (B + lam) ^ a)
    (size c + size (g * g) + g * g * (2 * lam + 2) + B + 3 + a * (size c + B + lam) ^ a + 2)
def StFormulaGiven : Prop := ∀ g : ℕ, 0 < g → ∀ (k : ℕ) (Φ : Fml),
  IsGivenNetwork (ofProcs (formulaProcs g k)) noTable Φ (satNet g k Φ) (satPf g k Φ) 1 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8 + 2)
end Given


