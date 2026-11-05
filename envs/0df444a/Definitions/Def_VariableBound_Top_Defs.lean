-- Prove2me | Definitions.Def_VariableBound_Top_Defs
-- name    : VariableBound_Top_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:19:59.337861+00:00
-- url     : https://prove2.me/theorems/7188a560-9a88-47df-b626-b8af50670363
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_UniformInK_Top_Defs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace VariableBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def valD (k : ℕ) (pad : U) (i : Idx) (n s : ℕ) (x : CNode) : ℕ := countD S k pad i n (blockU k n s) (leafM x)
def restD (k K n s : ℕ) : ℕ :=
  3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (blockU k n s)) +
    Nat.size (8 * (10 * n + 1) * (sbMax (blockU k n s) + 1) * (Nat.size (blockU k n s * n) + 2) + 8) + (n / 2 ^ s + 2) +
    (betaU k s + 5 * k + 10 + (k + 3) * Nat.size n)
def needD (k : ℕ) (i : Idx) (n s : ℕ) : ℕ :=
  needNet S i (UbD k (S.K i) n (blockU k n s)) (PbD (S.K i) n (blockU k n s)) (BbD k n) + restD k (S.K i) n s
def planAtD (k n : ℕ) (i : Idx) (s : ℕ) : Option ℕ :=
  if s0U k ≤ s ∧ 2 ^ betaU k s ≤ n + 1 ∧ 29 * LD (2 ^ betaU k s) + 19 ≤ n then
    (needNetC S (List.replicate n ()) i (UbD k (S.K i) n (blockU k n s)) (PbD (S.K i) n (blockU k n s)) (BbD k n)).bind fun v =>
      if v + restD k (S.K i) n s ≤ n then some (v + restD k (S.K i) n s) else none
  else none
def planD (pick : U → U × Idx) (slU : U → U) (x : List Bool) : Option ℕ :=
  planAtD S (kU x) (nU x) (idxU pick x) (precU pick slU x)
def eD (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ := (planD S pick slU x).getD (nU x)
def useMD (pick : U → U × Idx) (slU : U → U) (x : List Bool) : Bool :=
  allOccU x && decide (1 ≤ (fmlOf x).2.length) && decide (eM S pick x ≤ eD S pick slU x)
def eBD (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ :=
  bif useMD S pick slU x then eM S pick x else eD S pick slU x
end
def StBudgetD : Prop := ∀ k K n s F : ℕ, 1 ≤ k → s0U k ≤ s → 2 ^ restD k K n s ≤ F →
  nPrMax K n (blockU k n s) ≤ F ∧
  8 * (10 * n + 1) * (sbMax (blockU k n s) + 1) * (Nat.size (blockU k n s * n) + 2) + 8 ≤ F ∧
  2 * (∑ j ∈ Finset.range (k * n / tauOf s + 1), (bsumU (tauOf s) k * n).choose j) ≤ F + 1 ∧ stackLenCU k (tauOf s) n (inLen k n) ≤ F
def StExpBD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (k : ℕ) (pick : U → U × Idx) (slU : U → U) (n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ →
  eBD S pick slU (SatM.enc k φ) ≤ eD S pick slU (SatM.enc k φ) ∧
  (SatM.AllOccur φ → 1 ≤ φ.length → eBD S pick slU (SatM.enc k φ) ≤ eM S pick (SatM.enc k φ))
def StPlanLeD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (k n : ℕ) (i : Idx) (s : ℕ), (planAtD S k n i s).getD n ≤ n
def StArithD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ),
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∃ A B : ℕ, ∀ k n : ℕ, 1 ≤ k → S.K (Q.idx 0) ^ 17 ≤ n →
    ((planAtD S k n (Q.pick (root17 n)).2 (slU (Q.pick (root17 n)).1).length).getD n : ℝ) ≤
      A * (k : ℝ) ^ 2 * n * e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ∨ Nat.log 2 n < B * k ^ 2
def StTimeD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ),
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∀ (r : ℕ → ℝ) (c₁ : ℕ), (∀ n : ℕ, 1 ≤ n → 1 / (c₁ * Real.logb 2 ((n : ℝ) + 2) ^ c₁) ≤ r n) →
  (∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n → e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ≤ c₁ * r n) → FallBack r →
  ∀ q : ℕ, ∃ D : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
    q * ((SatM.enc k φ).length + 2 ^ eD S Q.pick slU (SatM.enc k φ) + 1) ^ q ≤ SatM.boundNK r D k n
end VariableBound


