-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_TopDefs
-- name    : ClauseBound_ParityChecks_TopDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:02:54.595212+00:00
-- url     : https://prove2.me/theorems/9b0a7943-6714-4c9e-b0f0-15e59b025a5a
-- title:
--   Top Defs
-- statement:
--   Definitions and structural lemmas for Top Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_FixedWidthVariableBoundStatement
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace ClauseBound.ParityChecks
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def valO (k : ℕ) (pad : U) (i : Idx) (n s : ℕ) (x : CNode) : ℕ :=
  countOL S k pad i n (blockN k n s) (parQ n (blockN k n s) (leafM x).length) (leafM x)
def numOL (k : ℕ) (i : Idx) (s : ℕ) (p : List Bool × U) : ℕ :=
  bif hasNil (decU k p.1).2 then 0 else walkS k p.2 (tauOf s) (valO S k p.2 i (nK k p.1) s) (rootC (decU k p.1))
def restO (k K n s : ℕ) : ℕ :=
  3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (blockN k n s) * (7 * n + 1)) + (3 * Nat.size (blockN k n s * n) + 3 * Nat.size n + 12) + (n / 2 ^ s + 2) +
    (betaN k s + 5 * k + 10 + (k + 3) * Nat.size n)
def needO (k : ℕ) (i : Idx) (n s : ℕ) : ℕ :=
  needNet S i (UbOL k (S.K i) n (blockN k n s)) (PbOL (S.K i) n (blockN k n s)) 0 + restO k (S.K i) n s
def planAtO (c n₀ k n : ℕ) (i : Idx) (s : ℕ) : Option ℕ :=
  if s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n then
    (needNetC S (List.replicate n ()) i (UbOL k (S.K i) n (blockN k n s)) (PbOL (S.K i) n (blockN k n s)) 0).bind fun v =>
      if v + restO k (S.K i) n s ≤ n then some (v + restO k (S.K i) n s) else none
  else none
def planO (c n₀ k : ℕ) (pick : U → U × Idx) (slU : U → U) (x : List Bool) : Option ℕ :=
  planAtO S c n₀ k (nK k x) (idxN k pick x) (precN k pick slU x)
def eO (c n₀ k : ℕ) (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ := (planO S c n₀ k pick slU x).getD (nK k x)
def AO (c n₀ k : ℕ) (pick : U → U × Idx) (slU : U → U) (p : List Bool × U) : List Bool :=
  outW (decU k p.1, bif (planO S c n₀ k pick slU p.1).isNone then bruteN k p else numOL S k (idxN k pick p.1) (precN k pick slU p.1) p)
end
def StBudgetO : Prop := ∀ k K n s F : ℕ, 1 ≤ k → s0K k ≤ s → 2 ^ restO k K n s ≤ F →
  nProf (3 * K ^ 8) (blkOL (blockN k n s) * (7 * n + 1)) 3 ≤ F ∧
  8 * (6 * n + 1) * (blockN k n s * n + 1) * (Nat.size (blockN k n s * n) + 2) + 8 ≤ F ∧
  2 * (∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j) ≤ F + 1 ∧ stackLenC k (tauOf s) n (inLen k n) ≤ F
def StCorrectO : Prop := ∀ c : ℕ, ∃ n₀ : ℕ, ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (k n : ℕ) (φ : Sat3.CNF n),
  1 ≤ k → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eO S c n₀ k Q.pick slU (SatK.enc k φ) ≤ pad.length →
  AO S c n₀ k Q.pick slU (SatK.enc k φ, pad) = SatK.binary n (SatK.numSat φ)
def StCertO : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (c n₀ k : ℕ) (pick : U → U × Idx) (slU : U → U), PolyT pick → PolyT slU →
  PolyT (AO S c n₀ k pick slU) ∧ PolyT (eO S c n₀ k pick slU)
def StArithO : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C k : ℕ), 1 ≤ k →
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∃ c : ℕ, ∀ n₀ : ℕ, ∃ A : ℕ, ∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n →
    ((planAtO S c n₀ k n (Q.pick (root17 n)).2 (slU (Q.pick (root17 n)).1).length).getD n : ℝ) ≤
      A * n * e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ)
def StEndO : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ), PolyT slU →
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∀ (k : ℕ) (r : ℕ → ℝ) (c₁ : ℕ), 1 ≤ k → (∀ n : ℕ, 1 ≤ n → 1 / (c₁ * Real.logb 2 ((n : ℝ) + 2) ^ c₁) ≤ r n) →
  (∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n → e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ≤ c₁ * r n) → SatK.CountInRateN k r
end ClauseBound.ParityChecks


