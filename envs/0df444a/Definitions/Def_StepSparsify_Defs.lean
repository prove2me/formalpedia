-- Prove2me | Definitions.Def_StepSparsify_Defs
-- name    : StepSparsify_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:20:22.623183+00:00
-- url     : https://prove2.me/theorems/15ac29b6-02dc-4591-89fd-fd40792d9c5d
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_UniformInK_Top_Defs
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace StepSparsify
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK SparsificationLemma
open PaddedDescent.F.Mark (occ)
structure Serves (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) : Prop where
  /-- The tree for width k ≥ 1 and precision s ≥ `s0U k`, of a k-CNF in which no clause contains a
  variable together with its negation: what `UniformInK.StTreeU` says, with 2^(⌊n/2^s⌋+1) for the
  number of leaves and Lc k s for the occurrences. -/
  tree : ∀ (k n s : ℕ), 1 ≤ k → s0U k ≤ s → ∀ ψ : PFml, IsKCNF k n ψ → (∀ C ∈ ψ, ∀ l ∈ C, (l.1, !l.2) ∉ C) →
    (leaves (stepC (Θ k s) k) (bsumU (tauOf s) k * n) (rootC (List.replicate n (), ψ))).length ≤ 2 ^ (n / 2 ^ s + 1) ∧
    (∀ x ∈ leaves (stepC (Θ k s) k) (bsumU (tauOf s) k * n) (rootC (List.replicate n (), ψ)),
      stepC (Θ k s) k x = none ∧ (leafF x).length ≤ (Lc k s + 2) * n ∧
        (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (occ x.1 v).length ≤ Lc k s) ∧
        ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧
    cntN n ψ = ((leaves (stepC (Θ k s) k) (bsumU (tauOf s) k * n) (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((round (stepC (Θ k s) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ bsumU (tauOf s) k * n + 1 ∧
      ∀ x ∈ ((round (stepC (Θ k s) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1,
        x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n
  /-- The bound on the occurrences, plus 2, is at most 2^(betaU k s) = 2^(2k(4s+17)). -/
  par : ∀ k s : ℕ, 1 ≤ k → s0U k ≤ s → Lc k s + 2 ≤ 2 ^ betaU k s
  /-- The two children of a node are polynomial-time jointly in k, s and the node, if k, 2^k and s
  are given in unary. -/
  cert : ∀ (α : Type) [Enc α] (k s : α → ℕ) (x : α → CNode), Unary k → (Unary fun a => 2 ^ k a) → Unary s → PolyT x →
    PolyT fun a => stepC (Θ (k a) (s a)) (k a) (x a)
def walkSG (θ : ℕ → ℕ) (k : ℕ) (pad : U) (val : CNode → ℕ) (r : CNode) : ℕ :=
  (pad.foldl (fun st _ => cap pad ([], 0) (roundS (stepC θ k) val st)) (cap pad ([], 0) ([r], 0))).2
section
variable (Θ : ℕ → ℕ → ℕ → ℕ) {Idx : Type} [Enc Idx] (S : Solver Idx)
end
def StWalkSG : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ) (pad : U) (val : CNode → ℕ) (r : CNode) (d : ℕ),
  (∀ x ∈ leaves (stepC θ k) d r, stepC θ k x = none) → 2 * (leaves (stepC θ k) d r).length ≤ pad.length + 1 →
  (∀ i, len ((roundS (stepC θ k) val)^[i] ([r], 0)) ≤ pad.length) →
  walkSG θ k pad val r = ((leaves (stepC θ k) d r).map val).sum
def StWalkCountG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), Serves Θ Lc →
  ∀ (k s n : ℕ) (φ : Sat3.CNF n) (pad : U) (val : CNode → ℕ), 1 ≤ k → SatK.IsKCNF k φ → s0U k ≤ s →
  2 * 2 ^ (n / 2 ^ s + 1) ≤ pad.length + 1 → stackLenCU k (tauOf s) n (inLen k n) ≤ pad.length →
  (∀ x : CNode, (leafF x).length ≤ (Lc k s + 2) * n → (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → (∀ v, (occ x.1 v).length ≤ Lc k s) →
    (∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) → val x = cntN n (leafF x)) →
  (bif hasNil (Decode.toN φ) then 0 else walkSG (Θ k s) k pad val (rootC (List.replicate n (), noTaut (Decode.toN φ)))) = SatK.numSat φ
def StCertWalkSG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), Serves Θ Lc →
  ∀ (α : Type) [Enc α] (k s : α → ℕ) (pad : α → U) (val : α → CNode → ℕ) (r : α → CNode),
  Unary k → (Unary fun x => 2 ^ k x) → Unary s → PolyT pad → (PolyT fun p : α × CNode => val p.1 p.2) → PolyT r →
  PolyT fun t => walkSG (Θ (k t) (s t)) (k t) (pad t) (val t) (r t)
def StCertNoTaut : Prop := PolyT noTaut
def alphaS (k s : ℕ) : ℕ := Cal.alphaC (max k 3) (1 / 2 ^ s)
def thCal (k s : ℕ) : ℕ → ℕ := Cal.thetaC (alphaS k s)
def lcCal (k s : ℕ) : ℕ := 2 * ∑ j ∈ range k, thCal k s j
def StAlphaS : Prop := ∀ k s : ℕ, alphaS k s = 2 * (max k 3 - 1) ^ 2 * 2 ^ s * Nat.clog 2 (32 * (max k 3 - 1) ^ 2 * 2 ^ s)
def StCalNumbers : Prop := ∀ k s : ℕ, 1 ≤ k → s0U k ≤ s →
  1 ≤ alphaS k s ∧ k ^ 2 ≤ alphaS k s ∧ ∑ c ∈ range k, Cal.betaC (alphaS k s) c ≤ bsumU (tauOf s) k ∧ lcCal k s + 2 ≤ 2 ^ betaU k s
def StCalLeaves : Prop := ∀ (k n s D : ℕ) (ψ : PFml), 1 ≤ k → (∑ c ∈ range k, Cal.betaC (alphaS k s) c) * n ≤ D → IsKCNF k n ψ →
  (tree (thCal k s) k D ψ).length ≤ 2 ^ (n / 2 ^ s + 1)
def StCertThCal : Prop := ∀ (α : Type) [Enc α] (k s i : α → ℕ), Unary k → Unary s → Unary i → PolyT fun a => thCal (k a) (s a) (i a)
def StServesCal : Prop := Serves thCal lcCal
end StepSparsify


