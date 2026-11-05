-- Prove2me | Definitions.Def_ClauseBound_TopN_Defs
-- name    : ClauseBound_TopN_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:31:00.298261+00:00
-- url     : https://prove2.me/theorems/706d28c5-6f4a-4238-94f7-ff5d1f21ebe6
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_FixedWidthVariableBoundStatement
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace ClauseBound.TopN
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg
open WidthK (theta bsum leafC)
open PaddedDescent.F.Mark (MCtx markF markN adm nProf cls WfL occ nSat placeE)
def evalV (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (p : U × U × U × U) (Ls : List Fml) : ℤ :=
  sumF (nProf gu.length (cls Ls).length Ls.length) pad fun y =>
    bif adm k gu.length p.1.length p.2.1.length Ls y then val ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y)) else 0
def betaN (k s : ℕ) : ℕ := (4 * s + 17) * (2 ^ (k + 1) + 1) + k + 3
def layersN (k s : ℕ) : ℕ := 2 * betaN k s + 4
def blockN (k n s : ℕ) : ℕ := min (2 ^ betaN k s) (n + 1)
def UbN (k K n s : ℕ) : ℕ := Ub k (3 * K ^ 8) n (n + 2) (betaN k s) (layersN k s + 2)
def PbN (k K n s : ℕ) : ℕ := Pb (3 * K ^ 8) n (betaN k s) (blockN k n s)
def root17 (n : ℕ) : U := List.replicate (((List.range (n + 1)).filter fun b => decide (b ^ 17 ≤ n)).length - 1) ()
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def needNetC (b : U) (i : Idx) (Ub P B : ℕ) : Option ℕ :=
  (S.needC (b, i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) Ub P) (), List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) P B) ())).map fun v =>
    max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (P * (2 * (3 * S.K i ^ 8) / S.K i + 1))) (max ((S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) Ub P) v)
def idxN (k : ℕ) (pick : U → U × Idx) (x : List Bool) : Idx := (pick (root17 (nK k x))).2
def precN (k : ℕ) (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ := (slU (pick (root17 (nK k x))).1).length
end
def StParN : Prop := ∀ k n s : ℕ, leafC (tauOf s) k + 2 ≤ 2 ^ betaN k s ∧
  (6 ≤ n → 2 ^ layersN k s * (2 ^ betaN k s * n) + 5 * 3 ^ layersN k s ≤ 3 ^ layersN k s * (n + 2))
def StWalkCount : Prop := ∀ (k τ n : ℕ) (φ : Sat3.CNF n) (pad : U) (val : CNode → ℕ), 1 ≤ k → SatK.IsKCNF k φ → k ^ 2 ≤ τ →
  2 * (∑ j ∈ Finset.range (k * n / τ + 1), (bsum τ k * n).choose j) ≤ pad.length + 1 → stackLenC k τ n (inLen k n) ≤ pad.length →
  (∀ x : CNode, (leafF x).length ≤ (leafC τ k + 2) * n → (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → (∀ v, (occ x.1 v).length ≤ leafC τ k) →
    (∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) → val x = cntN n (leafF x)) →
  (bif hasNil (decU k (SatK.enc k φ)).2 then 0 else walkS k pad τ val (rootC (decU k (SatK.enc k φ)))) = SatK.numSat φ
end ClauseBound.TopN


