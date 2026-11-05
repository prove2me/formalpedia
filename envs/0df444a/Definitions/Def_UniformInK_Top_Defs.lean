-- Prove2me | Definitions.Def_UniformInK_Top_Defs
-- name    : UniformInK_Top_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:17:27.811552+00:00
-- url     : https://prove2.me/theorems/c4e68c1f-8781-41af-97e9-4c8661568cc2
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_Both_Defs
import Definitions.Def_UniformInKStatement
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace UniformInK
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
def betaU (k s : ℕ) : ℕ := 2 * k * (4 * s + 17)
def s0U (k : ℕ) : ℕ := 2 * Nat.size k
def blockU (k n s : ℕ) : ℕ := min (2 ^ betaU k s) (n + 1)
def kcU (k n : ℕ) : ℕ := min k (Nat.log 2 (n + 1))
def kU (x : List Bool) : ℕ := (kOf x).length
def nU (x : List Bool) : ℕ := (fmlOf x).1.length
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def bruteU (p : List Bool × U) : ℕ := ((rng p.2 (2 ^ (fmlOf p.1).1.length)).filter fun y => satAt (fmlOf p.1).2 y).length
def restU (k K n s : ℕ) : ℕ :=
  3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (blockU k n s) * (7 * n + 1)) + (3 * Nat.size (blockU k n s * n) + 3 * Nat.size n + 12) + (n / 2 ^ s + 2) +
    (betaU k s + 5 * k + 10 + (k + 3) * Nat.size n)
def needU (k : ℕ) (i : Idx) (n s : ℕ) : ℕ :=
  needNet S i (UbOL k (S.K i) n (blockU k n s)) (PbOL (S.K i) n (blockU k n s)) 0 + restU k (S.K i) n s
def idxU (pick : U → U × Idx) (x : List Bool) : Idx := (pick (root17 (nU x))).2
def precU (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ := (slU (pick (root17 (nU x))).1).length
def allOccU (x : List Bool) : Bool := (List.range (nU x)).all fun v => (fmlOf x).2.any fun C => C.any fun l => l.1 == v
end
def StLeavesU : Prop := ∀ k n s : ℕ, 1 ≤ k → s0U k ≤ s →
  ∑ j ∈ Finset.range (k * n / tauOf s + 1), (bsumU (tauOf s) k * n).choose j ≤ 2 ^ (n / 2 ^ s + 1)
def StParU : Prop := ∀ k s : ℕ, 1 ≤ k → leafCU (tauOf s) k + 2 ≤ 2 ^ betaU k s ∧ (s0U k ≤ s → k ^ 2 ≤ tauOf s ∧ 8 * k ≤ tauOf s)
def StAllOccU : Prop := ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ → (allOccU (SatM.enc k φ) = true ↔ SatM.AllOccur φ)
def FallBack (r : ℕ → ℝ) : Prop := ∀ B : ℕ, ∃ c₂ : ℕ, ∀ k n : ℕ, 1 ≤ k → 1 ≤ n → Nat.log 2 n < B * k ^ 2 → 1 ≤ (c₂ : ℝ) * (k : ℝ) ^ 2 * r n
end UniformInK


