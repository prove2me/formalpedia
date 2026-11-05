-- Prove2me | Definitions.Def_ClauseBound_Alg_Top
-- name    : ClauseBound_Alg_Top
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:11:54.839296+00:00
-- url     : https://prove2.me/theorems/3abcad95-c684-4c28-bc87-d2757005b6b6
-- title:
--   Top
-- statement:
--   Definitions and structural lemmas for Top, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Top.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_CountKSatRate_Interfaces
import Theorems.Thm_Groundwork_PolyT_dropWhile
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.takeWhile


set_option autoImplicit false
section
section
namespace ClauseBound.Alg
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat
def kOf (x : List Bool) : U := (x.takeWhile id).map fun _ => ()
def restOf (x : List Bool) : List Bool := (x.dropWhile id).drop 1
def fmlOf (x : List Bool) : U × Fml := decU (kOf x).length (restOf x)
def root9 (m : ℕ) : U := List.replicate (((List.range (m + 1)).filter fun b => decide (b ^ 9 ≤ m)).length - 1) ()
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def PtopK (g k m : ℕ) : ℕ := max 1 (2 * k * ((m + g - 1) / g))
def lamTopK (K g k m : ℕ) : ℕ := (K ^ 3 + K * (2 * k * m) + g * PtopK g k m) / K ^ 3
def countG (pad : U) (i : Idx) (ku : U) (ψ : Fml) : ℤ :=
  (rebalG pad (S.K i) (3 * S.K i ^ 8) (lamTopK (S.K i) (3 * S.K i ^ 8) ku.length ψ.length) satFk
    ((List.replicate (3 * S.K i ^ 8) (), ku), ψ)).elim 0 fun I => S.run (pad, i, I)
def needTop (i : Idx) (k m : ℕ) : ℕ :=
  max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i + 1)))
    (max ((S.K i - 1) * lamTopK (S.K i) (3 * S.K i ^ 8) k m)
      (S.need (i, List.replicate (lamTopK (S.K i) (3 * S.K i ^ 8) k m) (),
        List.replicate (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i)) ())))
def needTopC (b : U) (i : Idx) (k m : ℕ) : Option ℕ :=
  (S.needC (b, i, List.replicate (lamTopK (S.K i) (3 * S.K i ^ 8) k m) (),
      List.replicate (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i)) ())).bind fun v =>
    if max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i + 1)))
        (max ((S.K i - 1) * lamTopK (S.K i) (3 * S.K i ^ 8) k m) v) ≤ b.length
    then some (max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i + 1)))
        (max ((S.K i - 1) * lamTopK (S.K i) (3 * S.K i ^ 8) k m) v))
    else none
def planM (pick : U → U × Idx) (x : List Bool) : Option ℕ :=
  needTopC S (fmlOf x).1 (pick (root9 (fmlOf x).2.length)).2 (kOf x).length (fmlOf x).2.length
def eM (pick : U → U × Idx) (x : List Bool) : ℕ := (planM S pick x).getD (fmlOf x).1.length
def AM (pick : U → U × Idx) (p : List Bool × U) : List Bool :=
  outW (fmlOf p.1,
    bif (planM S pick p.1).isNone then ((rng p.2 (2 ^ (fmlOf p.1).1.length)).filter fun y => satAt (fmlOf p.1).2 y).length
    else bif hasNil (fmlOf p.1).2 then 0
    else (countG S p.2 (pick (root9 (fmlOf p.1).2.length)).2 (kOf p.1) (fmlOf p.1).2).toNat)
end
def StDecM : Prop := ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → (∀ C ∈ φ, C.length ≤ k) →
  kOf (SatM.enc k φ) = List.replicate k () ∧ fmlOf (SatM.enc k φ) = (List.replicate n (), Decode.toN φ)
def StCertDecM : Prop := PolyT kOf ∧ PolyT fmlOf
def StCountG : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (pad : U) (i : Idx) (k : ℕ) (ψ : Fml), ok i → 2 ≤ S.K i → 1 ≤ k →
  (∀ C ∈ ψ, C.length ≤ k) → 2 ^ needTop S i k ψ.length ≤ pad.length →
  countG S pad i (List.replicate k ()) ψ = (Count.wordNet (3 * S.K i ^ 8) k ψ).value
def StCorrectM : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (k n : ℕ) (φ : Sat3.CNF n),
  1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ → ∀ pad : U, 2 ^ eM S Q.pick (SatM.enc k φ) ≤ pad.length →
  AM S Q.pick (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)
def StCertSatK : Prop := FKeeps satFk
def StCertM : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ pick : U → U × Idx, PolyT pick → PolyT (AM S pick) ∧ PolyT (eM S pick)
def StTopArith : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), ∃ A : ℕ, ∀ k m : ℕ, 1 ≤ k → S.K (Q.idx 0) ^ 9 ≤ m →
  (needTop S (Q.pick (root9 m)).2 k m : ℝ) ≤ A * k * m * e (Q.pick (root9 m)).1.length
end ClauseBound.Alg


