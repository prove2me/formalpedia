-- Prove2me | Definitions.Def_StepMachines_Math_SatNet
-- name    : StepMachines_Math_SatNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:37.189524+00:00
-- url     : https://prove2.me/theorems/5e7b5aa2-484b-4eea-bd1b-cb8d19be3a02
-- title:
--   Sat Net
-- statement:
--   Definitions and structural lemmas for Sat Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
set_option autoImplicit false
section
namespace Groundwork.SatNet
open Finset
section Chain
variable {ι V : Type}
@[expose] public def Consec (idx : ι → ℕ) (lab : ι → Option V) (p q : ι) : Prop :=
  idx p < idx q ∧ lab p ≠ none ∧ lab p = lab q ∧ ∀ r, idx p < idx r → idx r < idx q → lab r ≠ lab p
public instance [Fintype ι] [DecidableEq V] (idx : ι → ℕ) (lab : ι → Option V) (p q : ι) : Decidable (Consec idx lab p q) := by
  unfold Consec; infer_instance
variable {idx : ι → ℕ} {lab : ι → Option V}
end Chain
section Net
variable {V : Type}
public abbrev Sl (μ k : ℕ) : Type := Fin μ × Fin k
public abbrev Slot (g μ k : ℕ) : Type := Fin g × Sl μ k
@[expose] public def idx {g μ k : ℕ} (p : Slot g μ k) : ℕ := (p.1.val * μ + p.2.1.val) * k + p.2.2.val
@[expose] public def lit (φ : List (List (V × Bool))) {g μ k : ℕ} (p : Slot g μ k) : Option (V × Bool) :=
  (φ[p.1.val * μ + p.2.1.val]?).bind (·[p.2.2.val]?)
@[expose] public def lab (φ : List (List (V × Bool))) {g μ k : ℕ} (p : Slot g μ k) : Option V :=
  (lit φ p).map Prod.fst
public abbrev Link (φ : List (List (V × Bool))) {g μ k : ℕ} (p q : Slot g μ k) : Prop :=
  Consec idx (lab φ) p q
variable [DecidableEq V]
@[expose] public def weight (φ : List (List (V × Bool))) {g μ k : ℕ} (a : Fin g) (z : Sl μ k → Bool) : ℤ :=
  if (∀ s, lit φ (a, s) = none → z s = false) ∧
      (∀ c : Fin μ, a.val * μ + c.val < φ.length →
        ∃ j : Fin k, (lit φ (a, c, j)).map Prod.snd = some (z (c, j))) ∧
      (∀ s s', Link φ (a, s) (a, s') → z s = z s') then 1 else 0
@[expose] public def Good (φ : List (List (V × Bool))) {g μ k : ℕ} (z : Fin g → Sl μ k → Bool) : Prop :=
  (∀ p : Slot g μ k, lit φ p = none → z p.1 p.2 = false) ∧
    (∀ (a : Fin g) (c : Fin μ), a.val * μ + c.val < φ.length →
      ∃ j : Fin k, (lit φ (a, c, j)).map Prod.snd = some (z a (c, j))) ∧
    (∀ p q : Slot g μ k, Link φ p q → z p.1 p.2 = z q.1 q.2)
public instance (φ : List (List (V × Bool))) {g μ k : ℕ} (z : Fin g → Sl μ k → Bool) : Decidable (Good φ z) := by
  unfold Good; infer_instance
@[expose] public def IsModel (φ : List (List (V × Bool))) (a : V → Bool) : Prop :=
  (∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2) ∧ ∀ v, (∀ C ∈ φ, ∀ l ∈ C, l.1 ≠ v) → a v = false
@[expose] public def toState (φ : List (List (V × Bool))) {g μ k : ℕ} (a : V → Bool) (c : Fin g) (s : Sl μ k) : Bool :=
  match lit φ (c, s) with
  | none => false
  | some l => a l.1
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
public instance [Fintype V] (φ : List (List (V × Bool))) (a : V → Bool) : Decidable (IsModel φ a) := by
  unfold IsModel; infer_instance
@[expose] public def Out (φ : List (List (V × Bool))) {g μ k : ℕ} (a b : Fin g) (s : Sl μ k) : Prop :=
  ∃ s', Link φ (a, s) (b, s')
public instance (φ : List (List (V × Bool))) {g μ k : ℕ} (a b : Fin g) (s : Sl μ k) : Decidable (Out φ a b s) := by
  unfold Out; infer_instance
@[expose] public def net (φ : List (List (V × Bool))) (g μ k : ℕ) :
    Network (Fin g) (Sl μ k → Bool) (Sl μ k → Bool) where
  S _ := univ
  W := weight φ
  Θ a b := if a < b then tuples (Out φ a b) (fun _ => univ) false else ∅
  f a b z θ :=
    if a < b then (if ∀ s, Out φ a b s → z s = θ s then 1 else 0)
    else (if ∀ s s', Link φ (b, s) (a, s') → z s' = θ s then 1 else 0)
  c a b := #{s : Sl μ k | Out φ (min a b) (max a b) s}
end Net
end Groundwork.SatNet


