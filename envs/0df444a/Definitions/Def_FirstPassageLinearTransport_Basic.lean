-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Basic
-- name    : FirstPassageLinearTransport_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:55:32.467289+00:00
-- url     : https://prove2.me/theorems/9e97a686-2167-4542-be19-a88531fc67a5
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
set_option autoImplicit true
namespace FirstPassageLinearTransport
def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
def orbit (k n : ℕ) : ℕ := (shortcut^[k]) n
def parityBit (n i : ℕ) : Fin 2 :=
  ⟨orbit i n % 2, Nat.mod_lt _ (by omega)⟩
def oddCount (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (parityBit n i : ℕ)
def dyadicShell (M : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ M) (2 ^ (M + 1))
noncomputable def badCount (S : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n => n ∉ S).card
def PowerDense (S : Set ℕ) (C D : ℝ) : Prop :=
  0 < C ∧ 0 < D ∧ D ≤ 1 ∧
    ∀ X : ℕ, 1 ≤ X → (badCount S X : ℝ) ≤ C * (X : ℝ) ^ (1 - D)
def NaturalDensityOne (S : Set ℕ) : Prop :=
  Filter.Tendsto (fun X : ℕ => (badCount S X : ℝ) / (X : ℝ))
    Filter.atTop (nhds 0)
def ReachesBelow (n : ℕ) (Y : ℝ) : Prop :=
  ∃ k : ℕ, (orbit k n : ℝ) ≤ Y
def HasStretchedLogDescent (δ : ℝ) (n : ℕ) : Prop :=
  ReachesBelow n (Real.exp ((Real.log n) ^ (1 - δ)))
def HasFixedPowerDescent (alpha : ℝ) (n : ℕ) : Prop :=
  ReachesBelow n ((n : ℝ) ^ alpha)
noncomputable def orbitMinimum (n : ℕ) : ℕ :=
  sInf (Set.range fun k : ℕ => orbit k n)
def HasTimedStretchedLogDescent (δ clock : ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ,
    (k : ℝ) < clock * Real.log n ∧
      (orbit k n : ℝ) ≤ Real.exp ((Real.log n) ^ (1 - δ))
end FirstPassageLinearTransport


