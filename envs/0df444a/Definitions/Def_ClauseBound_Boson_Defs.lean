-- Prove2me | Definitions.Def_ClauseBound_Boson_Defs
-- name    : ClauseBound_Boson_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:24.981273+00:00
-- url     : https://prove2.me/theorems/44089092-d88f-47f7-bc88-4a20175bf382
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_PartitionStatement
set_option autoImplicit false
section
section
namespace ClauseBound.Boson
open Finset
abbrev Ker : Type := Multiset ℕ → Multiset ℕ → ℤ
def bet (n : ℕ) (r : ℤ) : ℤ := if r = 0 then 0 else Ring.choose (r - 1) (n - 1)
def cre (l : ℕ) (K : Ker) : Ker := fun π σ => if l ∈ π then K (π.erase l) σ else 0
def ann (K : Ker) (k : ℕ) : Ker := fun π σ => k * σ.count k * K π (σ.erase k)
def nop (n : ℕ) (F : ℤ → Ker) (r : ℤ) : Ker := fun π σ =>
  ∑ l ∈ π.toFinset, bet n l * cre l (F (r - l)) π σ + ∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ
def one : Ker := fun π σ => if π = σ then 1 else 0
def op : List ℕ → ℤ → Ker
  | [], r => if r = 0 then one else 0
  | n :: a, r => nop n (op a) r
def P (m : ℕ) : Finset (Multiset ℕ) := (univ : Finset (Nat.Partition m)).image fun q => q.parts
def Pz (m : ℤ) : Finset (Multiset ℕ) := if 0 ≤ m then P m.toNat else ∅
def mul2 (a : List ℕ) (r : ℤ) (b : List ℕ) (r' : ℤ) : Ker := fun π σ => ∑ τ ∈ Pz (σ.sum + r'), op a r π τ * op b r' τ σ
def Gam (j n : ℕ) : ℤ := n * Ring.choose (-(n : ℤ) - 1) (j - 1)
def Pos (a : List ℕ) : Prop := ∀ n ∈ a, 1 ≤ n
end ClauseBound.Boson


