-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_RunDefs
-- name    : ClauseBound_ParityChecks_RunDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:40.329882+00:00
-- url     : https://prove2.me/theorems/d390c728-0fb7-4301-b906-168faa96cd44
-- title:
--   Run Defs
-- statement:
--   Definitions and structural lemmas for Run Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_ParityChecksStatement
set_option autoImplicit false
section
section
namespace ClauseBound.ParityChecks
open Finset _root_.ParityChecks
abbrev Chk : Type := List ℕ
def lam (m : ℕ) (Ls : List Chk) : ℕ → Finset (Fin m) := fun j => univ.filter fun x => x.val ∈ Ls.getD j []
def Dset (m e : ℕ) : Finset (Fin m) := univ.filter fun x => e ≤ x.val
section Sums
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (nb r : ℕ)
end Sums
def bal (β : ℕ) (a : ℤ) : ℤ := (a + 2 ^ (β - 1)) % 2 ^ β - 2 ^ (β - 1)
structure Par where
  m : ℕ
  nb : ℕ
  r : ℕ
  i₀ : ℕ
  β : ℕ
namespace Par
variable (q : Par)
def k (j : ℕ) : ℕ := q.r - 1 - j
def den (j : ℕ) : ℕ := 16 * 8 ^ q.k j * q.nb ^ q.i₀ * q.m * q.r * (q.nb + 1) ^ (q.m + q.r)
def numP (A : ℤ) (B : ℕ → ℤ) : ℤ :=
  A * q.nb ^ q.i₀ + ((List.range (q.i₀ + 1)).map fun i => (-2 : ℤ) ^ i * q.nb ^ (q.i₀ - i) * B i).sum
def colOf (Ls : List Chk) (cur : Chk) (x : ℕ) : ℕ := (Ls.countP fun L => decide (x ∈ L)) + if x ∈ cur then 1 else 0
def numI (Ls : List Chk) (cur : Chk) (e : ℕ) : ℕ :=
  ((Ls.map List.length).sum + cur.length) * q.nb + ((q.m - e) + q.k Ls.length * q.m)
def numR (Ls : List Chk) (cur : Chk) (e : ℕ) : ℕ :=
  (Ls.map fun L => 2 ^ L.length * q.nb ^ q.m).sum + 2 ^ cur.length * q.nb ^ e * (q.nb + 1) ^ (q.m - e) + q.k Ls.length * (q.nb + 1) ^ q.m
def numC (Ls : List Chk) (cur : Chk) (e : ℕ) : ℕ :=
  ((List.range q.m).map fun x =>
    2 ^ colOf Ls cur x * q.nb ^ (Ls.length + if x < e then 1 else 0) * (q.nb + 1) ^ (q.r - (Ls.length + if x < e then 1 else 0))).sum
def num (A : ℤ) (B : ℕ → ℤ) (Ls : List Chk) (cur : Chk) (e : ℕ) : ℤ :=
  5 ^ q.k Ls.length * q.numP A B * (8 * q.m * q.r * (q.nb + 1) ^ (q.m + q.r) : ℕ) +
    (q.numI Ls cur e * (2 * 8 ^ q.k Ls.length * q.nb ^ q.i₀ * (q.nb + 1) ^ (q.m + q.r)) +
      q.numR Ls cur e * (2 * 8 ^ q.k Ls.length * q.nb ^ q.i₀ * q.m * (q.nb + 1) ^ q.r) +
      q.numC Ls cur e * (2 * 8 ^ q.k Ls.length * q.nb ^ q.i₀ * q.r * (q.nb + 1) ^ q.m) : ℕ)
variable (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
def numO (Ls : List Chk) (cur : Chk) (e : ℕ) : ℤ :=
  q.num (bal q.β (orcA Ls)) (fun i => bal q.β (orcB Ls cur e i)) Ls cur e
def decide1 (Ls : List Chk) (cur : Chk) (e : ℕ) : Chk :=
  if q.numO orcA orcB Ls (cur ++ [e]) (e + 1) ≤ q.numO orcA orcB Ls cur (e + 1) then cur ++ [e] else cur
def runTo (Ls : List Chk) (e : ℕ) : Chk := (List.range e).foldl (q.decide1 orcA orcB Ls) []
def runChecks (j : ℕ) : List Chk := (List.range j).foldl (fun Ls _ => Ls ++ [q.runTo orcA orcB Ls q.m]) []
def run : List Chk := q.runChecks orcA orcB q.r
end Par
structure Tent (q : Par) (Λ : ℕ → Finset (Fin q.m)) : Prop where
  inc : ((∑ j' ∈ range q.r, #(Λ j') : ℕ) : ℚ) < 8 * pr q.nb * q.m * q.r + 1
  row : ∀ j' < q.r, (2 : ℚ) ^ #(Λ j') < 2 * (8 * q.r * (1 + pr q.nb) ^ q.m)
  col : ∀ x : Fin q.m, (2 : ℚ) ^ #{j' ∈ range q.r | x ∈ Λ j'} < 2 * (8 * q.m * (1 + pr q.nb) ^ q.r)
structure Hyp (q : Par) (cardX : ℕ) (ε : ℚ) : Prop where
  nb_two : 2 ≤ q.nb
  r_pos : 1 ≤ q.r
  m_pos : 1 ≤ q.m
  β_pos : 2 ≤ q.β
  start : (5 / 8 : ℚ) ^ q.r * (cardX * q.m.choose (q.nb + 1) : ℕ) ≤ 1 / 8
  series : ∀ u ≤ q.m, |(1 - 2 * pr q.nb) ^ u - ∑ i ∈ range (q.i₀ + 1), (-2 * pr q.nb) ^ i * (u.choose i : ℚ)| ≤ ε
  drift : ε * (cardX * q.m.choose (q.nb + 1) : ℕ) * (q.m * q.r) < 1 / 4
  small : ∀ i ≤ q.i₀, cardX * q.m.choose (q.nb + 1) * q.m.choose i ≤ 2 ^ (q.β - 2)
end ClauseBound.ParityChecks


