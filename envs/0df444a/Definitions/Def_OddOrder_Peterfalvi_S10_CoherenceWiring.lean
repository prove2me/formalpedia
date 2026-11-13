-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S10_CoherenceWiring
-- name    : OddOrder_Peterfalvi_S10_CoherenceWiring
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:31:49.316435+00:00
-- url     : https://prove2.me/theorems/19729769-f784-4b87-badf-842d3ecb577f
-- title:
--   Peterfalvi §10–16: the coherence-wiring bridge to (6.8)
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §10–16 repeatedly asserts that a maximal-subgroup character family $S$ is coherent (Peterfalvi (9.11), (10.4), (13.2.d), …); in the textbook these are all the same fact, the Sibley coherence theorem. This file provides the bridge wiring those uses to (6.8) through a single opaque coherence target.
--
--   The main declaration: `SibleyTarget` (A Sibley witness for an opaque coherence target `(τ, S, A₀)`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S10_CoherenceWiring.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S10_CoherenceWiring.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems

namespace OddOrder.Peterfalvi.CoherenceWiring

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **A Sibley witness for an opaque coherence target `(τ, S, A₀)`.**

This is the single piece of data a §10–16 spine rider needs in order to discharge its
`Nonempty (S07.IsCoherent τ S A₀)` obligation through (6.8): a normal subgroup `H` of the
maximal subgroup `L`, a faithful Sibley Dade hypothesis `sib` for `(G, L, H)`, and the three
identifications matching `sib`'s Dade map / base family / `H^#`-support to the spine's opaque
`τ` / `S` / `A₀`.

Constructing one is exactly the maximal-subgroup structure obligation of Peterfalvi §14 (e.g.
the proof of (13.2.d) reads off "(6.8) applies to `S`"); it is *not* part of this wiring layer.
Once a `SibleyTarget` is available, `coherent_of_sibleyTarget` discharges the rider with no
further input — and B's (6.8) proof flows through automatically. -/
structure SibleyTarget {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (τ : S07.IntegralCharacterMap ↥L G) (S : Set (ClassFunction ↥L ℂ)) (A0 : Set ↥L) where
  /-- The kernel of the Sibley Dade setup, a normal subgroup of the maximal subgroup `L`. -/
  H : Subgroup ↥L
  /-- `|H|` is invertible in `ℂ` (automatic for finite `H`, carried for convenience). -/
  invH : Invertible (Nat.card ↥H : ℂ)
  /-- The faithful Sibley Dade hypothesis (6.8)(a)/(b)/(c) for `(G, L, H)`. -/
  sib : @S08.SibleyDadeHypothesis G _ _ _ L _ _ H invH
  /-- `sib`'s §4 Dade isometry is the spine's integral character map. -/
  tau_eq : sib.tau = τ
  /-- `sib`'s base family `{Ind_H^L θ}` is the spine's family. -/
  S_eq : sib.S = S
  /-- `sib`'s `H^#`-support is the spine's `A₀`. -/
  A0_eq : S04.supportInSubgroup (S08.sharpImage H) L = A0

end OddOrder.Peterfalvi.CoherenceWiring


