-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
-- name    : CollatzEndpointTransport_Common_QuantitativePullbackDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:20:29.117583+00:00
-- url     : https://prove2.me/theorems/ce514a8a-351e-5438-b699-debc1b4066aa
-- title:
--   Quantitative Pullback Defs
-- statement:
--   Definitions and structural lemmas for Quantitative Pullback Defs, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativePullbackDefs.lean

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace Terras
noncomputable def parityTol (t : ℝ) : ℝ := min t (1 / 2)
def parityGood (t : ℝ) : Set ℕ :=
  {n | PrefixTwoSidedRegular n (Nat.log 2 n / 2) (Nat.log 2 n) (parityTol t)}
end Terras
namespace QuantitativeDensity
open scoped Real
noncomputable section
def collatzPullback (S : Set ℕ) : Set ℕ :=
  {n | (Terras.T^[Nat.log 2 n]) n ∈ S}
def coneCore (K : ℕ) (eta : ℝ) (S : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧
    ∀ k : ℕ, (k : ℝ) ≤ eta * Nat.log 3 n →
      ∀ i : ℕ, i < K * 3 ^ k → 3 ^ k * n + i ∈ S}
def shellConeCore (K : ℕ) (eta : ℝ) (j : ℕ) (S : Set ℕ) : Set ℕ :=
  {n | 3 ^ j ≤ n ∧ n < 3 ^ (j + 1) ∧
    ∀ k : ℕ, (k : ℝ) ≤ eta * j →
      ∀ i : ℕ, i < K * 3 ^ k → 3 ^ k * n + i ∈ S}
def baseMapAt (alpha : ℝ) (M n : ℕ) : ℕ :=
  (3 ^ ⌊alpha * M⌋₊ * n) / 2 ^ M
def baseMap (alpha : ℝ) (n : ℕ) : ℕ :=
  baseMapAt alpha (Nat.log 2 n) n
def basePullback (alpha : ℝ) (S : Set ℕ) : Set ℕ :=
  {n | baseMap alpha n ∈ S}
def pullbackWitnessSet
    (S : Set ℕ) (eta etaPrime alpha correctionTol : ℝ) : Set ℕ :=
  basePullback alpha (coneCore 2 etaPrime S) ∩
    Terras.parityGood eta ∩
    Terras.affineCorrectionGood correctionTol
end
end QuantitativeDensity
end CollatzEndpointTransport


