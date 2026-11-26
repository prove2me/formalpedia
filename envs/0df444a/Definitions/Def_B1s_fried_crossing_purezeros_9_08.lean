-- Prove2me | Definitions.Def_B1s_fried_crossing_purezeros_9_08
-- name    : B1s_fried_crossing_purezeros_9_08
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:39:22.33863+00:00
-- url     : https://prove2.me/theorems/d0fb1bc2-bea7-515c-8031-dfc0149c10ca
-- title:
--   fried crossing purezeros 9 08
-- statement:
--   Definitions and structural lemmas for fried crossing purezeros 9 08, from Ben Lawton (blawton/fried-conj-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Resonance-cluster conditional reduction for a proposed counterexample to Fried's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
namespace FriedCrossing
open Filter Topology
namespace PureZeros
open TwinRate
def quartic (c₁ c₂ c₃ c₄ z : ℝ) : ℝ := z ^ 4 - c₁ * z ^ 3 + c₂ * z ^ 2 - c₃ * z + c₄
def e₁of (c₁ scl snc : ℝ) : ℝ := c₁ - scl - snc
def e₂of (c₁ c₂ scl snc : ℝ) : ℝ := c₂ - scl * snc - (scl + snc) * e₁of c₁ scl snc
def rem₁ (c₁ c₂ c₃ scl snc : ℝ) : ℝ :=
  c₃ - ((scl + snc) * e₂of c₁ c₂ scl snc + scl * snc * e₁of c₁ scl snc)
def rem₀ (c₁ c₂ c₄ scl snc : ℝ) : ℝ := c₄ - scl * snc * e₂of c₁ c₂ scl snc
noncomputable def dwMinus (a b a' b' : ℝ) : ℝ :=
  (a' - (2 * a * a' - 4 * b') / (2 * Real.sqrt (disc a b))) / 2
end PureZeros
namespace Capstone
open TorsionCore OrderCount Crossing RateRatio TwinRate PureZeros
end Capstone
end FriedCrossing


