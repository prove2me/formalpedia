-- Prove2me | Definitions.Def_DerivativeChainContinuation_NearCollisionTower
-- name    : DerivativeChainContinuation_NearCollisionTower
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:23:03.363802+00:00
-- url     : https://prove2.me/theorems/159fbe6c-7464-4b0d-957d-9863f9a9ce36
-- title:
--   Uniform row Gini dispersion, local mass and mean cost
-- statement:
--   Define the uniform-slot Gini pair-distance dispersion, the mass in a closed ball about each row slot, and the uniform average of the recursive complete-history endpoint cost. The closed-ball convention retains repeated-root mass at radius zero.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/NearCollisionTower.lean#L12-L13; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/NearCollisionTower.lean#L15-L16; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/NearCollisionTower.lean#L9-L10

import Mathlib
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

noncomputable def uniformSlotGini (r : ComplexRootRows) (k : ℕ) : ℝ :=
  finiteGini (fun _ : Fin (k+1) => (k+1:ℝ)⁻¹) (r k)

noncomputable def complexMeanCost (r : ComplexRootRows) (k : ℕ) : ℝ :=
  ∑ i, (k+1:ℝ)⁻¹*complexRowHistoryCost r k (r k i)

noncomputable def rowLocalMass (r : ComplexRootRows) (k : ℕ) (ρ : ℝ) (i : Fin (k+1)) : ℝ :=
  ∑ j, if ‖r k i-r k j‖ ≤ ρ then (k+1:ℝ)⁻¹ else 0






end DerivativeChainContinuation


