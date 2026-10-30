-- Prove2me | Definitions.Def_DerivativeChainContinuation_PolynomialNearCollision
-- name    : DerivativeChainContinuation_PolynomialNearCollision
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:18:28.506809+00:00
-- url     : https://prove2.me/theorems/64e36b3b-7a58-4bb4-beee-746e6f4e6cbd
-- title:
--   Actual polynomial Gini dispersion and local mass
-- statement:
--   Define Gini dispersion from the polynomial root multiset with uniform degree normalization, and local mass from the proportion of root slots in a closed radius-$\rho$ ball. All roots count multiplicity; no supplied coupling or chosen root labeling enters either definition.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PolynomialNearCollision.lean#L8-L10; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PolynomialNearCollision.lean#L12-L13

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

noncomputable def polynomialGini (p : Polynomial ℂ) : ℝ :=
  (p.natDegree:ℝ)⁻¹*(p.natDegree:ℝ)⁻¹*
    (p.roots.map (fun x => (p.roots.map (fun y => ‖x-y‖)).sum)).sum

noncomputable def polynomialLocalMass (p : Polynomial ℂ) (x : ℂ) (ρ : ℝ) : ℝ :=
  (p.natDegree:ℝ)⁻¹*(p.roots.map (fun y => if ‖x-y‖ ≤ ρ then (1:ℝ) else 0)).sum










end DerivativeChainContinuation


