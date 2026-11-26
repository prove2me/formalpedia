-- Prove2me | Definitions.Def_O3_Stage2RouteA
-- name    : O3_Stage2RouteA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:30:40.068546+00:00
-- url     : https://prove2.me/theorems/6307d7bb-f1f4-5ab8-9cf2-5c6f15cfc8fa
-- title:
--   Stage2 Route A
-- statement:
--   Definitions and structural lemmas for Stage2 Route A, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
set_option autoImplicit true
open scoped BigOperators
namespace O3.Stage2RouteA
noncomputable def linePower (p : ℝ) {d : ℕ} (x h : Point d) (t : ℝ) : ℝ :=
  lpPower p (x + t • h)
noncomputable def linePowerDerivative (p : ℝ) {d : ℕ}
    (x h : Point d) (t : ℝ) : ℝ :=
  p * pairing (powerDualityMap p (x + t • h)) h
noncomputable def lineEnergy (p : ℝ) {d : ℕ} (x h : Point d) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (linePower p x h t) ^ (2 / p)
noncomputable def weightedSquareSum (p : ℝ) {d : ℕ}
    (x h : Point d) (t : ℝ) : ℝ :=
  ∑ i : Fin d, |(x + t • h) i| ^ (p - 2) * (h i) ^ (2 : ℕ)
noncomputable def linePowerPair (p : ℝ) {d : ℕ}
    (x h : Point d) (t : ℝ) : ℝ :=
  pairing (powerDualityMap p (x + t • h)) h
noncomputable def lineGradientFormula (p : ℝ) {d : ℕ}
    (x h : Point d) (t : ℝ) : ℝ :=
  (linePower p x h t) ^ (2 / p - 1) * linePowerPair p x h t
noncomputable def WeightedHolderResidual : Prop :=
  ∀ (p : ℝ), 1 < p → p < 2 → ∀ (d : ℕ) (z h : Point d),
    (∀ i : Fin d, z i ≠ 0) →
      (lpPower p z) ^ (2 / p - 1) *
          (∑ i : Fin d, |z i| ^ (p - 2) * (h i) ^ (2 : ℕ)) ≥
        (lpNorm p h) ^ (2 : ℕ)
end O3.Stage2RouteA


