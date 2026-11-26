-- Prove2me | Definitions.Def_O3_Stage11Amortization
-- name    : O3_Stage11Amortization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:23:47.983302+00:00
-- url     : https://prove2.me/theorems/63fd747f-1b8b-406b-ac0b-13bd072e17ac
-- title:
--   Stage11 Amortization
-- statement:
--   Definitions and structural lemmas for Stage11 Amortization, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean

import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
namespace O3
structure DoublingWeight (w : ℝ → ℝ) (ratio : ℝ) : Prop where
  ratio_gt_one : 1 < ratio
  nonneg : ∀ {x}, 0 ≤ x → 0 ≤ w x
  mono : MonotoneOn w (Set.Ici 0)
  doubling : ∀ {x}, 0 ≤ x → ratio * w x ≤ w (2 * x)
noncomputable def WrapperExponent (p : ℝ) : ℝ :=
  if p ≤ 2 then (1 / 2 : ℝ) else aboveAlpha p
noncomputable def geometricAmortizationConstant (a : ℝ) : ℝ :=
  (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)
noncomputable def euclideanWrapperWeight (x : ℝ) : ℝ := Real.sqrt x
noncomputable def aboveWrapperWeight (a x : ℝ) : ℝ := x ^ a
noncomputable def belowWrapperWeight (x : ℝ) : ℝ :=
  Real.sqrt x * Real.log (Real.exp 1 + x)
end O3


