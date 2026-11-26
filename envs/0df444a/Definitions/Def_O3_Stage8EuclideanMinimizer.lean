-- Prove2me | Definitions.Def_O3_Stage8EuclideanMinimizer
-- name    : O3_Stage8EuclideanMinimizer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:15:01.828865+00:00
-- url     : https://prove2.me/theorems/85a10bc4-fdca-55a9-a985-b04c9b423d60
-- title:
--   Stage8 Euclidean Minimizer
-- statement:
--   Definitions and structural lemmas for Stage8 Euclidean Minimizer, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanMinimizer.lean

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
set_option autoImplicit true
namespace O3
namespace Stage8EuclideanMinimizer
noncomputable def euclideanPsi (M : ℝ) {d : ℕ}
    (x₀ s : Point d) (c : ℝ) (x : Point d) : ℝ :=
  M / 2 * (lpNorm 2 (x - x₀)) ^ (2 : ℕ) + c + pairing s (x - x₀)
noncomputable def euclideanPsiMinimizer (M : ℝ) {d : ℕ}
    (x₀ s : Point d) : Point d :=
  x₀ - M⁻¹ • s
end Stage8EuclideanMinimizer
end O3


