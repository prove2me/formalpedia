-- Prove2me | Definitions.Def_O3_Stage9Telescoping
-- name    : O3_Stage9Telescoping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:23:57.090693+00:00
-- url     : https://prove2.me/theorems/0e9402ba-0ed0-417a-b3f7-4daae189e64a
-- title:
--   Stage9 Telescoping
-- statement:
--   Definitions and structural lemmas for Stage9 Telescoping, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
set_option autoImplicit true
open scoped BigOperators
namespace O3
noncomputable def stage9WeightedGradient {d : ℕ}
    (delta : ℕ → ℝ) (g : ℕ → Vec d) (k : ℕ) : Vec d :=
  ∑ j ∈ Finset.range k, delta j • g j
noncomputable def stage9P {d : ℕ} (theta : ℕ → ℝ)
    (g : ℕ → Vec d) : ℕ → Vec d
  | 0 => 0
  | k + 1 => (1 - 1 / theta k) • stage9P theta g k +
      (1 / theta k) • g k
end O3


