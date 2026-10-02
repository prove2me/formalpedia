-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsCone
-- name    : DiscreteConvex_ConjugacyDualityB_IsCone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:28:03.938379+00:00
-- url     : https://prove2.me/theorems/54643417-4bc5-4faf-8044-20ce213394d9
-- title:
--   IsCone
-- statement:
--   $C$ is a cone: contains $0$ and is closed under nonnegative scaling.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, supporting Theorem 8.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, supporting Theorem 8.5

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `C` is a cone: contains `0` and is closed under nonnegative scaling. -/
def IsCone (C : Set (V → ℝ)) : Prop :=
  (fun _ => (0 : ℝ)) ∈ C ∧ ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → (fun v => t * x v) ∈ C

end DiscreteConvex.ConjugacyDualityB


