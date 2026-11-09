-- Prove2me | Definitions.Def_LindbladStructLearn_FinDist_bind
-- name    : LindbladStructLearn_FinDist_bind
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:43.746244+00:00
-- url     : https://prove2.me/theorems/a0670e38-bf54-42aa-96c5-8aefe85d0e08
-- title:
--   Sequential composition of finite laws
-- statement:
--   Sample an outcome $a$ from the first law, then an outcome from the law $f(a)$; the weights multiply along each path.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithms 2–3, pp.30–32

import Mathlib
import Definitions.Def_LindbladStructLearn_FinDist

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Sequential composition of finite laws (sample `a`, then sample from `f a`); weights multiply.
Used for Algorithms 2 and 3 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), pp.30–32). -/
def FinDist.bind {α β : Type*} (μ : FinDist α) (f : α → FinDist β) : FinDist β :=
  List.flatMap (fun pa => List.map (fun qb => (pa.1 * qb.1, qb.2)) (f pa.2)) μ

end LindbladStructLearn


