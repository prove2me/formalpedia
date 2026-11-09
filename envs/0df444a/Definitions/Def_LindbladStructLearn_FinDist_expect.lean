-- Prove2me | Definitions.Def_LindbladStructLearn_FinDist_expect
-- name    : LindbladStructLearn_FinDist_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:11.029829+00:00
-- url     : https://prove2.me/theorems/9140d793-413f-4104-a6b5-0c2ea1305336
-- title:
--   Expectation under a finite law
-- statement:
--   $\mathbb E_\mu[f] = \sum_{(p,a)\in\mu} p\, f(a)$ for a finite law $\mu$ and a complex function $f$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Lemmas 4.9–4.10, pp.31–32

import Mathlib
import Definitions.Def_LindbladStructLearn_FinDist

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Expectation of a complex function under a finite law (`E[·]` in Lemmas 4.9 and 4.10,
Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), pp.31–32). -/
def FinDist.expect {α : Type*} (μ : FinDist α) (f : α → ℂ) : ℂ :=
  (List.map (fun pa => (pa.1 : ℂ) * f pa.2) μ).sum

end LindbladStructLearn


