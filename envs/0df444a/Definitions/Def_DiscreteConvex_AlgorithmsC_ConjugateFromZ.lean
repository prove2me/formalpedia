-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateFromZ
-- name    : DiscreteConvex_AlgorithmsC_ConjugateFromZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:35:27.79068+00:00
-- url     : https://prove2.me/theorems/521eecff-2b28-463f-a940-59510b0a41da
-- title:
--   ConjugateFromZ
-- statement:
--   The mixed real-primal/integer-dual conjugate: $f\in M[R\to R|Z]$ (dual integral) exactly when $f$ arises this way from some $g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Eq. (10.76).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Eq. (10.76)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_FromEReal
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateFromZE

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f(x) = sup{⟨p,x⟩ - g(p) | p ∈ Zⱽ}`, the mixed real-primal/integer-dual conjugate, Eq.
(10.76): `f ∈ M[R→R|Z]` (dual integral) exactly when `f` arises this way from some `g`. -/
noncomputable def ConjugateFromZ (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : WithTop ℝ :=
  FromEReal (ConjugateFromZE g x)

end DiscreteConvex.AlgorithmsC


