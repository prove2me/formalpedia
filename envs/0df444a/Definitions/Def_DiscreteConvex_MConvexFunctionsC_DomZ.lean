-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
-- name    : DiscreteConvex_MConvexFunctionsC_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:16.315505+00:00
-- url     : https://prove2.me/theorems/76df26f9-7150-415e-978e-0f8f8fb64550
-- title:
--   DomZ
-- statement:
--   The effective domain $\operatorname{dom} f$ of $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def DomZ (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.MConvexFunctionsC


