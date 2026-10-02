-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomZ
-- name    : DiscreteConvex_MConvexFunctionsD_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:47:55.647535+00:00
-- url     : https://prove2.me/theorems/0454ec89-eb24-45aa-b3e3-19e96aec2276
-- title:
--   DomZ
-- statement:
--   The effective domain of $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def DomZ (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.MConvexFunctionsD


