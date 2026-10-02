-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_Phi
-- name    : DiscreteConvex_Algorithms_Phi
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:23:23.268839+00:00
-- url     : https://prove2.me/theorems/c6a5cddb-d8d3-4938-af23-1ad7dc2f9dc6
-- title:
--   Tie-breaking key $\Phi(u,v)$ (Eq. 10.2)
-- statement:
--   The tie-breaking key $\Phi(u,v)$ (Eq. (10.2)) for a fixed ordering $\varphi : V \to \mathbb N$ of the ground set: $(-1, \varphi(u), -\varphi(v))$ if $\varphi(u) < \varphi(v)$, else $(1, -\varphi(v), \varphi(u))$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2)

import Mathlib

namespace DiscreteConvex.Algorithms

/-- The tie-breaking key `Φ(u,v)` (Eq. (10.2), p.282) for a fixed ordering `φ : V → ℕ` of the
ground set: `(-1, φ(u), -φ(v))` if `φ(u) < φ(v)`, else `(1, -φ(v), φ(u))`. -/
def Phi {V : Type*} (φ : V → ℕ) (u v : V) : ℤ × ℤ × ℤ :=
  if φ u < φ v then (-1, (φ u : ℤ), -(φ v : ℤ)) else (1, -(φ v : ℤ), (φ u : ℤ))

end DiscreteConvex.Algorithms


