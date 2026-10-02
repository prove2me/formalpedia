-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_Conjugate
-- name    : DiscreteConvex_CombinatorialB_Conjugate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:18.127177+00:00
-- url     : https://prove2.me/theorems/fff7ce11-527e-4ac5-b3d9-573c7377edf0
-- title:
--   Real Legendre-Fenchel conjugate
-- statement:
--   The Legendre-Fenchel conjugate $f^\bullet(p)=\sup_x\{\langle p,x\rangle - f(x)\}$ of a real-valued function $f:\mathbb R^V\to\mathbb R$, valued in $\mathrm{EReal}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68, citing Eq. (1.6).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68, citing Eq. (1.6)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.68, citing Eq. (1.6): the real
Legendre-Fenchel transform of a real-valued function on `Rⱽ`, in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- The Legendre-Fenchel conjugate `f•(p) = sup_x \{⟨p,x⟩ - f(x)\}` (Eq. (1.6)) of a
real-valued (everywhere-finite) function `f : Rⱽ → R`, landing in `EReal` since the supremum
need not be finite. -/
noncomputable def Conjugate {V : Type*} [Fintype V] (f : (V → ℝ) → ℝ) (p : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ x : V → ℝ, v = ((dotProduct p x : ℝ) : EReal) - ((f x : ℝ) : EReal)}

end DiscreteConvex.CombinatorialB


