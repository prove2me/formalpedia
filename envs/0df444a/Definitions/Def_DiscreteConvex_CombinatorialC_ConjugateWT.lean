-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_ConjugateWT
-- name    : DiscreteConvex_CombinatorialC_ConjugateWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:42:28.20721+00:00
-- url     : https://prove2.me/theorems/08b56707-c97b-4111-9fe6-b8ebed73101c
-- title:
--   Legendre-Fenchel conjugate of an extended-real function
-- statement:
--   $f^\bullet(p)=\sup_x\{\langle p,x\rangle-f(x)\}$ for $f$ valued in $\mathbb R\cup\{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, citing Eq. (1.6).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, citing Eq. (1.6)

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_ToEReal2

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, citing Eq. (1.6): the real Legendre-Fenchel
transform of an extended-real-valued function, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The Legendre-Fenchel conjugate `f•(p) = sup_x \{⟨p,x⟩ - f(x)\}` (Eq. (1.6)) of a
`WithTop ℝ`-valued function `f : Rⱽ → R ∪ \{+∞\}`, landing in `EReal`. -/
noncomputable def ConjugateWT {V : Type*} [Fintype V] (f : (V → ℝ) → WithTop ℝ)
    (p : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ x : V → ℝ, v = ((dotProduct p x : ℝ) : EReal) - ToEReal2 (f x)}

end DiscreteConvex.CombinatorialC


