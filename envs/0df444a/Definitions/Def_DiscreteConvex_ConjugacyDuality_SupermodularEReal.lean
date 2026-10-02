-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_SupermodularEReal
-- name    : DiscreteConvex_ConjugacyDuality_SupermodularEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:09:35.990042+00:00
-- url     : https://prove2.me/theorems/932e73a0-c666-46ba-8d09-eee735a96348
-- title:
--   Supermodularity of an EReal-valued lattice function (Eq. 8.2)
-- statement:
--   $g : \mathbb R^V \to \mathbb R \cup \{\pm\infty\}$ is **supermodular**: $g(x)+g(y) \le g(x\vee y) + g(x \wedge y)$ for all $x,y \in \mathbb R^V$ — the natural codomain of a real Legendre-Fenchel transform.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.2)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.206, Eq. (8.2): supermodularity, stated for an
`EReal`-valued lattice function (the natural codomain of a real Legendre-Fenchel transform), in
`DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- `g : Rⱽ → R ∪ {±∞}` is **supermodular** (Eq. (8.2)): `g(x) + g(y) ≤ g(x ∨ y) + g(x ∧ y)`
for all `x, y ∈ Rⱽ`. -/
def SupermodularEReal {V : Type*} (g : (V → ℝ) → EReal) : Prop :=
  ∀ x y : V → ℝ, g x + g y ≤ g (x ⊔ y) + g (x ⊓ y)

end DiscreteConvex.ConjugacyDuality


