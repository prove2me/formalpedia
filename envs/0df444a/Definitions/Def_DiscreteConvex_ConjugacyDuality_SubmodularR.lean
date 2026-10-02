-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_SubmodularR
-- name    : DiscreteConvex_ConjugacyDuality_SubmodularR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:09:38.993527+00:00
-- url     : https://prove2.me/theorems/8206dd42-26fe-4e3b-85d6-ec67f413e814
-- title:
--   Submodularity of a real-valued lattice function (Eq. 8.1)
-- statement:
--   $f : \mathbb R^V \to \mathbb R \cup \{+\infty\}$ is **submodular**: $f(x)+f(y) \ge f(x\vee y) + f(x \wedge y)$ for all $x,y \in \mathbb R^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.1)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.206, Eq. (8.1): submodularity of a real-valued
lattice function, in `DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- `f : Rⱽ → R ∪ {+∞}` is **submodular** (Eq. (8.1)): `f(x) + f(y) ≥ f(x ∨ y) + f(x ∧ y)` for
all `x, y ∈ Rⱽ`. -/
def SubmodularR {V : Type*} (f : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x y : V → ℝ, f x + f y ≥ f (x ⊔ y) + f (x ⊓ y)

end DiscreteConvex.ConjugacyDuality


