-- Prove2me | Definitions.Def_LiouvilleDiffAlg_RatFunc
-- name    : LiouvilleDiffAlg_RatFunc
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T17:27:50.076357+00:00
-- url     : https://prove2.me/theorems/f2d52cf2-6798-4a19-b650-3b57c3cdf05b
-- title:
--   The standard derivative $d/dx$ on $\mathbb{C}(x)$
-- statement:
--   Let $\mathbb{C}(x)$ be the field of rational functions in one variable over $\mathbb{C}$, and let $D$ be a derivation on $\mathbb{C}(x)$. We say that $D$ is the **standard derivative** if it agrees with the formal derivative on polynomials:
--   $$D(p) = p' \qquad \text{for every } p \in \mathbb{C}[x].$$
--
--   The examples of the source ("the field $\mathbb{C}(x)$ of rational functions in a single variable has a derivation given by the standard derivative with respect to that variable") are stated for any derivation with this property.
--
--   **Formalization Note** $\mathbb{C}(x)$ is Mathlib's `RatFunc ℂ`, and the derivation is a `Differential (RatFunc ℂ)` instance. Mathlib does not provide this derivation, so the property is a predicate on an arbitrary instance. Its existence and uniqueness are a separate milestone.
-- source:
--   Wikipedia, "Liouville's theorem (differential algebra)", revision oldid=1349223559, https://en.wikipedia.org/w/index.php?title=Liouville%27s_theorem_(differential_algebra)&oldid=1349223559, section "Examples"

import Mathlib

namespace LiouvilleDiffAlg

open scoped Differential

/-- A derivation on `ℂ(x)` (the field `RatFunc ℂ` of rational functions in one variable) is the
*standard derivative* `d/dx` if it restricts to the usual formal derivative on polynomials:
`D(p) = p'` for every `p ∈ ℂ[x]`. -/
def IsStandardDerivation [Differential (RatFunc ℂ)] : Prop :=
  ∀ p : Polynomial ℂ,
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)′ =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative p)

end LiouvilleDiffAlg


