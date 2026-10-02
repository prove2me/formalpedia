-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_NegUtil
-- name    : DiscreteConvex_EconomicEquilibrium_NegUtil
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:49:45.708152+00:00
-- url     : https://prove2.me/theorems/bbe8f521-4c01-4fcc-bcf9-dde7e4378a8a
-- title:
--   Negation $\mathbb R\cup\{-\infty\}\to\mathbb R\cup\{+\infty\}$
-- statement:
--   The negation `WithBot ℝ → WithTop ℝ`, sending $-\infty \mapsto +\infty$ and $r \mapsto -r$. Used to form the term $-U_h(x_h)$ (a `WithTop ℝ`-valued, i.e. convex-type, quantity) from the utility value $U_h(x_h) \in \mathbb R \cup \{-\infty\}$ inside the aggregate cost function $\Psi$ (Eq. (11.24)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.335, Eq. (11.24).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.335, Eq. (11.24)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.335, Eq. (11.24) (the `−Uh(xh)` term of the
aggregate cost function `Ψ`): the negation of a utility value, converting a `WithBot ℝ`-valued
(concave-type) quantity into a `WithTop ℝ`-valued (convex-type) one, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The negation `WithBot ℝ → WithTop ℝ`, sending `⊥ ↦ ⊤` and `(r:ℝ) ↦ (-r:ℝ)`. Used to form
`−Uh(xh)` (a `WithTop ℝ`-valued quantity) from the utility value `Uh(xh) : WithBot ℝ` in the
aggregate cost function `Ψ` (Eq. (11.24)). -/
def NegUtil (v : WithBot ℝ) : WithTop ℝ :=
  v.elim ⊤ (fun r => ((-r : ℝ) : WithTop ℝ))

end DiscreteConvex.EconomicEquilibrium


