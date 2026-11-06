-- Prove2me | Definitions.Def_OrderedExperts_gamma
-- name    : OrderedExperts_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:41.476219+00:00
-- url     : https://prove2.me/theorems/b8cc272b-f16c-489d-9741-ca60d0da075b
-- title:
--   Symmetric conductance $\Gamma(a,b)$
-- statement:
--   For a chain of $m$ active ranks, a floor parameter $\xi$ and a vector $\pi$, the **conductance** of two ranks $1\le a<b\le m$ is
--   $$
--   \Gamma(a,b)=\frac{1}{4\Lambda}\,\frac{\pi(a)\pi(b)}{\Pi[a,b]},\qquad \Lambda=1+\log\frac{m}{\xi},
--   $$
--   and $\Gamma(b,a)=\Gamma(a,b)$. The conductance is largest for pairs of likely actions separated by little $\pi$-mass; it defines the off-diagonal entries of the pair kernel.
--
--   **Formalization Note** Written with $a\wedge b$ and $a\vee b$, so symmetric by construction. The diagonal value of the formula is never read.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.3, p.8

import Definitions.Def_OrderedExperts_massCC
import Definitions.Def_OrderedExperts_bigLambda

namespace OrderedExperts

/-- **Symmetric conductance `Γ`.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.3, p.8: "For
`1 ≤ a < b ≤ m`, define the symmetric conductance `Γ(a, b) = (1/(4Λ)) π(a)π(b)/Π[a, b]`, set
`Γ(b, a) = Γ(a, b)`".

`gamma m ξ π a b = (1/(4Λ)) · π(a∧b) π(a∨b) / Π[a∧b, a∨b]` with `Λ = 1 + log(m/ξ)`; written with
`min`/`max` it is symmetric by construction.

**Formalization Note.** The paper defines `Γ` only for `a ≠ b`; the diagonal value of this
formula is never read (the kernel's diagonal is defined separately, and the estimator evaluates `Γ`
only when `A ≠ B`). -/
noncomputable def gamma (m : ℕ) (ξ : ℝ) (π : ℕ → ℝ) (a b : ℕ) : ℝ :=
  1 / (4 * bigLambda m ξ) * (π (min a b) * π (max a b) / massCC π (min a b) (max a b))

end OrderedExperts


