-- Prove2me | Definitions.Def_OWFLocalDesc_IsWeakOWF
-- name    : OWFLocalDesc_IsWeakOWF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:34.831746+00:00
-- url     : https://prove2.me/theorems/e1513791-cafa-4d41-9c2f-255441082c5d
-- title:
--   Weak one-way function (Definition 2.7)
-- statement:
--   A deterministic polynomial-time function $f$ is a **weak one-way function** if there is a positive polynomial $R$ such that every PPT inverter $I$ fails eventually with probability at least $1/R(n)$: for each $I$ there is $n_0$ with
--   $$1-\mathrm{Inv}_f(I,n)\ \ge\ \frac{1}{R(n)}\qquad\text{for all } n\ge n_0 .$$
--
--   Theorem 2.8 (amplification) shows that weak one-way functions exist exactly when one-way functions exist.
--
--   **Formalization Note** $R$ has natural coefficients and values at least $1$, as for negligible functions.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.7, p.14

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OWFLocalDesc_IsOWF
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Weak one-way function (Definition 2.7).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 2.7,
p.14: "A weak one-way function is such a function with a positive polynomial R for which every PPT
inverter fails eventually with probability at least 1/R(n). That is, each inverter has a length n0
beyond which its failure probability at every n ≥ n0 is at least 1/R(n)."

**Formalization Note.** `R` has natural coefficients and value at least `1` everywhere (see
`Negligible`); the failure probability is `1 - invSuccess`. -/
def IsWeakOWF (f : List Bool → List Bool) : Prop :=
  CookPvsNP.PolyTimeComputable f ∧
    ∃ R : Polynomial ℕ, (∀ n, 1 ≤ R.eval n) ∧
      ∀ I : PPT, ∃ n₀ : ℕ, ∀ n ≥ n₀, 1 / ((R.eval n : ℕ) : ℝ) ≤ 1 - invSuccess f I n

end OWFLocalDesc


