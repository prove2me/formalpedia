-- Prove2me | Definitions.Def_TIESharp_IsTIE
-- name    : TIESharp_IsTIE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:45.699161+00:00
-- url     : https://prove2.me/theorems/e918148c-7fd0-42df-baf0-33567c24698d
-- title:
--   Truthfulness in expectation (2.1)
-- statement:
--   A family is **truthful in expectation** if for every job count $m$, every machine $i$, every true type $t_i\in[0,\infty)^m$, every alternative bid $b_i\in[0,\infty)^m$ and every profile $b_{-i}$ of the other machines' bids,
--   $$p^m_i(t_i,b_{-i})-t_i\cdot q^m_i(t_i,b_{-i})\ \ge\ p^m_i(b_i,b_{-i})-t_i\cdot q^m_i(b_i,b_{-i}).\tag{2.1}$$
--   A deviation may change the entire row. Only marginals and expected payments enter.
--
--   **Formalization Note.** $(b_i,b_{-i})$ is `Function.update b i bi`; the original row $i$ of `b` is overwritten. All rows range over nonnegative vectors.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §2, p.4, (2.1)

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_marg

set_option autoImplicit false

namespace TIESharp

/-- **Dominant-strategy truthfulness in expectation**, (2.1) (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §2, p.4):
`p^m_i(t_i, b_{-i}) − t_i · q^m_i(t_i, b_{-i}) ≥ p^m_i(b_i, b_{-i}) − t_i · q^m_i(b_i, b_{-i})`
for every job count `m`, machine `i`, true type `t_i`, alternative bid `b_i` and profile `b_{-i}` of
the other machines' bids. "A deviation may change the entire row."

**Formalization Note.** `(b_i, b_{-i})` is `Function.update b i bi`; the row `i` of `b` itself is
overwritten and plays no role. True types, deviations and opponents' bids range over nonnegative
vectors, the paper's `[0, ∞)^m`. -/
def IsTIE {n : ℕ} (F : Family n) : Prop :=
  ∀ (m : ℕ) (b : Fin n → Fin m → ℝ) (i : Fin n) (ti bi : Fin m → ℝ),
    Nonneg b → (∀ j, 0 ≤ ti j) → (∀ j, 0 ≤ bi j) →
      F.pay m (Function.update b i bi) i
          - ∑ j, ti j * marg F m (Function.update b i bi) i j
        ≤ F.pay m (Function.update b i ti) i
          - ∑ j, ti j * marg F m (Function.update b i ti) i j

end TIESharp


