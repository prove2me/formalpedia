-- Prove2me | Definitions.Def_QMAvsQCIP_yesExp
-- name    : QMAvsQCIP_yesExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:54:32.926467+00:00
-- url     : https://prove2.me/theorems/50441ecc-db3f-4b6d-9a56-e9e79943e248
-- title:
--   Expectation over $\mathrm{YES}_\lambda$
-- statement:
--   The **codeword-hash structure distribution** $\mathrm{YES}_\lambda$ samples the predicates $H_i(a)\leftarrow\mathrm{Bernoulli}(p)$ independently for $(i,a)\in[q]\times\Sigma$, with $p=\lambda^{-4}$, and outputs $O_H$. This is the expectation
--   $$
--   \mathbb E_{O\leftarrow\mathrm{YES}_\lambda}[F(O)]=\mathbb E_H[F(O_H)];
--   $$
--   the probability of an event is the expectation of its indicator.
--
--   **Formalization Note** A finite sum over predicate families.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 8, Eq. (13), p.24

import Definitions.Def_QMAvsQCIP_yesOracle
import Definitions.Def_QMAvsQCIP_bernExp

set_option autoImplicit false

namespace QMAvsQCIP

/-- Expectation over the **codeword-hash structure distribution** `YES_λ` (Definition 8, item 1):
`E_{O ← YES_λ}[F(O)] = E_H[F(O_H)]`, where the values `H_i(a)`, `(i, a) ∈ [q] × Σ`, are independent
Bernoulli(`p`), `p = λ^{−4}`, and `O_H = yesOracle H`. The probability of an event `E` is
`yesExp λ q (E.indicator 1)`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 8, p.24 (PDF p.27): "1. Codeword-hash structure distribution
(YES_λ). Sample predicates H_i : Σ → {0,1} independently according to H_i(a) ← Bernoulli(p)
((i, a) ∈ [q] × Σ) … Define O(y, v) = 1 if H(v) = y∥0^{q−λ}, 0 otherwise"; (13): "p = λ^{−4}". -/
noncomputable def yesExp (lam : ℕ) (q : ℕ+) (F : (Zdom lam q → Bool) → ℝ) : ℝ :=
  bernExp ((lam : ℝ) ^ 4)⁻¹ (fun H : ZMod q × Sym lam q → Bool => F (yesOracle H))

end QMAvsQCIP


