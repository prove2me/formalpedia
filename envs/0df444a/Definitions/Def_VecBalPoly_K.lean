-- Prove2me | Definitions.Def_VecBalPoly_K
-- name    : VecBalPoly_K
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:09:33.654204+00:00
-- url     : https://prove2.me/theorems/15198801-aca3-4c2d-91de-a6a84417854f
-- title:
--   The constants $K=16$, $\eta=1/(Kn)$, $H=2^{24}$, $\tau$, $\epsilon$
-- statement:
--   The constants of Algorithm 2.2, for an input with $n$ columns:
--   $$K=16,\qquad \eta=\frac1{Kn},\qquad H=2^{24},\qquad \tau=\frac{\eta}{KHn^2},\qquad \epsilon=\frac{\eta\tau}{K^2}.$$
--   $K$ governs the spreading condition and the row classes, $\eta$ is the weight of the rank-one term of the Gram matrix, $\tau$ bounds the step length and $\epsilon$ is the first-order accuracy of the update direction. All are fixed for the whole run, with $n$ the number of columns of the input (not the number of active coordinates).
--
--   **Formalization Note** The PDF text layer prints "H = 224"; the rendered page reads $H=2^{24}$.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), §2.1, p.4; (2.6), p.5; §2.4, p.6 (PDF p.7); Appendix C, p.15

import Mathlib

namespace VecBalPoly

/-- **The constant `K = 16`.**
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §2.1, p.4 (PDF p.5): "Fix K = 16." -/
def K : ℝ := 16

/-- **`η = 1/(Kn)`**, with `n` the number of columns of the input (fixed for the whole run).
Source: ibid., §2.3, p.5 (PDF p.6), (2.6). -/
noncomputable def eta (n : ℕ) : ℝ := 1 / (K * n)

/-- **`H = 2²⁴`.** Source: ibid., §2.4, p.6 (PDF p.7): "Set H = 2²⁴"; Appendix C, p.15. -/
def Hc : ℝ := 2 ^ 24

/-- **The step bound `τ = η/(KHn²)`.** Source: ibid., p.6 (PDF p.7). -/
noncomputable def tau (n : ℕ) : ℝ := eta n / (K * Hc * n ^ 2)

/-- **The accuracy `ϵ = ητ/K²`** of Lemma 2.1. Source: ibid., p.6 (PDF p.7).

**Formalization Note** The text layer of the PDF prints `H = 224`; the rendered page reads
`H = 2²⁴`. -/
noncomputable def epsA (n : ℕ) : ℝ := eta n * tau n / K ^ 2

end VecBalPoly


