-- Prove2me | Definitions.Def_TTTSampling_Supplement_klDiv
-- name    : TTTSampling_Supplement_klDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:59:20.36841+00:00
-- url     : https://prove2.me/theorems/d70f4a0e-f29e-4b48-8927-a272e02a45d3
-- title:
--   Kullback–Leibler divergence $D_{\mathrm{KL}}(p\,\|\,q)$ of two distributions on a finite set (in nats)
-- statement:
--   Let $p$ and $q$ be probability distributions on a finite set $B$. The **Kullback–Leibler divergence** of $p$ from $q$ is
--
--   $$
--   D_{\mathrm{KL}}(p\,\|\,q) \;=\; \begin{cases} \displaystyle\sum_{b\in B} p(b)\,\log\frac{p(b)}{q(b)} & \text{if } p \ll q,\\[1ex] +\infty & \text{otherwise,}\end{cases}
--   $$
--
--   where $p \ll q$ (absolute continuity) means that $q(b)=0$ implies $p(b)=0$ for every $b$, $\log$ is the natural logarithm, and $0\log 0 = 0$.
--
--   It is the accuracy measure of the KL lower bound (Theorem 4.14): an algorithm must output a distribution $\hat\nu$ with $D_{\mathrm{KL}}(\hat\nu\,\|\,\mu^\star)\le K$. The value $+\infty$ off absolute continuity matters there: a distribution has finite divergence from a point mass $\delta_x$ only if it equals $\delta_x$.
--
--   **Formalization Note** The value lies in $[0,\infty]$ (`ℝ≥0∞`). On the absolutely continuous branch the finite sum is nonnegative (Gibbs' inequality), so it is taken into $[0,\infty]$ without loss; off it the value is $\top$. Nats are the unit in which Pinsker's inequality reads $D_{\mathrm{TV}}\le\sqrt{D_{\mathrm{KL}}/2}$, the form the paper's proof uses.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Theorem 4.14 and its proof, pp.50–51 (PDF pp.52–53)

import Mathlib

namespace TTTSampling

namespace Supplement

/-- **Kullback–Leibler divergence** `D_KL(p‖q)` of two distributions on a finite type, in nats.

Golowich, Moitra, Rohatgi, *The Power of Test-Time Training for Approximate Sampling*,
arXiv:2606.11437 (version of November 3, 2026), Theorem 4.14, printed p.50 (PDF p.52), where the
accuracy requirement is `D_KL(ν̂‖µ⋆) ≤ K`; its proof (p.50) uses that "D_KL(ν̂‖δ_x) is finite only if
ν̂ = δ_x", and (p.51) Pinsker's inequality `D_TV ≤ √(D_KL/2)`.

`klDiv p q = Σ_b p(b) · log(p(b)/q(b))` when `p` is absolutely continuous with respect to `q`
(`q(b) = 0 ⇒ p(b) = 0` for every `b`), and `+∞` otherwise.

**Formalization Note**
* Natural logarithm (nats), the unit in which Pinsker's inequality reads `D_TV ≤ √(D_KL/2)`.
* Terms with `p(b) = 0` contribute `0` (Lean's `0 * x = 0`), the convention `0 log 0 = 0`.
* On the absolutely continuous branch the sum is nonnegative (Gibbs' inequality), so taking it into
  `ℝ≥0∞` by `ENNReal.ofReal` loses nothing; off it the value is `⊤`, never a junk finite number. -/
noncomputable def klDiv {β : Type} [Fintype β] (p q : PMF β) : ENNReal :=
  if (∀ b : β, q b = 0 → p b = 0) then
    ENNReal.ofReal (∑ b : β, (p b).toReal * Real.log ((p b).toReal / (q b).toReal))
  else ⊤

end Supplement

end TTTSampling


