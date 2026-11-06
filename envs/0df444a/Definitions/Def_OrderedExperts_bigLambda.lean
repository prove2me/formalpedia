-- Prove2me | Definitions.Def_OrderedExperts_bigLambda
-- name    : OrderedExperts_bigLambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:42.552001+00:00
-- url     : https://prove2.me/theorems/6b141df7-84db-41fc-bd8f-c70e2da541ce
-- title:
--   The logarithmic factor $\Lambda=1+\log(m/\xi)$
-- statement:
--   For a chain of $m$ active ranks and a floor parameter $\xi\in(0,1]$, set
--   $$
--   \Lambda=1+\log\frac{m}{\xi}.
--   $$
--   This factor governs the second moment and the self-bound of the endpoint flow estimator, and it normalizes the conductances of the pair sampler. With the final choice $\xi=1/T$ it is at most $1+\log(|\mathcal F|T)$.
--
--   **Formalization Note** $\log$ is the natural logarithm.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.1, p.6

import Mathlib

namespace OrderedExperts

/-- **The logarithmic factor `Λ`.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.1, p.6: "We assume a floor on the
intended distribution, `π(j) ≥ ξ/m`, `j = 1, . . . , m`, where `0 < ξ ≤ 1`, and write
`Λ := 1 + log(m/ξ)`."

`bigLambda m ξ = 1 + log(m/ξ)`, with the natural logarithm.

**Formalization Note.** `Real.log` is the natural logarithm, the paper's `log` (its proofs use
`e^{−x} ≤ 1 − x + x²/2` and `x ≤ −log(1 − x)`). Under the floor (`m ≥ 1`, `0 < ξ ≤ 1`) the argument `m/ξ` is at least `1`. -/
noncomputable def bigLambda (m : ℕ) (ξ : ℝ) : ℝ :=
  1 + Real.log (m / ξ)

end OrderedExperts


