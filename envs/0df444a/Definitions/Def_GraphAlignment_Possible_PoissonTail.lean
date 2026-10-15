-- Prove2me | Definitions.Def_GraphAlignment_Possible_PoissonTail
-- name    : GraphAlignment_Possible_PoissonTail
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:28.529224+00:00
-- url     : https://prove2.me/theorems/5e168f1a-180b-48d2-a9f7-fec52215a242
-- title:
--   Lemma 4.1, p. 14 — the Poisson tail ψ_j(µ) = P(Po(µ) ≥ j)
-- statement:
--   The tail of the Poisson distribution (notation of Lemma 4.1, p. 14). For a parameter $\mu$ and a threshold $j$,
--   $$\psi_j(\mu) = \mathbb P(\mathrm{Po}(\mu) \ge j) = \sum_{i \ge j} \frac{\mu^i e^{-\mu}}{i!},$$
--   the sum running over the integers $i \ge j$.
--
--   It is used in Lemma A.2, which bounds $\psi_{\lambda/2-1}(2\lambda/3)$ from below.
--
--   **Formalization Note** The threshold $j$ is a real number (the paper states $j$ integer, but applies $\psi$ at $j = \lambda/2 - 1$, which need not be an integer); the sum runs over the natural numbers $i$ with $j \le i$. The series is written out explicitly rather than through Mathlib's (deprecated) `poissonPMFReal`.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 14, Lemma 4.1 (definition of ψ_j); p. 21, Lemma A.2

import Mathlib

namespace GraphAlignment.Possible

/-- The Poisson tail `ψ_j(µ) = P(Po(µ) ≥ j) = Σ_{i ≥ j} µ^i e^{-µ} / i!` (Lemma 4.1, p. 14),
for a real threshold `j` and a real parameter `mu = µ`. -/
noncomputable def psi (j mu : ℝ) : ℝ :=
  ∑' k : ℕ, if j ≤ (k : ℝ) then mu ^ k * Real.exp (-mu) / (k.factorial : ℝ) else 0

end GraphAlignment.Possible


