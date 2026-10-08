-- Prove2me | Definitions.Def_ShadowTomography_ClassicalLB_biasedDist
-- name    : ShadowTomography_ClassicalLB_biasedDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:29.704528+00:00
-- url     : https://prove2.me/theorems/31fe0765-0a91-401d-a3b0-dcb89c9c9d1b
-- title:
--   Distribution biased toward a half-size subset
-- statement:
--   Let $S$ contain half of the elements of $[N]$. The proof of Theorem 16 uses the **biased distribution** $\mathcal D_{S,\varepsilon}$ that chooses uniformly inside $S$ with total probability $1/2+3\varepsilon$ and uniformly outside $S$ with total probability $1/2-3\varepsilon$. Its mass function is
--
--   $$
--   \mathcal D_{S,\varepsilon}(x)=\begin{cases}(1/2+3\varepsilon)/(N/2),&x\in S,\\(1/2-3\varepsilon)/(N/2),&x\notin S.\end{cases}
--   $$
--
--   When $N\ge2$, $|S|=N/2$, and $0\le\varepsilon\le1/6$, this is a probability distribution. The same family supplies the acceptance and entropy milestones.
--
--   **Formalization Note** The definition is a mass function; the later entropy and information statements assert the existence of a `WildeQIT.FinDist` with exactly these masses under the stated domain conditions.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 20, proof of Theorem 16, definition of 𝒟_i

import Mathlib

namespace ShadowTomography.ClassicalLB

/-- The distribution used in the proof of Theorem 16, as a probability mass function.
When `S` has half the elements of `Fin N`, the two branches have total masses
`1/2 + 3ε` and `1/2 - 3ε`. -/
noncomputable def biasedDist (N : ℕ) (S : Finset (Fin N)) (ε : ℝ) : Fin N → ℝ :=
  fun x => if x ∈ S then (1 / 2 + 3 * ε) / (N / 2 : ℝ)
    else (1 / 2 - 3 * ε) / (N / 2 : ℝ)

end ShadowTomography.ClassicalLB


