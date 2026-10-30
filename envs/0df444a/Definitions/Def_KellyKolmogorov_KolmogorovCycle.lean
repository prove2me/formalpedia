-- Prove2me | Definitions.Def_KellyKolmogorov_KolmogorovCycle
-- name    : KellyKolmogorov_KolmogorovCycle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:39:40.899282+00:00
-- url     : https://prove2.me/theorems/9efcfddd-568e-4406-92b8-5b7da6910696
-- title:
--   Kolmogorov's cycle condition (1.22)
-- statement:
--   Let $\mathcal S$ be a set and $w(j,k)\ge0$, $j,k\in\mathcal S$, nonnegative weights. The weights satisfy **Kolmogorov's cycle condition** if for any finite sequence of states $j_1,j_2,\dots,j_n\in\mathcal S$
--   $$
--   w(j_1,j_2)\,w(j_2,j_3)\cdots w(j_{n-1},j_n)\,w(j_n,j_1)=w(j_1,j_n)\,w(j_n,j_{n-1})\cdots w(j_3,j_2)\,w(j_2,j_1).
--   $$
--
--   The product of the weights around any closed path equals the product around the same path traversed in the opposite direction. For transition rates this is (1.22) of Theorem 1.8; for transition probabilities it is (1.21) of Theorem 1.7.
--
--   **Formalization Note** Sequences of every length $n\ge1$ are indexed by `Fin n`, with `finRotate` as the cyclic successor; repeated states are allowed.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.5, eq. (1.22), p. 23 (PDF p. 26); eq. (1.21), p. 21 (PDF p. 24)

import Mathlib

open scoped NNReal

namespace KellyKolmogorov

/-- **Kolmogorov's cycle condition.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.5, Theorem 1.8, eq. (1.22),
p. 23 (and (1.21), p. 21, for transition probabilities): for any finite sequence of states
`j₁, j₂, …, jₙ ∈ 𝒮`,
`q(j₁, j₂)q(j₂, j₃) ⋯ q(jₙ₋₁, jₙ)q(jₙ, j₁) = q(j₁, jₙ)q(jₙ, jₙ₋₁) ⋯ q(j₃, j₂)q(j₂, j₁)`.

`KolmogorovCycle w` says: for every `n` and every sequence `j : Fin (n+1) → 𝒮`, the product of
`w` around the closed path `j 0 → j 1 → ⋯ → j n → j 0` equals the product around the same path
traversed in the opposite direction.

**Formalization Note.** Sequences of every length `≥ 1` are indexed by `Fin (n+1)`;
`finRotate (n+1) i` is the cyclic successor `i + 1 mod (n+1)`, so the left product is
`∏ᵢ w(jᵢ, jᵢ₊₁)` and the right product is `∏ᵢ w(jᵢ₊₁, jᵢ)`. Repeated states are allowed. -/
def KolmogorovCycle {𝒮 : Type*} (w : 𝒮 → 𝒮 → ℝ≥0) : Prop :=
  ∀ (n : ℕ) (j : Fin (n + 1) → 𝒮),
    ∏ i, w (j i) (j (finRotate (n + 1) i)) = ∏ i, w (j (finRotate (n + 1) i)) (j i)

end KellyKolmogorov


