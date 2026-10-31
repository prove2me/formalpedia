-- Prove2me | Definitions.Def_FuchsThesis_Daroczy_IsDist
-- name    : FuchsThesis_Daroczy_IsDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:20:57.558807+00:00
-- url     : https://prove2.me/theorems/3e9e631f-ac10-451e-8797-195b2ae533a8
-- title:
--   $n$-point probability distributions $\Gamma_n$ (eq. 2.112)
-- statement:
--   For a natural number $n$, the set of **$n$-point probability distributions** is
--
--   $$
--   \Gamma_n = \Big\{ (p_1,\dots,p_n) \;\Big|\; p_k \ge 0,\ k = 1,\dots,n,\ \text{and } \sum_{i=1}^{n} p_i = 1 \Big\},
--   $$
--
--   and $\Gamma = \bigcup_n \Gamma_n$ is the set of all discrete probability distributions. The predicate says that a real vector $p = (p_1,\dots,p_n)$ lies in $\Gamma_n$.
--
--   These are the arguments of the information functions $H_\alpha$ in Daróczy's characterization of the Shannon entropy (Theorem 2.7 of Fuchs's thesis).
--
--   **Formalization Note** A vector is a function on $\{0,\dots,n-1\}$; the source's $p_k$ sits at index $k-1$. $\Gamma_0$ is empty because the empty sum is $0$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.7, eq. (2.112), p.32 (PDF p.41)

import Mathlib

namespace FuchsThesis.Daroczy

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.7, eq. (2.112), p.32 (PDF p.41): the set of `n`-point
probability distributions
`Γ_n = {(p₁, …, pₙ) | p_k ≥ 0, k = 1, …, n, and ∑ᵢ pᵢ = 1}`.
`IsDist p` says `p ∈ Γ_n`; the set `Γ = ⋃ₙ Γ_n` of all discrete distributions is the union over
`n` of these predicates.

**Formalization Note.** An `n`-point vector is a function `p : Fin n → ℝ`, with the source's
`p_k` (1-based) stored at index `k - 1`. `Γ_0` is empty (the empty sum is `0 ≠ 1`). -/
def IsDist {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

end FuchsThesis.Daroczy


