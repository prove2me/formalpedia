-- Prove2me | Definitions.Def_QuantumPRC_Negligible
-- name    : QuantumPRC_Negligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:04.769526+00:00
-- url     : https://prove2.me/theorems/58a1d6f6-9b21-4848-b122-4f02e3ee308d
-- title:
--   Negligible functions and $\omega(\log\lambda)$
-- statement:
--   A function $\nu:\mathbb N\to\mathbb R$ is **negligible** if for every constant $c>0$ there is $n_0$ such that
--
--   $$
--   |\nu(n)| < n^{-c}\qquad\text{for all } n\ge n_0 .
--   $$
--
--   Every statement of the form "$X(\lambda)\le \mathsf{negl}(\lambda)$" in this mission means: there is a negligible $\nu$ with $X(\lambda)\le\nu(\lambda)$ for all $\lambda$.
--
--   A real sequence $g$ is **$\omega(\log\lambda)$** (written `SuperLog g`) if for every constant $C$, eventually $g(\lambda)\ge C\log\lambda$. This is the meaning of "$n(\lambda)=\omega(\log\lambda)$" (Theorem 6.6) and of "$r\ge n_{\mathrm L}+\ell+\omega(\log\lambda)$" (Lemma 7.11, Theorem 7.3).
--
--   **Formalization Note** The exponent $c$ ranges over positive reals ($n^{-c}$ is the real power), which is equivalent to the version with natural $c$. $\omega(\log\lambda)$ is stated as a lower bound rather than through little-$o$, because $\log\lambda=o(g)$ bounds only $|g|$ and would admit a large negative $g$.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), §3.1, p.16 (negl); Theorem 6.6, p.34 and Lemma 7.11, p.50 (ω(log λ))

import Mathlib

namespace QuantumPRC

/-- **Negligible function.** Hsieh, Yamada, *Quantum Pseudorandom Error-Correcting Codes*,
arXiv:2609.38986 (held file sha256 6901b59d…), §3.1, p.16 ("We write negl for a negligible
function"). A function `ν : ℕ → ℝ` is negligible if for every constant `c > 0` there is `n₀` with
`|ν n| < n^{-c}` for all `n ≥ n₀`.

**Formalization Note.** The exponent `c` is real and `n^{-c}` is `Real.rpow`; this is the
usual definition (equivalent to the version with natural `c`). "`X ≤ negl(λ)`" is always written
as "there is a negligible `ν` with `X ≤ ν λ` for every `λ`". -/
def Negligible (ν : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ n ≥ n₀, |ν n| < (n : ℝ) ^ (-c)

/-- **`g = ω(log λ)`** (used in Theorem 6.6, p.34, Lemma 7.11, p.50, and Theorem 7.3, p.42 of
arXiv:2609.38986): for every constant `C`, eventually `C · log λ ≤ g(λ)`.

**Formalization Note.** Stated as a lower bound and not through `IsLittleO`, because `log = o(g)`
only bounds `|g|` and would admit a large negative `g` (in "`r ≥ nL + ℓ + ω(log λ)`" the quantity
`r − nL − ℓ` is a real number that could a priori be negative). -/
def SuperLog (g : ℕ → ℝ) : Prop :=
  ∀ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, C * Real.log (n : ℝ) ≤ g n

end QuantumPRC


