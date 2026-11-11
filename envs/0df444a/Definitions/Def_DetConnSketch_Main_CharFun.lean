-- Prove2me | Definitions.Def_DetConnSketch_Main_CharFun
-- name    : DetConnSketch_Main_CharFun
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:02.755543+00:00
-- url     : https://prove2.me/theorems/323f9dac-7b5b-446b-b4cf-47ce7bbfa96e
-- title:
--   The characteristic function $\varphi_S(t)=\mathbb E_{\sigma,\tau}\exp(it\,\sigma^\top S\tau)$ (§8.1)
-- statement:
--   Let $S$ be a real $k\times k$ matrix and let $\sigma, \tau \in \{-1,1\}^k$ be independent uniformly random sign vectors. The **characteristic function** of the bilinear form $\sigma^\top S \tau$ is
--   $$\varphi_S(t) = \mathbb E_{\sigma,\tau}\, \exp\!\big(i\,t\,\sigma^\top S \tau\big) = 2^{-2k} \sum_{\sigma,\tau \in \{-1,1\}^k} \exp\!\Big(i\,t \sum_{i,j} \sigma_i S_{ij} \tau_j\Big), \qquad t \in \mathbb R,$$
--   a complex number. The paper observes that pairing $\sigma$ with $-\sigma$ shows its imaginary part vanishes; the definition does not assume this.
--
--   Theorem 8.2 asserts its uniform positivity at a small $\theta$; Eq. (8) identifies its values at the sign matrices $S_\ell$ with the eigenvalues of the lower-bound matrix.
--
--   **Formalization Note.** `charFun S t : ℂ`, the finite average over the $2^{2k}$ pairs of bit vectors, signs through `sgn`.
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 48 (PDF 52), §8.1; p. 49 (PDF 53), §8.2

import Mathlib
import Definitions.Def_DetConnSketch_Main_Signs

namespace DetConnSketch.Main

/-!
# The characteristic function `φ_S` of the bilinear Rademacher form (§8.1)

Khanna, Putterman, Sudan, *Deterministic Connectivity Sketches Under Edge Deletions*,
arXiv:2611.06626 (copy sha256 fff87f5b…), p. 48, §8.1; p. 49, §8.2.

For a real `k × k` matrix `S` and `t ∈ ℝ`,
`φ_S(t) = E_{σ,τ} exp(i t σᵀ S τ)`, with `σ, τ ∈ {−1, 1}^k` independent and uniform. The
expectation is the finite average over the `2^{2k}` pairs of sign vectors; the value is complex
(`φ_S : ℝ → ℂ`, as defined in §8.1).
-/

/-- `φ_S(t) = 2^{-2k} ∑_{σ, τ ∈ {±1}^k} exp(i t σᵀ S τ)`, signs encoded by `sgn`. -/
noncomputable def charFun {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) : ℂ :=
  ((2 : ℂ) ^ (2 * k))⁻¹ * ∑ σ : Fin k → Bool, ∑ τ : Fin k → Bool,
    Complex.exp (Complex.I * ((t * ∑ i, ∑ j, sgn (σ i) * S i j * sgn (τ j) : ℝ) : ℂ))

end DetConnSketch.Main


