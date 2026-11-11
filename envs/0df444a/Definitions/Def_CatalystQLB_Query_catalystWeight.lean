-- Prove2me | Definitions.Def_CatalystQLB_Query_catalystWeight
-- name    : CatalystQLB_Query_catalystWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:26.281489+00:00
-- url     : https://prove2.me/theorems/22d3cc5b-ff13-442b-b710-5b6ff9f93a58
-- title:
--   Product weight $\mu_p(z)=p^{\mathrm{hw}(z)}(1-p)^{\ell-\mathrm{hw}(z)}$
-- statement:
--   For $z\in\{0,1\}^\ell$ and $p\in\mathbb R$, let $\mathrm{hw}(z)$ be the number of ones of $z$ and
--   $$\mu_p(z)=p^{\mathrm{hw}(z)}(1-p)^{\ell-\mathrm{hw}(z)}.$$
--   For $p\in[0,1]$ this is the probability of $z$ when each of the $\ell$ bits is independently $1$ with probability $p$. It is the eigenvalue of the catalyst state $\eta_{\ell,p}$ on $|z\rangle$.
--
--   **Formalization Note** `hammingWeight` counts the `true` entries; the natural-number exponent $\ell-\mathrm{hw}(z)$ is exact because $\mathrm{hw}(z)\le\ell$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), §9.3, p.74 (PDF 77), before Eq. (93)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace CatalystQLB.Query

open QAlgorithms

/-- The weight `µ_p(z) = p^{hw(z)} (1 − p)^{ℓ − hw(z)}` of the catalyst string `z ∈ {0,1}^ℓ`
(Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), §9.3, Lemma 119's proof, p.74 (PDF 77), before Eq. (93): "the eigenvalue of `η_λ`
corresponding to `|z⟩` is `µ_p(z) = p^{hw(z)}(1 − p)^{ℓ−hw(z)}`"). It is the probability of `z`
when each of the `ℓ` bits is independently `1` with probability `p`.

**Formalization Note** `hw` is `QAlgorithms.hammingWeight` (the number of `true` entries,
`true` = `1`); since `hw(z) ≤ ℓ` the natural-number subtraction is exact. -/
noncomputable def catalystWeight (ℓ : ℕ) (p : ℝ) (z : Qubits ℓ) : ℝ :=
  p ^ hammingWeight z * (1 - p) ^ (ℓ - hammingWeight z)

end CatalystQLB.Query


