-- Prove2me | Definitions.Def_TentNoise_revKernel
-- name    : TentNoise_revKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:43:01.321925+00:00
-- url     : https://prove2.me/theorems/844a2d09-b1a9-4528-8ddc-020b536c42f0
-- title:
--   The reverse kernel $K^*_\sigma=H_\sigma F^*$ of the noised tent map
-- statement:
--   The **stationary reverse kernel of the noised tent map** is $K^*_\sigma=H_\sigma F^*$: $K^*_\sigma(y,\cdot)$ is the law of
--
--   $$
--   a_B\bigl(\mathfrak r(y+\sigma Z)\bigr),\qquad Z\sim\mathcal N(0,1),\ B\sim\mathrm{Bern}(1/2)\ \text{independent},
--   $$
--
--   first a reflected Gaussian step, then a uniformly chosen inverse branch $a_0(z)=z/2$ or $a_1(z)=1-z/2$ of the tent map. Because $H_\sigma$ is symmetric with respect to $\mu$, this kernel generates the noised path law $\mathbb P^\sigma_T$ backward in time.
--
--   **Formalization Note** $K^*_\sigma(y,\cdot)=\int F^*(z,\cdot)\,H_\sigma(y,dz)$ is the kernel composition `revTent ∘ₖ H σ` (Mathlib's `∘ₖ` applies the right-hand kernel first).
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Definition 2.9, p.5; proof of Lemma A.2, p.16 (PDF pp.5, 16)

import Mathlib
import Definitions.Def_TentNoise_H
import Definitions.Def_TentNoise_revTent

open MeasureTheory ProbabilityTheory

namespace TentNoise

/-- The stationary reverse transition kernel of the noised tent map, `K*_σ = H_σ F*`
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Definition 2.9, p.5; the proof of Lemma A.2, p.16): `K*_σ(y, ·)` is the law of
`a_B(𝔯(y + σZ))` with `Z ∼ N(0,1)` and `B ∼ Bern(1/2)` independent: first the reflected Gaussian
step `H_σ`, then a uniformly chosen inverse branch of the tent map.

**Formalization Note** `revTent ∘ₖ H σ` is the kernel composition `y ↦ ∫ F*(z, ·) H_σ(y, dz)`
(Mathlib's `∘ₖ` applies the right-hand kernel first). -/
noncomputable def revKernel (σ : ℝ) : Kernel ℝ ℝ := revTent ∘ₖ H σ

end TentNoise


