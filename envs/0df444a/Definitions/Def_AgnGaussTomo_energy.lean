-- Prove2me | Definitions.Def_AgnGaussTomo_energy
-- name    : AgnGaussTomo_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:52.056897+00:00
-- url     : https://prove2.me/theorems/4a7094bb-28a2-4670-8837-820543b6fc04
-- title:
--   Energy from the moments, $E=\tfrac14\operatorname{tr}V+\tfrac12\|m\|_2^2$
-- statement:
--   For an $n$-mode state with mean vector $m\in\mathbb R^{2n}$ and covariance matrix $V$ (normalized so that the vacuum has $V=I$), the expected energy $E=\operatorname{tr}(\rho\hat E_n)$ of $\hat E_n=\tfrac12\sum_j(\hat q_j^2+\hat p_j^2)$ is
--
--   $$
--   E(\rho)=\tfrac14\operatorname{tr}V(\rho)+\tfrac12\|m(\rho)\|_2^2 .
--   $$
--
--   The energy of the closest Gaussian state controls the error of plain robust heterodyne tomography (Theorem 3.2).
--
--   **Formalization Note** Means and covariances are indexed by the interleaved quadratures $(q_1,p_1,\dots,q_n,p_n)$ of the published `GaussianAt`; trace and norm do not depend on the ordering.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), §2.2, printed p. 9 (PDF p. 12)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Support50.P14 (InterleavedQuadrature OscillatorCovariance)

namespace AgnGaussTomo

/-- **Energy of a state from its moments, `E(ρ) = ¼ tr V(ρ) + ½ ‖m(ρ)‖²`.** Arulandu, Chen, Chen, Li,
Ma, *Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), §2.2,
printed p. 9 (PDF p. 12): "Ê_n ≡ ½ Σ_j (q̂_j² + p̂_j²) = ½ R̂ᵀR̂, E(ρ) ≡ tr(ρÊ_n) = ¼ tr V(ρ) + ½ ‖m(ρ)‖²".

`energy d V` is `¼ tr V + ½ Σₐ d_a²` for a mean vector `d` and covariance `V`.

**Formalization Note.** Mean and covariance are indexed by the interleaved quadratures
`Fin n × Fin 2` of the published `Support50.P14` (`(j, 0) = q̂_j`, `(j, 1) = p̂_j`), with the
covariance normalized so that the vacuum has `V = I` (the paper's normalization, p. 9). Trace and
Euclidean norm do not depend on the ordering of the quadratures. -/
noncomputable def energy {n : ℕ} (d : InterleavedQuadrature (Fin n) → ℝ)
    (V : OscillatorCovariance (Fin n)) : ℝ :=
  (1 / 4) * V.trace + (1 / 2) * ∑ a, d a ^ 2

end AgnGaussTomo


