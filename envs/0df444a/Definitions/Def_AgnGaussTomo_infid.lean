-- Prove2me | Definitions.Def_AgnGaussTomo_infid
-- name    : AgnGaussTomo_infid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:36.453138+00:00
-- url     : https://prove2.me/theorems/91d0bdb4-cce3-4434-878b-553071b4f33e
-- title:
--   Infidelity with a pure state, $d_{\mathrm{IF}}(\rho,\sigma)=1-\operatorname{tr}(\rho\sigma)$
-- statement:
--   For quantum states $\rho,\sigma$ the **infidelity** is $d_{\mathrm{IF}}(\rho,\sigma)=1-F(\rho,\sigma)$ with fidelity $F(\rho,\sigma)=\big(\operatorname{tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}\big)^2$. When $\sigma=|\psi\rangle\langle\psi|$ is pure, $F(\rho,\sigma)=\langle\psi|\rho|\psi\rangle=\operatorname{tr}(\rho\sigma)$, so
--
--   $$
--   d_{\mathrm{IF}}(\rho,|\psi\rangle\langle\psi|)=1-\operatorname{Re}\operatorname{tr}(\rho\,|\psi\rangle\langle\psi|).
--   $$
--
--   This is the error measure of the main theorem: the learner must output a pure Gaussian state whose infidelity with the unknown state is at most $\mathrm{opt}+\epsilon$.
--
--   **Formalization Note** The definition is the pure-state formula $1-\operatorname{Re}\sum_i\sum_j\rho_{ij}\sigma_{ji}$ (iterated series over the Fock basis); it is the infidelity only when $\sigma$ is pure, which is the case in every statement of the mission.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), §1, printed p. 2 (PDF p. 5), definition of d_IF and F; Eq. (1), p. 1 (PDF p. 4)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **Infidelity with a pure state, `d_IF(ρ, σ) = 1 − tr(ρσ)`.** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), §1,
printed p. 2 (PDF p. 5): "Let d_IF(ρ, σ) ≡ 1 − F(ρ, σ) denote the infidelity between two quantum
states, where F(ρ, σ) ≡ (tr sqrt(√ρ σ √ρ))^2 is the fidelity"; and p. 1, Eq. (1), where the
fidelity with a pure state is `⟨ψ|ρ|ψ⟩`.

For a pure `σ = |ψ⟩⟨ψ|` one has `F(ρ, σ) = ⟨ψ|ρ|ψ⟩ = tr(ρσ)`, so `d_IF(ρ, σ) = 1 − Re tr(ρσ)`.

**Formalization Note.** This is the infidelity **only when the second argument is pure**; every
use in this mission has a pure second argument (an output in `G` or a pure Gaussian state). The
trace is the iterated series `∑ᵢ ∑ⱼ ρᵢⱼ σⱼᵢ` over the Fock basis (absolutely convergent for a
density `ρ` and a rank-one `σ` of a unit vector); its real part is taken (the trace is real
for Hermitian arguments). -/
noncomputable def infid {n : ℕ} (ρ σ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) : ℝ :=
  1 - (∑' i, ∑' j, ρ i j * σ j i).re

end AgnGaussTomo


