-- Prove2me | Definitions.Def_FermiHubbardMix_eulerStep
-- name    : FermiHubbardMix_eulerStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:35:49.992813+00:00
-- url     : https://prove2.me/theorems/7f39d41b-6e0d-4826-985b-8a4eab68ffa3
-- title:
--   Euler steps $\Phi^{(\delta)}_{i,\mathrm{cohe}}$, $\Phi^{(\delta)}_{i,\mathrm{diss}}$, $\Phi^{(\delta)}_{i,0}$
-- statement:
--   For the field-resonant construction at a site $i$ and $\delta\ge0$:
--   $$
--   \Phi^{(\delta)}_{i,\mathrm{cohe}}(X)=X-i\delta\sum_{B\in\mathcal B_i}[C_B,X],\qquad
--   \Phi^{(\delta)}_{i,\mathrm{diss}}(X)=X+\delta\sum_{B\in\mathcal B_i}\int\gamma_B(\omega)\,\mathcal D_{A_B(\omega)}(X)\,d\omega,
--   $$
--   $$
--   \Phi^{(\delta)}_{i,0}(X)=X+\delta\sum_{B\in\mathcal B_i}\int\gamma_B(\omega)\,\mathcal D_{G^{B,\omega}_{i,0}}(X)\,d\omega,\qquad
--   G^{B,\omega}_{i,0}=\frac1{\sqrt{2\pi}}\int e^{itv_i}Be^{-itv_i}e^{-i\omega t}f_B(t)\,dt,
--   $$
--   with $\mathcal D_A(X)=AXA^\dagger-\tfrac12\{A^\dagger A,X\}$; $G^{B,\omega}_{i,0}$ is eq. (22), the jump operator with $H$ replaced by the onsite term $v_i$.
--
--   These are the one-step maps whose update matrices are computed in Section 14.
--
--   **Formalization Note** The jumps are those of the field-resonant Lindbladian (`FRData.jump`), and the integrals are those of Definition 13.1.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Lemma 14.2, p.63; Lemma 14.3, p.64; Lemma 14.4, p.66; eq. (22), p.62

import Mathlib
import Definitions.Def_FermiHubbardMix_FRData
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}

/-- The coherent Euler step `Φ^{(δ)}_{i,cohe}(X) = X - iδ ∑_{B ∈ B_i} [C_B, X]` of the field-resonant
Lindbladian at site `i` (arXiv:2604.08408, held version sha256 055b8f8f…, Lemma 14.2, p.63). -/
def cohStep (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (F : FRData ord H) (β : ℝ) (i : Λ)
    (δ : ℝ) : Op N →ₗ[ℂ] Op N :=
  LinearMap.id - (Complex.I * δ) • ∑ μ, ∑ ν,
    commLin (cohTerm H.ham (F.jump i μ ν) β (F.sigma β i μ ν) (F.sigma β i μ ν) (F.delta β i μ ν))

/-- The dissipative Euler step
`Φ^{(δ)}_{i,diss}(X) = X + δ ∑_{B ∈ B_i} ∫ γ_B(ω)(A_B(ω) X A_B(ω)† - ½{A_B(ω)†A_B(ω), X}) dω`
(arXiv:2604.08408, held version sha256 055b8f8f…, Lemma 14.3, p.64). -/
def dissStep (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (F : FRData ord H) (β : ℝ) (i : Λ)
    (δ : ℝ) : Op N →ₗ[ℂ] Op N :=
  LinearMap.id + (δ : ℂ) • ∑ μ, ∑ ν,
    linExt (dissipFun H.ham (F.jump i μ ν) (F.sigma β i μ ν) (F.sigma β i μ ν) (F.delta β i μ ν))

/-- The onsite dissipative step `Φ^{(δ)}_{i,0}(X) = X + δ ∑_{B ∈ B_i} ∫ γ_B(ω) D_{G^{B,ω}_{i,0}}(X) dω`,
where `G^{B,ω}_{i,0} = (2π)^{-1/2} ∫ e^{itv_i} B e^{-itv_i} e^{-iωt} f_B(t) dt` is eq. (22), i.e. the
jump operator (17) with `H` replaced by the onsite term `v_i` (arXiv:2604.08408, held version sha256
055b8f8f…, Lemma 14.4, p.66, and eq. (22), p.62). -/
def onsiteStep (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (F : FRData ord H) (β : ℝ) (i : Λ)
    (δ : ℝ) : Op N →ₗ[ℂ] Op N :=
  LinearMap.id + (δ : ℂ) • ∑ μ, ∑ ν,
    linExt (dissipFun (H.v i) (F.jump i μ ν) (F.sigma β i μ ν) (F.sigma β i μ ν) (F.delta β i μ ν))

end FermiHubbardMix


