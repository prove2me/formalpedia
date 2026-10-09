-- Prove2me | Definitions.Def_LinearMDPRL_Misspec_Event
-- name    : LinearMDPRL_Misspec_Event
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:00.653354+00:00
-- url     : https://prove2.me/theorems/c60ace9e-98c2-4a33-af13-1a8a8e3416bb
-- title:
--   Theorem 3.2 and App. C, pp. 8, 21, 24 — β_k = c(d√ι + ζ√(kd))H, χ, the event 𝔈 of Lemma C.3, δ^k_h and the noise term of Lemma C.7
-- statement:
--   This file names the quantities of the proof of Theorem 3.2 (App. C).
--
--   1. The **episode-dependent bonus** of Theorem 3.2: $\beta_k=c\,(d\sqrt\iota+\zeta\sqrt{kd})\,H$, with $\iota=\log(2dT/p)$ and $T=KH$.
--   2. $\chi=\log[2(c_\beta+1)dT/p]$ (Lemma C.3).
--   3. The **event $\mathfrak E$** of Lemma C.3: for Algorithm 1 run with $\lambda=1$ and $\beta_k=c_\beta(d\sqrt\iota+\zeta\sqrt{kd})H$ on the data $(x^\tau_h,a^\tau_h)$,
--   $$\forall (k,h)\in[K]\times[H]:\quad\Big\|\sum_{\tau=1}^{k-1}\phi^\tau_h\big[V^k_{h+1}(x^\tau_{h+1})-\mathbb P_hV^k_{h+1}(x^\tau_h,a^\tau_h)\big]\Big\|_{(\Lambda^k_h)^{-1}}\le C\cdot dH\sqrt\chi,$$
--   where $\|v\|_{\Lambda^{-1}}=\sqrt{v^\top\Lambda^{-1}v}$.
--   4. The **gap** $\delta^k_h=V^k_h(x^k_h)-V^{\pi_k}_h(x^k_h)$ and the **noise term** $\xi^k_{h+1}=\mathbb E[\delta^k_{h+1}\mid x^k_h,a^k_h]-\delta^k_{h+1}$ of Lemma C.7, where the conditional expectation is $\int\big(V^k_{h+1}-V^{\pi_k}_{h+1}\big)(x')\,\mathbb P_h(\mathrm dx'\mid x^k_h,a^k_h)$.
--
--   **Formalization Note** The page writes the noise term as $\zeta^k_{h+1}$; it is renamed $\xi$ here because $\zeta$ is the misspecification level. Within episode $k$ the functions $V^k$ and $\pi_k$ are fixed, so $\mathbb E[\delta^k_{h+1}\mid x^k_h,a^k_h]$ is the kernel integral above. The event is a property of the data sequence, so it can be assumed of deterministic data in Lemmas C.5–C.7.
-- source:
--   arXiv:1907.05388v2, Theorem 3.2, p. 8 (β_k); Lemma C.3, p. 21 (𝔈, χ); Lemma C.7, p. 24 (δ, ζ^k_{h+1})

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB

open MeasureTheory ProbabilityTheory Matrix

namespace LinearMDPRL.Misspec

universe u v

variable {S : Type u} {A : Type v} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] [Nonempty A]
  {d : ℕ}

/-- The episode-dependent bonus parameter of Theorem 3.2: `β_k = c · (d√ι + ζ√(kd)) H`, with
`ι = log(2dT/p)` and `T = KH`. -/
noncomputable def betaMis (c ζ : ℝ) (d H K : ℕ) (p : ℝ) : ℕ → ℝ :=
  fun k => c * (d * Real.sqrt (LinearMDPRL.Linear.iota d K H p) + ζ * Real.sqrt ((k : ℝ) * d)) * H

/-- `χ = log[2(c_β + 1) d T / p]` (Lemma C.3), with `T = KH`. -/
noncomputable def chi (cβ : ℝ) (d K H : ℕ) (p : ℝ) : ℝ :=
  Real.log (2 * (cβ + 1) * d * ((K : ℝ) * H) / p)

/-- The event `𝔈` of Lemma C.3, as a property of the data `(x^τ_h, a^τ_h)`: for all
`(k, h) ∈ [K] × [H]`,
`‖Σ_{τ=1}^{k-1} φ^τ_h [LinearMDPRL.Linear.V^k_{h+1}(x^τ_{h+1}) − P_h LinearMDPRL.Linear.V^k_{h+1}(x^τ_h, a^τ_h)]‖_{(Λ^k_h)^{-1}} ≤ C · d H √χ`,
where `Λ^k_h`, `V^k` are those of Algorithm 1 run with `λ = 1` and `β_k = c_β (d√ι + ζ√(kd)) H`. -/
def goodEvent (M : LinearMDPRL.Linear.EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ C cβ p : ℝ)
    (H K : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) : Prop :=
  ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
    let Vk : S → ℝ := LinearMDPRL.Linear.lsviV φ M.r 1 (betaMis cβ ζ d H K p) H xs as k (h + 1)
    let s : Fin d → ℝ := ∑ τ ∈ Finset.Ico 1 k,
      (Vk (xs τ (h + 1)) - ∫ y, Vk y ∂(M.P h (xs τ h, as τ h))) •
        WithLp.ofLp (φ (xs τ h) (as τ h))
    Real.sqrt (s ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ s) ≤ C * d * H * Real.sqrt (chi cβ d K H p)

variable [LinearOrder A]

/-- `δ^k_h = LinearMDPRL.Linear.V^k_h(x^k_h) − LinearMDPRL.Linear.V^{π_k}_h(x^k_h)` (Lemma C.7), for Algorithm 1 run with parameters
`λ`, `β`. -/
noncomputable def gapAt (M : LinearMDPRL.Linear.EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (β : ℕ → ℝ) (H : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) : ℝ :=
  LinearMDPRL.Linear.lsviV φ M.r lam β H xs as k h (xs k h) -
    LinearMDPRL.Linear.V M H (LinearMDPRL.Linear.greedyPolicy φ M.r lam β H xs as k) h (xs k h)

/-- The martingale-difference term of Lemma C.7 (written `ζ^k_{h+1}` on the page):
`E[δ^k_{h+1} | x^k_h, a^k_h] − δ^k_{h+1}`, where the conditional expectation is the integral of
`x′ ↦ LinearMDPRL.Linear.V^k_{h+1}(x′) − LinearMDPRL.Linear.V^{π_k}_{h+1}(x′)` against `P_h(· | x^k_h, a^k_h)`. -/
noncomputable def xiNext (M : LinearMDPRL.Linear.EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (β : ℕ → ℝ) (H : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) : ℝ :=
  (∫ y, (LinearMDPRL.Linear.lsviV φ M.r lam β H xs as k (h + 1) y -
      LinearMDPRL.Linear.V M H (LinearMDPRL.Linear.greedyPolicy φ M.r lam β H xs as k) (h + 1) y) ∂(M.P h (xs k h, as k h))) -
    gapAt M φ lam β H xs as k (h + 1)

end LinearMDPRL.Misspec


