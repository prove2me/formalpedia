-- Prove2me | Definitions.Def_TeleDriving_AsymLimited_Aux
-- name    : TeleDriving_AsymLimited_Aux
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:50.691443+00:00
-- url     : https://prove2.me/theorems/a06a2c8f-9ecc-4331-85f1-23fc86e48caa
-- title:
--   App. D.1, pp. 44–46 — π̃ (19), H(n) = 1/ρ(n), π̂ (22) for the rate (4)
-- statement:
--   Three auxiliary quantities used in the proof of Theorem 2.A (Appendix D.1). Throughout, $\mu$ is the rate (4), $\mu(m,q) = [s/\sqrt{m-q+1}+s]^{-1}$, so the load is
--   $$\rho(q) = \frac{\lambda}{q}\Big(\frac{s}{\sqrt{m-q+1}} + s\Big) \qquad (13),$$
--   $m_\lambda = \lfloor \alpha\lambda s\rfloor$ and $a = 1/\alpha$.
--
--   1. **The comparison probability (19).** With $m = m_\lambda$,
--   $$\tilde\pi_{m_\lambda,m_\lambda}(m_\lambda) = \frac{1}{1 + \sum_{i=0}^{m_\lambda-1} \frac{1}{\rho(m_\lambda)\,a^{i}}}.$$
--   2. **The function $H$** (p. 44). For $m$ vehicles and real $n \in [0,m]$,
--   $$H(n) = \frac{1}{\rho(n)} = \frac{n}{\lambda s\big(\frac{1}{\sqrt{m-n+1}} + 1\big)},$$
--   with $H(0) = 0$.
--   3. **The comparison probability (22).** Given a real number $x \ge 0$ (in the proof, the maximizer $n^*$ of $H$ for $m = m_\lambda$) and $\epsilon \in (0,1)$, let $N = \lfloor x \rfloor$ and $z = \lfloor (1-\epsilon)x \rfloor$. Then
--   $$\hat\pi_{m_\lambda,N}(N) = \pi_{m_\lambda,N}(N)\cdot\frac{1 + \sum_{i=0}^{N-z-1}\prod_{k=0}^{i}\frac{1}{\rho(N-k)}}{1 + \sum_{i=0}^{N-z-1}\big(\frac{1}{\rho(z)}\big)^{i+1}}.$$
--
--   $\tilde\pi$ is a lower bound for the blocking probability with $m_\lambda$ drivers and $\hat\pi$ an upper bound for the blocking probability with $\lfloor n^*\rfloor$ drivers; together they bound the ratio of service levels in Theorem 2.A.
--
--   **Formalization Note** $H$ takes $\lambda$ and $m$ as separate arguments (the page uses $m = m_\lambda$). In Lean $1/\rho(0) = 1/0 = 0$, which is the page's $H(0)$. $\hat\pi$ takes the value $x$ of $n^*$ as an argument; $N$, $z$ are natural-number floors, and $N - z$ is natural subtraction, which is exact because $z \le N$ for $x \ge 0$. The index $N - k$ in the product stays $\ge z+1 \ge 1$ throughout the sums.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.1, p. 44 (19) and H(n), p. 46 (22); App. D (13), p. 42

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymLimited

/-- π̃_{m_λ,m_λ}(m_λ), (19), p. 44: with m = m_λ = ⌊αλs⌋, a = 1/α and ρ the load (13) of the rate (4),
π̃ = 1 / [1 + Σ_{i=0}^{m−1} 1/(ρ(m) aⁱ)]. -/
noncomputable def piTilde (s alpha lam : ℝ) : ℝ :=
  1 / (1 + ∑ i ∈ Finset.range (TeleDriving.ScarceFleet.mLam alpha s lam),
    1 / (TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) * (1 / alpha) ^ i))

/-- H(n) = 1/ρ(n) = n / (λs(1/√(m − n + 1) + 1)), App. D.1, p. 44, for the rate (4) with m vehicles;
n is real and meaningful for n ∈ [0, m]. At n = 0 the Lean value is 1/0 = 0, which is the page's H(0). -/
noncomputable def H (s lam : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  1 / TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam m x

/-- π̂_{m_λ,⌊n*⌋}(⌊n*⌋), (22), p. 46, evaluated at the value `x` of n*: with m = m_λ, N = ⌊x⌋ and
z = ⌊(1 − ϵ)x⌋,
π̂ = π_{m,N}(N) · [1 + Σ_{i=0}^{N−z−1} Π_{k=0}^{i} 1/ρ(N − k)] / [1 + Σ_{i=0}^{N−z−1} (1/ρ(z))^{i+1}]. -/
noncomputable def piHat (s alpha eps lam x : ℝ) : ℝ :=
  TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) ⌊x⌋₊ ⌊x⌋₊ *
    (1 + ∑ i ∈ Finset.range (⌊x⌋₊ - ⌊(1 - eps) * x⌋₊),
        ∏ k ∈ Finset.range (i + 1),
          1 / TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) ((⌊x⌋₊ - k : ℕ) : ℝ)) /
    (1 + ∑ i ∈ Finset.range (⌊x⌋₊ - ⌊(1 - eps) * x⌋₊),
        (1 / TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (⌊(1 - eps) * x⌋₊ : ℝ)) ^ (i + 1))

end TeleDriving.AsymLimited


