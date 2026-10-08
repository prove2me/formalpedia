-- Prove2me | Definitions.Def_TamedEuler_Convergence_Dominator
-- name    : TamedEuler_Convergence_Dominator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:46.4867+00:00
-- url     : https://prove2.me/theorems/d2680a66-3814-409e-9191-bc8f3af89919
-- title:
--   (13), (14), (25), pp. 6 and 13 — λ, α^N_n, the dominating processes D^N_n and the events Ω^N_n
-- statement:
--   In the setting of the tamed Euler scheme $Y^N_n$ with increments $\Delta W^N_k$:
--
--   1. $\lambda := (1+2c+T+\|\mu(0)\|+\|\sigma(0)\|)^4\in[1,\infty)$ (p. 6), with the operator norm on $\sigma(0)$.
--   2. (25), p. 13: $\displaystyle \alpha^N_n := \mathbb 1_{\{\|Y^N_n\|\ge1\}}\Big\langle \frac{Y^N_n}{\|Y^N_n\|},\frac{\sigma(Y^N_n)}{\|Y^N_n\|}\Delta W^N_n\Big\rangle$.
--   3. The **dominating stochastic processes** (13), p. 6:
--   $$D^N_n := (\lambda+\|\xi\|)\exp\Big(\lambda+\sup_{u\in\{0,1,\dots,n\}}\sum_{k=u}^{n-1}\big[\lambda\|\Delta W^N_k\|^2+\alpha^N_k\big]\Big).$$
--   4. The events (14), p. 6:
--   $$\Omega^N_n := \Big\{\omega\in\Omega:\ \sup_{k\in\{0,\dots,n-1\}}D^N_k(\omega)\le N^{1/(2c)},\ \sup_{k\in\{0,\dots,n-1\}}\|\Delta W^N_k(\omega)\|\le1\Big\}.$$
--
--   On $\Omega^N_n$ the scheme is dominated by $D^N_n$ (Lemma 3.1); the moments of $D^N_n$ are bounded (Lemma 3.5), and $\Omega^N_N$ has complement of probability $O(N^{-p})$ for every $p$ (Lemma 3.6). Together these give the moment bounds of the scheme.
--
--   **Formalization Note** The supremum over $u$ in (13) is the finite maximum over $u\in\{0,\dots,n\}$; the term $u=n$ is the empty sum $0$. The suprema in (14) are written "for all $k<n$", so $\Omega^N_0=\Omega$. $N^{1/(2c)}$ is a real power.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 6, (13)–(14) and λ; p. 13, (25)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_TamedEuler_Convergence_Setting
import Definitions.Def_TamedEuler_Convergence_Scheme

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

variable {d m : ℕ} {Ω : Type*}

/-- Hutzenthaler–Jentzen–Kloeden, p. 6: `λ := (1 + 2c + T + ‖µ(0)‖ + ‖σ(0)‖)⁴`, with the
operator norm on `σ(0)`. -/
noncomputable def lam (T : ℝ≥0) (c : ℝ) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  (1 + 2 * c + T + ‖mu 0‖ + opNorm (σ 0)) ^ 4

/-- Hutzenthaler–Jentzen–Kloeden, p. 13, (25):
`α^N_n := 𝟙_{‖Y^N_n‖ ≥ 1} ⟨Y^N_n / ‖Y^N_n‖, (σ(Y^N_n) / ‖Y^N_n‖) ΔW^N_n⟩`
(used for `n ∈ {0, …, N − 1}`). -/
noncomputable def alpha (T : ℝ≥0) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ) (ξ : Ω → SDEState d)
    (W : ℝ≥0 → Ω → SDEState m) (N n : ℕ) (ω : Ω) : ℝ :=
  if 1 ≤ ‖Y T mu σ ξ W N n ω‖ then
    inner ℝ (‖Y T mu σ ξ W N n ω‖⁻¹ • Y T mu σ ξ W N n ω)
      (‖Y T mu σ ξ W N n ω‖⁻¹ • matVec (σ (Y T mu σ ξ W N n ω)) (dW T W N n ω))
  else 0

/-- Hutzenthaler–Jentzen–Kloeden, p. 6, (13): the dominating process
`D^N_n := (λ + ‖ξ‖) exp(λ + sup_{u ∈ {0,…,n}} Σ_{k=u}^{n−1} [λ ‖ΔW^N_k‖² + α^N_k])`.
The supremum is the finite maximum over `u ∈ {0, …, n}`; the term `u = n` is the empty sum
`0`. -/
noncomputable def D (T : ℝ≥0) (c : ℝ) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ) (ξ : Ω → SDEState d)
    (W : ℝ≥0 → Ω → SDEState m) (N n : ℕ) (ω : Ω) : ℝ :=
  (lam T c mu σ + ‖ξ ω‖) *
    Real.exp (lam T c mu σ +
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun u =>
        ∑ k ∈ Finset.Ico u n,
          (lam T c mu σ * ‖dW T W N k ω‖ ^ 2 + alpha T mu σ ξ W N k ω)))

/-- Hutzenthaler–Jentzen–Kloeden, p. 6, (14): the event
`Ω^N_n := {ω : sup_{k ∈ {0,…,n−1}} D^N_k(ω) ≤ N^{1/(2c)}, sup_{k ∈ {0,…,n−1}} ‖ΔW^N_k(ω)‖ ≤ 1}`,
written as "for all `k < n`"; for `n = 0` it is all of `Ω`. `N^{1/(2c)}` is a real power. -/
def Good (T : ℝ≥0) (c : ℝ) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ) (ξ : Ω → SDEState d)
    (W : ℝ≥0 → Ω → SDEState m) (N n : ℕ) : Set Ω :=
  {ω | ∀ k < n, D T c mu σ ξ W N k ω ≤ (N : ℝ) ^ (1 / (2 * c)) ∧ ‖dW T W N k ω‖ ≤ 1}

end TamedEuler.Convergence


