-- Prove2me | Definitions.Def_RankBasedSDI_LoadBalancing_ScaledProcesses
-- name    : RankBasedSDI_LoadBalancing_ScaledProcesses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:17.642848+00:00
-- url     : https://prove2.me/theorems/4baa8ecb-28c7-46bf-bf98-33662a475953
-- title:
--   Scaled primitives (4.1)–(4.4), (4.6), $\hat U^n$ (4.8), $\hat B^n$, history σ-fields $\mathcal F^n_t$ and squared-jump sums
-- statement:
--   For the $n$-th load-balancing system, $i\in[N]$ and $t\ge0$, with $\mathcal R^n_i(s)=\mathrm{rank}(i;X^n(s))$:
--
--   $$
--   \hat E^n_i(t)=n^{-1/2}(E^n_i(t)-\lambda^n_it),\quad \hat S^n_i(t)=n^{-1/2}(S^n_i(t)-\mu^n_it),\quad \hat A^n_i(t)=n^{-1/2}A^n_i(t),
--   $$
--
--   $$
--   \hat P^{\#,n}_i(t)=\lambda_0\int_0^tp_{\mathcal R^n_i(s)}\,ds,\quad \hat P^n_i(t)=\hat\lambda^n_0\int_0^tp_{\mathcal R^n_i(s)}\,ds,\quad \hat M^n_i=\hat A^n_i-\hat P^n_i,
--   $$
--
--   where $\hat\lambda^n_0=n^{-1/2}\lambda^n_0$. Let $\hat m^n_i=\hat\lambda^n_i-\hat\mu^n_i$ (4.4), with $\hat\lambda^n_i=n^{-1/2}(\lambda^n_i-n\lambda_i)$ and $\hat\mu^n_i=n^{-1/2}(\mu^n_i-n\mu_i)$. Then define
--
--   $$
--   \hat U^n_i(t)=\hat X^n_i(0-)+\hat E^n_i(t)+\hat A^n_i(t)-\hat S^n_i(T^n_i(t))+\hat m^n_it \quad (4.8),\qquad \hat B^n_i=\sigma_i^{-1}(\hat E^n_i-\hat S^n_i),
--   $$
--
--   with $\sigma_i$ from (2.17). The **history** of the system is the filtration $\mathcal F^n_t=\sigma\{\mathcal I^n,\mathcal S^n(s), s\in[0,t]\}$, where
--
--   $$
--   \mathcal S^n(s)=(E^n_i(s),A^n_i(s),D^n_i(s),X^n_i(s),T^n_i(s), i\in[N], A^n_0(s), \theta_{A^n_0(s)}).
--   $$
--
--   Finally, for a path $f$ the sum of its squared jumps over $(0,t]$ is $\sum_{s\in(0,t]}(f(s)-f(s-))^2$. For a càdlàg martingale of finite variation this is its optional quadratic variation $[f](t)$.
--
--   **Formalization Note** The paper prints "$i\in[n]$" in $\mathcal S^n$; this is a typo for $i\in[N]$, which the formalization uses. The mark $\theta_{A^n_0(s)}$ is recorded as $\theta_{A^n_0(s)}+1\in\mathbb N$ when $A^n_0(s)\ge1$, and as $0$ before the first LBS arrival, so no undefined mark $\theta_0$ enters the history. $\mathcal F^n_t$ is given as a family of σ-algebras indexed by $t\in\mathbb R_{\ge0}$. The squared-jump sum is an unordered sum in $[0,\infty]$.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, pp. 10–12, §4.1, (4.1)–(4.4), (4.6), (4.8), the history 𝒮ⁿ and Fⁿ_t (p. 11), B̂ⁿ of Proposition 4.1(iii)

import Mathlib
import Definitions.Def_RankBasedSDI_LoadBalancing_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace RankBasedSDI.LoadBalancing

/-!
Atar & Ichiba, arXiv:2409.15121v1, §4.1 pp. 10–13: the centred and scaled primitives
(4.1)–(4.4), (4.6), (4.8), `B̂ⁿ` of Proposition 4.1(iii), the history σ-fields `Fⁿ_t`, and the
sum of squared jumps used for the optional quadratic variation of Lemma 4.3. All processes are
`ℝ^N`-valued maps `ℕ → Ω → ℝ → (Fin N → ℝ)` (system index, outcome, time, server).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

/-- (4.1): `Êⁿᵢ(t) = n^{−1/2}(Eⁿᵢ(t) − λⁿᵢ t)`. -/
noncomputable def Ehat (S : LoadBalancingSequence Ω N) (n : ℕ) (ω : Ω) (t : ℝ) : Fin N → ℝ :=
  fun i => (S.E n i ω t - S.lam n i * t) / Real.sqrt n

/-- (4.1): `Ŝⁿᵢ(t) = n^{−1/2}(Sⁿᵢ(t) − µⁿᵢ t)`. -/
noncomputable def Shat (S : LoadBalancingSequence Ω N) (n : ℕ) (ω : Ω) (t : ℝ) : Fin N → ℝ :=
  fun i => (S.S n i ω t - S.mu n i * t) / Real.sqrt n

/-- (4.2): `Âⁿᵢ(t) = n^{−1/2} Aⁿᵢ(t)`. -/
noncomputable def Ahat (S : LoadBalancingSequence Ω N) (n : ℕ) (ω : Ω) (t : ℝ) : Fin N → ℝ :=
  fun i => S.A n i ω t / Real.sqrt n

/-- (4.3): `P̂^{#,n}ᵢ(t) = λ₀ ∫_0^t p_{ℛⁿᵢ(s)} ds`, `ℛⁿᵢ(s) = rank(i; Xⁿ(s))`. -/
noncomputable def PhatSharp {S : LoadBalancingSequence Ω N} (H : HeavyTraffic S) (n : ℕ)
    (ω : Ω) (t : ℝ) : Fin N → ℝ :=
  fun i => H.lam0 * ∫ s in (0 : ℝ)..t, S.p (rank (fun j => S.X n j ω s) i)

/-- (4.6): `P̂ⁿᵢ(t) = λ̂ⁿ₀ ∫_0^t p_{ℛⁿᵢ(s)} ds`, with `λ̂ⁿ₀ = n^{−1/2} λⁿ₀`. -/
noncomputable def Phat (S : LoadBalancingSequence Ω N) (n : ℕ) (ω : Ω) (t : ℝ) : Fin N → ℝ :=
  fun i => ((S.lam0 n : ℝ) / Real.sqrt n) * ∫ s in (0 : ℝ)..t, S.p (rank (fun j => S.X n j ω s) i)

/-- (4.6): `M̂ⁿᵢ(t) = Âⁿᵢ(t) − P̂ⁿᵢ(t)`. -/
noncomputable def Mhat (S : LoadBalancingSequence Ω N) (n : ℕ) (ω : Ω) (t : ℝ) : Fin N → ℝ :=
  fun i => Ahat S n ω t i - Phat S n ω t i

/-- (4.4): `m̂ⁿᵢ = λ̂ⁿᵢ − µ̂ⁿᵢ`, with `λ̂ⁿᵢ = n^{−1/2}(λⁿᵢ − nλᵢ)` and `µ̂ⁿᵢ = n^{−1/2}(µⁿᵢ − nµᵢ)`
as in (2.9), (2.11). -/
noncomputable def mhatN {S : LoadBalancingSequence Ω N} (H : HeavyTraffic S) (n : ℕ) :
    Fin N → ℝ :=
  fun i => ((S.lam n i : ℝ) - n * H.lam i) / Real.sqrt n - (S.mu n i - n * H.mu i) / Real.sqrt n

/-- (4.8): `Ûⁿᵢ(t) = X̂ⁿᵢ(0−) + Êⁿᵢ(t) + Âⁿᵢ(t) − Ŝⁿᵢ(Tⁿᵢ(t)) + m̂ⁿᵢ t`. -/
noncomputable def Uhat {S : LoadBalancingSequence Ω N} (H : HeavyTraffic S) (n : ℕ) (ω : Ω)
    (t : ℝ) : Fin N → ℝ :=
  fun i => Xhat0 S n ω i + Ehat S n ω t i + Ahat S n ω t i - Shat S n ω (S.T n i ω t) i +
    mhatN H n i * t

/-- Proposition 4.1(iii): `B̂ⁿᵢ = σᵢ^{−1}(Êⁿᵢ − Ŝⁿᵢ)`, `σᵢ` as in (2.17). -/
noncomputable def Bhat {S : LoadBalancingSequence Ω N} (H : HeavyTraffic S) (n : ℕ) (ω : Ω)
    (t : ℝ) : Fin N → ℝ :=
  fun i => (Ehat S n ω t i - Shat S n ω t i) / diffSigma H i

/-- The history σ-field `Fⁿ_t = σ{ℐⁿ, 𝒮ⁿ(s), s ∈ [0, t]}` (p. 11), where
`𝒮ⁿ(s) = (Eⁿᵢ(s), Aⁿᵢ(s), Dⁿᵢ(s), Xⁿᵢ(s), Tⁿᵢ(s), i ∈ [N], Aⁿ₀(s), θ_{Aⁿ₀(s)})` (the paper's
"`i ∈ [n]`" is a typo for `i ∈ [N]`) and `ℐⁿ = (Xⁿ(0−), Zⁿ(0))` (the sets `𝒩ⁿ, 𝒫ⁿ` are
functions of `Zⁿ(0)`). The last LBS mark `θ_{Aⁿ₀(s)}` is recorded as the natural number
`θ_{Aⁿ₀(s)} + 1` when `Aⁿ₀(s) ≥ 1` and as `0` before the first LBS arrival. -/
@[instance_reducible]
noncomputable def historySigma (S : LoadBalancingSequence Ω N) (n : ℕ) (t : ℝ≥0) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (i : Fin N) => ((S.X0m n i ω : ℝ), S.Z n i 0 ω)) inferInstance ⊔
  ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap
    (fun ω => ((fun i : Fin N => (S.E n i ω s, S.A n i ω s, S.D n i ω s, S.X n i ω s,
        S.T n i ω s)), S.A0 n ω s,
      (if 1 ≤ ⌊S.A0 n ω s⌋₊ then ((S.θ n ⌊S.A0 n ω s⌋₊ ω : ℕ) + 1) else 0 : ℕ)))
    inferInstance

/-- The sum of the squared jumps of a path over `(0, t]`,
`∑_{s ∈ (0,t]} (f(s) − f(s−))²`, computed in `[0, ∞]` (an unordered sum over the uncountable
interval: the supremum of its finite partial sums). For a càdlàg martingale of finite variation
this is its optional quadratic variation `[f](t)`. -/
noncomputable def sqJumpSum (f : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∑' s : Set.Ioc (0 : ℝ) t, ENNReal.ofReal ((f s - Function.leftLim f s) ^ 2)

end RankBasedSDI.LoadBalancing


