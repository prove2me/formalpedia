-- Prove2me | Definitions.Def_ContagionGrowth_FluidLimit_Limit
-- name    : ContagionGrowth_FluidLimit_Limit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:28.111313+00:00
-- url     : https://prove2.me/theorems/108734f8-96e0-4495-a158-d7e7b171b4c6
-- title:
--   Theorem 5, (6), (19), (23), Lemma 15, (DE), p. 25 — limit objects P_{λ,θ,ℓ}, B^α (corrected at θ = 0), J^α, π*, t̂, closed form s, δ
-- statement:
--   This file defines the deterministic limit objects of the threshold contagion model with growth of Amini, Minca and Sulem.
--
--   Throughout, $\lambda\in\mathbb N$ is a connectivity (degree), $\theta\in\mathbb N$ an initial threshold, $\ell\in\mathbb N$ a number of failed links, $0<\alpha<1$ the growth rate, and $\mu=(\mu_{\lambda,\theta})$ a probability distribution on $\mathbb N^2$.
--
--   1. **Order-statistic probability.** For $c\in\mathbb R$, $\pi>0$ and $\ell>\theta$, let $U_1,\dots,U_\ell$ be i.i.d. uniform on $[0,\pi]$ with order statistics $U_{(1)}\le\dots\le U_{(\ell)}$, and
--   $$P^{c}_{\theta,\ell}(\pi)=\mathbb P\big(U_{(u)}>c\,(u-\theta)\ \text{ for } u=\theta+1,\dots,\ell\big);$$
--   $P^{c}_{\theta,\ell}=1$ for $\ell\le\theta$. With $c=1/(\alpha\lambda)$ this is $P_{\lambda,\theta,\ell}(\pi)$ of (6), with thresholds $t_u=(u-\theta)/(\alpha\lambda)$; with $c=\bar\lambda/(\alpha\lambda)$ it is $P_{\lambda,\theta,\ell}(t)$ of (23), with thresholds $\hat t_{\lambda,\theta,u}=(u-\theta)\bar\lambda/(\alpha\lambda)$ of (19).
--   2. **Failure probability** $B^\alpha_{\lambda,\theta}(\pi)$: $B^\alpha_{\lambda,0}(\pi)=1$, and for $\theta\ge1$
--   $$B^\alpha_{\lambda,\theta}(\pi)=1-\sum_{\ell=0}^{\min\{\lceil\theta+\alpha\lambda\pi\rceil-1,\lambda\}}\binom{\lambda}{\ell}\pi^\ell(1-\pi)^{\lambda-\ell}P_{\lambda,\theta,\ell}(\pi).$$
--   3. **Mean connectivity** $\bar\lambda=\sum_{\lambda,\theta}\lambda\mu_{\lambda,\theta}$, and the map $J^\alpha(\pi)=\sum_{\lambda,\theta}\frac{\lambda\mu_{\lambda,\theta}}{\bar\lambda}B^\alpha_{\lambda,\theta}(\pi)$.
--   4. **Relaxed fixed point** $\pi^*=\inf\{\pi\in[0,1]\mid J^\alpha(\pi)\le\pi\}$, and **stability**: $\pi^*$ is a stable fixed point if $J^\alpha(\pi)<\pi$ for all $\pi$ in some interval $(\pi^*,\pi^*+\eta)$, $\eta>0$.
--   5. **Growth times** $\hat t_{\lambda,\theta,\ell}=(\ell-\theta)\bar\lambda/(\alpha\lambda)$ for $\ell\ge\theta$ and $0$ for $\ell\le\theta$ (19).
--   6. **The system (DE)** for one class $(\lambda,\theta)$ with mass $m$: a family $y=(y_\ell)_{0\le\ell\le\lambda}$ solves it on $[0,\bar\lambda)$ if $y_\ell(0)=m\,\mathbf 1(\ell=0)$, $y_\ell(t)=0$ for $0\le t<\hat t_{\lambda,\theta,\ell}$, and for $\hat t_{\lambda,\theta,\ell}\le t<\bar\lambda$ the right derivative of $y_\ell$ is
--   $$-\tfrac{\lambda}{\bar\lambda-t}y_0(t)\ (\ell=0),\qquad \tfrac{\lambda-\ell+1}{\bar\lambda-t}y_{\ell-1}(t)-\tfrac{\lambda-\ell}{\bar\lambda-t}y_\ell(t)\ (\ell\ge1).$$
--   7. **Closed form** of Lemma 15: $s_{\lambda,\theta,\ell}(t)=m\binom{\lambda}{\ell}(t/\bar\lambda)^\ell(1-t/\bar\lambda)^{\lambda-\ell}P_{\lambda,\theta,\ell}(t)$, with $P$ from (23).
--   8. **Failed mass** $\delta_{\lambda,\theta}(t)=\mu_{\lambda,\theta}-\sum_{\ell=0}^{\lambda}s_{\lambda,\theta,\ell}(t)$ for $\theta\ge1$ (with $m=\mu_{\lambda,\theta}$), and $\delta_{\lambda,0}(t)=\mu_{\lambda,0}$.
--
--   $B^\alpha_{\lambda,\theta}(\pi)$ is the limiting failure probability of a node of type $(\lambda,\theta)$ when each of its in-links has failed with probability $\pi$, and $\pi^*$ is the limiting fraction of failed links; Theorem 5 expresses the final fraction of failed nodes through them.
--
--   **Formalization Note.** The page prints the formula of item 2 for every $\theta$, but for $\theta=0$ it gives $B^\alpha_{\lambda,0}(\pi)<1$ when $\pi>0$, against the paper's own statement "$B^\alpha_{\lambda,0}(\pi^*)=1$. This follows by definition" (p. 9) and the proof's initial condition, under which threshold-0 nodes fail at time 0; with the printed formula Theorem 5 is false. Here $B^\alpha_{\lambda,0}:=1$. The upper limit $\min\{\lceil\theta+\alpha\lambda\pi\rceil-1,\lambda\}$ is encoded as "$\ell\le\lambda$ and $\ell<\lceil\theta+\alpha\lambda\pi\rceil$" (integer ceiling), which avoids natural-number subtraction. The event $U_{(u)}>s$ is encoded as $\#\{i\mid U_i\le s\}<u$, and the probability as the Lebesgue measure of the event in $[0,\pi]^\ell$ divided by $\pi^\ell$; for $\ell>\theta$ and $\pi\le0$ it is $0$. In (DE) the page prints $\bar\lambda-u$ in the second equation; it is read as $\bar\lambda-t$. $\pi^*$ is defined as an infimum; that the minimum is attained is Remark 6. For classes with $\theta>\lambda$, $\delta_{\lambda,\theta}$ uses the same closed form, which gives $0$ (such nodes cannot fail).
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), pp. 9, 12–13, 22, 24–25: Theorem 5, (6), Remark 6, (DE), (19), Lemma 15, (23), δ before (24)

import Mathlib

namespace ContagionGrowth.FluidLimit

open MeasureTheory

/-- Order-statistic crossing probability, encoded by counting.
For `l ≤ θ` it is `1`. For `θ < l` and `π > 0` it is the probability that the order statistics
`U_(θ+1) ≤ ⋯ ≤ U_(l)` of `l` i.i.d. uniform variables on `[0, π]` satisfy `U_(u) > c * (u - θ)` for
every `u = θ + 1, …, l`; the event `U_(u) > s` is written as `#{i | U_i ≤ s} < u`.
With `c = 1/(α λ)` this is `P_{λ,θ,l}(π)` of (6), p. 12; with `c = λ̄/(α λ)` it is
`P_{λ,θ,l}(t)` of (23), p. 24 (thresholds `t̂_{λ,θ,u} = (u - θ) λ̄/(α λ)`, (19)).
For `θ < l` and `π ≤ 0` the value is `0` (the set has measure zero and `0/0 = 0`). -/
noncomputable def Pord (c : ℝ) (θ l : ℕ) (π : ℝ) : ℝ :=
  if l ≤ θ then 1 else
    (volume {x : Fin l → ℝ | (∀ i, x i ∈ Set.Icc 0 π) ∧
      ∀ u : ℕ, θ + 1 ≤ u → u ≤ l →
        (Finset.univ.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u}).toReal / π ^ l

/-- `B^α_{λ,θ}(π)`, Theorem 5, p. 12, **corrected at `θ = 0`**: `B^α_{λ,0} := 1` (p. 9: "Note that
`B^α_{λ,0}(π*) = 1`. This follows by definition"). For `θ ≥ 1`,
`1 - Σ_{l ≤ λ, l < ⌈θ + αλπ⌉} C(λ,l) π^l (1-π)^{λ-l} P_{λ,θ,l}(π)`; the printed upper summation
limit `min{⌈θ + αλπ⌉ - 1, λ}` is exactly `l ≤ λ ∧ l < ⌈θ + αλπ⌉`. -/
noncomputable def Balpha (α : ℝ) (lam θ : ℕ) (π : ℝ) : ℝ :=
  if θ = 0 then 1 else
    1 - ∑ l ∈ (Finset.range (lam + 1)).filter (fun l : ℕ => (l : ℤ) < ⌈(θ : ℝ) + α * lam * π⌉),
      (lam.choose l : ℝ) * π ^ l * (1 - π) ^ (lam - l) * Pord (1 / (α * lam)) θ l π

/-- Limiting mean connectivity `λ̄ = Σ_{λ,θ} λ µ_{λ,θ}`, (4), p. 6. -/
noncomputable def lbar (mu : ℕ × ℕ → ℝ) : ℝ := ∑' p : ℕ × ℕ, (p.1 : ℝ) * mu p

/-- `J^α(π) = Σ_{λ,θ} (λ µ_{λ,θ}/λ̄) B^α_{λ,θ}(π)`, Theorem 5, p. 12. -/
noncomputable def Jalpha (mu : ℕ × ℕ → ℝ) (α : ℝ) (π : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, (p.1 : ℝ) * mu p / lbar mu * Balpha α p.1 p.2 π

/-- The relaxed fixed point `π* = min{π ∈ [0,1] | J^α(π) ≤ π}`, Theorem 5, p. 12 (as an infimum;
that it is attained is Remark 6). -/
noncomputable def piStar (mu : ℕ × ℕ → ℝ) (α : ℝ) : ℝ :=
  sInf {π : ℝ | π ∈ Set.Icc (0 : ℝ) 1 ∧ Jalpha mu α π ≤ π}

/-- `π*` is a stable fixed point of `J^α`: `J^α(π) < π` on some interval `(π*, π* + η)`
(Remark 6, p. 13, and the proof of Theorem 5, p. 29). -/
def IsStableFixedPoint (mu : ℕ × ℕ → ℝ) (α : ℝ) : Prop :=
  ∃ η > 0, ∀ π ∈ Set.Ioo (piStar mu α) (piStar mu α + η), Jalpha mu α π < π

/-- `t̂_{λ,θ,l} = (l - θ) λ̄/(α λ)` for `θ ≤ l`, and `0` for `l ≤ θ`, (19), p. 22. -/
noncomputable def tHat (lb α : ℝ) (lam θ l : ℕ) : ℝ :=
  if l ≤ θ then 0 else ((l : ℝ) - θ) * lb / (α * lam)

/-- The closed form of Lemma 15, p. 22, for one class `(λ, θ)` with mass `m = µ_{λ,θ}`:
`s_{λ,θ,l}(t) = m C(λ,l) (t/λ̄)^l (1 - t/λ̄)^{λ-l} P_{λ,θ,l}(t)` with `P` from (23)
(`P = 1` for `l ≤ θ`, giving (20)). -/
noncomputable def sClosed (m lb α : ℝ) (lam θ l : ℕ) (t : ℝ) : ℝ :=
  m * (lam.choose l : ℝ) * (t / lb) ^ l * (1 - t / lb) ^ (lam - l) * Pord (lb / (α * lam)) θ l t

/-- Right-hand side of the system (DE), p. 22, for one class `(λ, θ)` (the printed `λ̄ - u` in
the second equation is read as `λ̄ - t`). -/
noncomputable def deRhs (lb : ℝ) (lam : ℕ) (y : ℕ → ℝ → ℝ) (l : ℕ) (t : ℝ) : ℝ :=
  if l = 0 then -((lam : ℝ) / (lb - t)) * y 0 t
  else ((lam : ℝ) - l + 1) / (lb - t) * y (l - 1) t - ((lam : ℝ) - l) / (lb - t) * y l t

/-- `y = (y_l)_{0 ≤ l ≤ λ}` solves the system (DE), p. 22, of the class `(λ, θ)` with
`0 < θ ≤ λ` and mass `m` on `[0, λ̄)`: initial condition `y_l(0) = m 1(l = 0)`;
`y_l(t) = 0` for `t < t̂_{λ,θ,l}`; and for `t̂_{λ,θ,l} ≤ t < λ̄`, `y_l` has right derivative
equal to the right-hand side of (DE). -/
def SolvesDE (m lb α : ℝ) (lam θ : ℕ) (y : ℕ → ℝ → ℝ) : Prop :=
  (∀ l ≤ lam, y l 0 = if l = 0 then m else 0) ∧
  (∀ l ≤ lam, ∀ t : ℝ, 0 ≤ t → t < lb → t < tHat lb α lam θ l → y l t = 0) ∧
  (∀ l ≤ lam, ∀ t : ℝ, tHat lb α lam θ l ≤ t → t < lb →
    HasDerivWithinAt (y l) (deRhs lb lam y l t) (Set.Ici t) t)

/-- `δ_{λ,θ}(t) = µ_{λ,θ} - Σ_l s_{λ,θ,l}(t)`, p. 25, with `s` the closed form of Lemma 15.
Classes with `θ = 0` fail at time `0` (initial condition `1(0 < θ)`, p. 21), so
`δ_{λ,0} := µ_{λ,0}`. For `θ > λ` the same closed form is used; it gives `δ = 0`. -/
noncomputable def delta (mu : ℕ × ℕ → ℝ) (α : ℝ) (lam θ : ℕ) (t : ℝ) : ℝ :=
  if θ = 0 then mu (lam, 0) else
    mu (lam, θ) - ∑ l ∈ Finset.range (lam + 1), sClosed (mu (lam, θ)) (lbar mu) α lam θ l t

end ContagionGrowth.FluidLimit


