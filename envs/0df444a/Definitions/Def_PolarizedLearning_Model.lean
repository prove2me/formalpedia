-- Prove2me | Definitions.Def_PolarizedLearning_Model
-- name    : PolarizedLearning_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:07.992192+00:00
-- url     : https://prove2.me/theorems/c07a6110-02c4-4cc3-9dcd-ab279bc2f575
-- title:
--   Content-consumption model under polarization: parameters, posterior (2), expected posterior (3), log-likelihood (4), ML beliefs $\Pi(x)$, belief kernel, Assumption 1, $\bar q$
-- statement:
--   This module defines the model of Kadiyala and Shin's analysis of social learning from view counts when consumers hold polarized preferences (§3.2–§3.4, pp. 8–14, and the e-companion's Proof Preliminaries, p. ec1).
--
--   **Parameters** (pp. 8–11). The content has quality $q\in\{H,L\}$ with $H>L$. A consumer is in-group with probability $u\in(0,1)$ and then gains $p>0$ from consuming, out-group otherwise and then loses $p$; $L-p>0$ and $H+p<1$. Consumers know only that $u\in[u-\epsilon,u+\epsilon]\subseteq[0,1]$, with $\epsilon>0$. A private signal $r_t\in\{\text{"H"},\text{"L"}\}$ equals the true quality with probability $\alpha$, where $1/2<\alpha<1$.
--
--   **Beliefs and signals.**
--   1. The Bayesian posterior (2): $$g(\pi,\text{"H"})=\frac{\pi\alpha}{\pi\alpha+(1-\pi)(1-\alpha)},\qquad g(\pi,\text{"L"})=\frac{\pi(1-\alpha)}{\pi(1-\alpha)+(1-\pi)\alpha}.$$
--   2. The expected posterior (3): $f(\pi,H)=\alpha g(\pi,\text{"H"})+(1-\alpha)g(\pi,\text{"L"})$ and $f(\pi,L)=(1-\alpha)g(\pi,\text{"H"})+\alpha g(\pi,\text{"L"})$.
--
--   **Maximum likelihood inference** (p. 12). Under a belief $(\tilde\pi,\tilde u)$ a past consumer consumes with probability $\theta(\tilde\pi,\tilde u)=L+(H-L)\tilde\pi+p(2\tilde u-1)$. Consumer $t$, having seen $n_t$ views, maximizes the log-likelihood (4) $$\ell_t(n_t;\tilde\pi,\tilde u)=n_t\log\theta(\tilde\pi,\tilde u)+(t-n_t)\log\bigl(1-\theta(\tilde\pi,\tilde u)\bigr)$$ over $B_0=[0,1]\times[u-\epsilon,u+\epsilon]$. With $x=n_t/t$ this is $t$ times the normalized log-likelihood $\tilde\ell(x;\tilde\pi,\tilde u)=x\log\theta+(1-x)\log(1-\theta)$ (p. ec1). The ML set $B(x)$ is the set of maximizers of $\tilde\ell(x;\cdot)$ over $B_0$, the ML quality beliefs $\Pi(x)$ are its projection onto the first coordinate, and $\pi^-(x)=\inf\Pi(x)$, $\pi^+(x)=\sup\Pi(x)$. The projection $\mathrm{proj}_{[0,1]}(z)=\min(\max(z,0),1)$ is also defined (p. 12).
--
--   **Belief kernel and Assumption 1** (pp. 13–14). Consumer $t$ draws a belief $\pi_t\sim\Psi(n_t/t)$, where each $\Psi(x)$ is a probability measure on $\mathbb R$ with $\Psi(x)(\Pi(x))=1$ for $x\in[0,1]$. Assumption 1 requires $\Psi(x)\bigl((\pi^-(x),\pi^+(x))\bigr)>0$ whenever $\pi^-(x)<\pi^+(x)$.
--
--   **Quality estimate and consumption.** The average quality estimate (p. 14) at statistic $x$ is $\bar q(x)=L+(H-L)\int f(\pi,q)\,d\Psi(x)(\pi)$, and the mean consumption probability (EC.4) is $\bar q(x)+p(2u-1)$, with the true $u$. The view count is $n_t=\sum_{s=1}^{t-1}v_s$ (p. 10).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\epsilon$, $\alpha$, $\tilde\pi$, $\tilde u$ are written `eps`, `al`, `piT`, `uT`. Two conditions are readings, not printed: $\epsilon>0$ and $\alpha<1$. $\Pi(x)$ is the image of the argmax set, never the closed form (5). The kernel is one stationary function of $x=n_t/t$, not a sequence $\Psi_t$, and Assumption 1 is imposed only where $\Pi(x)$ is not a singleton, because literally it cannot hold where $\Pi(x)=\{1\}$. Quality labels and signals share one two-valued type. `sInf`/`sSup` and divisions never meet their junk values on the domains used.
-- source:
--   Kadiyala–Shin, Social Learning and Content Quality under Polarization, MSOM (2024), doi:10.1287/msom.2022.0533, §3.2–§3.4, pp. 8–14 (PDF 8–14): eqs. (1)–(4), (6), Assumption 1 (p. 14), q̄_t (p. 14); e-companion, Proof Preliminaries, (EC.1), (EC.4), p. ec1 (PDF 33)

import Mathlib

open MeasureTheory

namespace PolarizedLearning

/-- **Parameters and standing assumptions** of the content-consumption model of Kadiyala–Shin,
*Social Learning and Content Quality under Polarization*, MSOM (2024), doi:10.1287/msom.2022.0533,
§3.2–§3.3, pp. 8–11 (PDF 8–11).

* `H`, `L` are the two possible quality levels, `H > L` (p. 9).
* `p` is the polarization level, `p > 0` (p. 8); `L − p > 0` and `H + p < 1` (p. 9).
* `u ∈ (0,1)` is the proportion of in-group consumers (p. 8).
* `eps` is the degree of uncertainty `ϵ`: consumers know only `u ∈ [u−ϵ, u+ϵ] ⊆ [0,1]` (p. 9).
* `al` is the signal accuracy `α > 0.5` of the private signal (1) (p. 11).

**Formalization Note.** `eps` stands for `ϵ` and `al` for `α`. Two conditions are readings of
the source, not printed: `eps > 0` (the paper calls `ϵ` a "degree of uncertainty" and divides by
it on p. 17; with `ϵ = 0` the uncertainty is absent) and `al < 1` (the signal "noisily reveals"
the quality, p. 11; at `α = 1` learning is complete and Theorem 2 fails). -/
structure Params where
  H : ℝ
  L : ℝ
  p : ℝ
  u : ℝ
  eps : ℝ
  al : ℝ
  hLH : L < H
  hp : 0 < p
  hLp : 0 < L - p
  hHp : H + p < 1
  hu0 : 0 < u
  hu1 : u < 1
  heps : 0 < eps
  hlo : 0 ≤ u - eps
  hhi : u + eps ≤ 1
  hal_lo : 1 / 2 < al
  hal_hi : al < 1

/-- **Quality levels and signals**, Kadiyala–Shin, MSOM (2024), pp. 9 and 11 (PDF 9, 11):
the content quality `q ∈ {H, L}` and the private signal `r ∈ {"H", "L"}` both take one of two
labels; `high` stands for `H` (resp. the signal "H") and `low` for `L` (resp. "L"). -/
inductive Quality
  | high
  | low
  deriving DecidableEq

/-- The real value of a quality label: `high ↦ H`, `low ↦ L` (p. 9). -/
def Quality.val (P : Params) : Quality → ℝ
  | .high => P.H
  | .low => P.L

/-- **Bayesian posterior after a private signal**, eq. (2), Kadiyala–Shin, MSOM (2024), p. 11
(PDF 11): for prior `π` and signal `r`,
`g(π,"H") = πα / (πα + (1−π)(1−α))`, `g(π,"L") = π(1−α) / (π(1−α) + (1−π)α)`.

**Formalization Note.** For `1/2 < α < 1` and `π ∈ [0,1]` both denominators are positive, so
Lean's convention `a / 0 = 0` is never met on `[0,1]`. Outside `[0,1]` the formula is not used. -/
noncomputable def g (al π : ℝ) : Quality → ℝ
  | .high => π * al / (π * al + (1 - π) * (1 - al))
  | .low => π * (1 - al) / (π * (1 - al) + (1 - π) * al)

/-- **Expected posterior**, eq. (3), Kadiyala–Shin, MSOM (2024), p. 11 (PDF 11):
`f(π,Q) = E[g(π, r_t) | q = Q]`, i.e. `f(π,H) = α g(π,"H") + (1−α) g(π,"L")` and
`f(π,L) = (1−α) g(π,"H") + α g(π,"L")`. -/
noncomputable def f (al π : ℝ) : Quality → ℝ
  | .high => al * g al π .high + (1 - al) * g al π .low
  | .low => (1 - al) * g al π .high + al * g al π .low

/-- **Consumption probability under a belief** `(π̃, ũ)`, Kadiyala–Shin, MSOM (2024), p. 12
(PDF 12), display before (4): `θ(π̃, ũ) = L + (H − L)π̃ + p(2ũ − 1)`.

**Formalization Note.** On `B₀` the value lies in `[L − p, H + p] ⊂ (0,1)`. `piT`, `uT` stand
for `π̃`, `ũ`. -/
def theta (P : Params) (piT uT : ℝ) : ℝ :=
  P.L + (P.H - P.L) * piT + P.p * (2 * uT - 1)

/-- **Log-likelihood**, eq. (4), Kadiyala–Shin, MSOM (2024), p. 12 (PDF 12): for consumer `t`
having observed `n` views, `ℓ_t(n; π̃, ũ) = n log θ(π̃, ũ) + (t − n) log(1 − θ(π̃, ũ))`.

**Formalization Note.** `n` is real so that `ℓ_t(tx; ·)` of the e-companion makes sense. -/
noncomputable def loglik (P : Params) (t : ℕ) (n piT uT : ℝ) : ℝ :=
  n * Real.log (theta P piT uT) + ((t : ℝ) - n) * Real.log (1 - theta P piT uT)

/-- **Normalized log-likelihood**, Kadiyala–Shin, MSOM (2024), e-companion, Proof Preliminaries,
p. ec1 (PDF 33): `ℓ̃(x; π̃, ũ) := ℓ_t(tx; π̃, ũ)`, written here without `t` as
`x log θ(π̃, ũ) + (1 − x) log(1 − θ(π̃, ũ))`.

**Formalization Note.** `ℓ_t(tx; ·) = t · ℓ̃(x; ·)`, so for `t ≥ 1` the two have the same
maximizers; this `t`-free form is what makes the ML set a function of `x = n_t / t` only. On
`B₀`, `θ ∈ [L − p, H + p] ⊂ (0,1)`, so `Real.log` never meets `0`. -/
noncomputable def normLoglik (P : Params) (x piT uT : ℝ) : ℝ :=
  x * Real.log (theta P piT uT) + (1 - x) * Real.log (1 - theta P piT uT)

/-- **Feasible beliefs** `B₀ := [0,1] × [u − ϵ, u + ϵ]`, Kadiyala–Shin, MSOM (2024), p. 12
(PDF 12). -/
def B0 (P : Params) : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (P.u - P.eps) (P.u + P.eps)

/-- **Set of maximum likelihood estimates** `B(x) = argmax_{(π̃,ũ) ∈ B₀} ℓ̃(x; π̃, ũ)`,
Kadiyala–Shin, MSOM (2024), p. 12 (PDF 12, `B_t`) and p. ec1 (PDF 33, `B(x)`). -/
def mlSet (P : Params) (x : ℝ) : Set (ℝ × ℝ) :=
  {b | b ∈ B0 P ∧ ∀ b' ∈ B0 P, normLoglik P x b'.1 b'.2 ≤ normLoglik P x b.1 b.2}

/-- **ML quality beliefs** `Π(x)`: the projection of `B(x)` onto the first coordinate,
Kadiyala–Shin, MSOM (2024), p. 12 (`Π_t`, PDF 12) and p. ec1 (PDF 33).

**Formalization Note.** `Π(x)` is defined as the image of the argmax set, never by the
closed form (5); that it is an interval is a theorem (`mlProjection_eq`). -/
def Pi (P : Params) (x : ℝ) : Set ℝ :=
  Prod.fst '' mlSet P x

/-- **Lower ML belief** `π⁻(x) = inf Π(x)`, (EC.1), p. ec1 (PDF 33), and Assumption 1, p. 14.

**Formalization Note.** `sInf`; on the empty set it would be `0`, but `Π(x)` is a nonempty
compact interval for `x ∈ [0,1]` (`mlProjection_eq`). -/
noncomputable def piMinus (P : Params) (x : ℝ) : ℝ :=
  sInf (Pi P x)

/-- **Upper ML belief** `π⁺(x) = sup Π(x)`, (EC.1), p. ec1 (PDF 33), and Assumption 1, p. 14.

**Formalization Note.** `sSup`; see `piMinus`. -/
noncomputable def piPlus (P : Params) (x : ℝ) : ℝ :=
  sSup (Pi P x)

/-- **Projection onto `[0,1]`**, Kadiyala–Shin, MSOM (2024), p. 12 (PDF 12), after (5):
`proj_{[0,1]}(z) := min(max(z, 0), 1)`. -/
def proj01 (z : ℝ) : ℝ :=
  min (max z 0) 1

/-- **Belief kernel carried by the ML beliefs**, Kadiyala–Shin, MSOM (2024), pp. 13–14 (PDF 13–14):
"consumer t resolves uncertainty in quality belief `π_t ∈ Π_t` according to an arbitrary
probability distribution `Ψ_t ∈ ∆(Π_t)`". Here `Ψ` is one stationary kernel evaluated at the ML
statistic `x = n_t / t`, as in (EC.4), p. ec1: every `Ψ x` is a probability measure on `ℝ`, and for
`x ∈ [0,1]` it gives mass one to `Π(x)`.

**Formalization Note.** A kernel indexed by `t` is replaced by one kernel of `x`: with a
time-varying `Ψ_t` the convergence part of Theorem 2 is false (see the goal's differences). -/
def IsBeliefKernel (P : Params) (Ψ : ℝ → Measure ℝ) : Prop :=
  (∀ x, IsProbabilityMeasure (Ψ x)) ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, Ψ x (Pi P x) = 1

/-- **Assumption 1**, Kadiyala–Shin, MSOM (2024), p. 14 (PDF 14): `Ψ` is not a Dirac distribution
on an extreme point of `Π`, i.e. `P_Ψ(π ∈ (π⁻, π⁺)) > 0`.

**Formalization Note.** Read as required only where `Π(x)` is not a singleton (`π⁻(x) < π⁺(x)`).
Literally the assumption cannot hold where `Π(x) = {1}`, which happens with positive probability;
on a singleton the Dirac is the only distribution in `∆(Π(x))`. -/
def Assumption1 (P : Params) (Ψ : ℝ → Measure ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, piMinus P x < piPlus P x →
    0 < Ψ x (Set.Ioo (piMinus P x) (piPlus P x))

/-- **Average quality estimate** at ML statistic `x`, Kadiyala–Shin, MSOM (2024), p. 14 (PDF 14):
`q̄ = E[q_t]` with `q_t = (1 − g(π_t, r_t))L + g(π_t, r_t)H` (6), the expectation over
`π_t ∼ Ψ(x)` and `r_t` given the true quality `q`. Since `E[g(π, r_t) | q] = f(π, q)` (3), this is
`L + (H − L) ∫ f(π, q) dΨ(x)(π)`. -/
noncomputable def avgQuality (P : Params) (q : Quality) (Ψ : ℝ → Measure ℝ) (x : ℝ) : ℝ :=
  P.L + (P.H - P.L) * ∫ π, f P.al π q ∂(Ψ x)

/-- **Mean consumption probability** at ML statistic `x`, Kadiyala–Shin, MSOM (2024), e-companion
(EC.4), p. ec1 (PDF 33): `L + (H − L) E[f(π̃(x), q)] + p(2u − 1)` with `π̃(x) ∼ Ψ(x)` and the
**true** in-group proportion `u` (this is `h(x, q) + x`). -/
noncomputable def meanConsumption (P : Params) (q : Quality) (Ψ : ℝ → Measure ℝ) (x : ℝ) : ℝ :=
  avgQuality P q Ψ x + P.p * (2 * P.u - 1)

/-- **View count** `n_t := Σ_{s=1}^{t−1} v_s`, `n_1 = 0`, Kadiyala–Shin, MSOM (2024), p. 10
(PDF 10).

**Formalization Note.** Consumers are `t = 1, 2, …`; `v 0` is never used. -/
def viewCount {Ω : Type*} (v : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.Ico 1 t, v s ω

end PolarizedLearning


