-- Prove2me | Definitions.Def_DirectedSearch_Approx_Setting
-- name    : DirectedSearch_Approx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:31.432393+00:00
-- url     : https://prove2.me/theorems/86af87cd-db6d-44b0-9059-9c7af2acb4ba
-- title:
--   §2–§3.2.1, §4.1 — directed-search market, program (6)/(6a)–(6f), the first-best relaxation, ρ_mw and LP (7)
-- statement:
--   **The market (§2).** There are finitely many types of agents on two sides, $\mathcal M$ and $\mathcal W$. Type $\theta$ arrives at rate $\alpha_\theta$, and every agent leaves the platform unmatched at rate $\delta$ (a "life event"). When agents of types $m$ and $w$ meet, they draw one common utility $u \sim F_{mw}$, a law on $\mathbb R$, and both receive $u$ if both accept. The **standing assumptions** are $\delta>0$, $\alpha_\theta>0$ for every type, and that each $F_{mw}$ is a probability law with no atoms ("continuous distribution") and finite mean. Write
--   $$\int_a^\infty dF_{mw} = \Pr_{u\sim F_{mw}}(u\ge a), \qquad \int_a^\infty u\,dF_{mw} = \mathbb E[u\,\mathbf 1\{u\ge a\}].$$
--
--   **Program (6) (§3.2.1).** A candidate consists of assortments $\lambda_m(w),\lambda_w(m)$, per-type thresholds $\tau_\theta$, matching rates $\xi_\theta$ and population masses $\eta_\theta$. It is *second-best feasible*, i.e. the assortments induce a stationary equilibrium, when for all types (with $\theta'$ ranging over the opposite side)
--
--   1. (6a) $\alpha_\theta = (\delta+\xi_\theta)\eta_\theta$;
--   2. (6b) $\eta_m\lambda_m(w)=\eta_w\lambda_w(m)$;
--   3. (6c) $\sum_{\theta'}\lambda_\theta(\theta')\le 1$;
--   4. (6d) $\xi_\theta=\sum_{\theta'}\lambda_\theta(\theta')\int_{\max(\tau_\theta,\tau_{\theta'})}^\infty dF_{\theta\theta'}$;
--   5. (6e) $\tau_\theta=\frac{1}{\delta+\xi_\theta}\sum_{\theta'}\lambda_\theta(\theta')\int_{\max(\tau_\theta,\tau_{\theta'})}^\infty u\,dF_{\theta\theta'}$;
--   6. (6f) $\lambda_m(w),\lambda_w(m)\ge0$.
--
--   Its welfare is the objective (6),
--   $$\sum_{m}\sum_{w}\eta_m\lambda_m(w)\int_{\max(\tau_m,\tau_w)}^\infty u\,dF_{mw}+\sum_{w}\sum_{m}\eta_w\lambda_w(m)\int_{\max(\tau_m,\tau_w)}^\infty u\,dF_{mw}.$$
--
--   **First best (§4.1).** The first-best relaxation drops the best-response constraint (6e) and replaces $\max(\tau_m,\tau_w)$ everywhere by a free pairwise threshold $\tau_{mw}$; its welfare is (6) with $\tau_{mw}$.
--
--   **LP (7) (Proposition 4.4).** For a law $F$ and $\delta$, $A(\tau)=\int_\tau^\infty u\,dF/(\delta+\int_\tau^\infty dF)$, and
--   $$\rho_{mw}:=\max_{\tau\ge0}\frac{\int_\tau^\infty u\,dF_{mw}}{\delta+\int_\tau^\infty dF_{mw}}.$$
--   A matrix $\beta$ is LP-feasible when $\beta\ge0$, $\sum_w\beta_{mw}\le\alpha_m$ for all $m$ and $\sum_m\beta_{mw}\le\alpha_w$ for all $w$; its objective is $2\sum_m\sum_w\rho_{mw}\beta_{mw}$.
--
--   These objects are the common vocabulary of every statement of the mission: Theorem 4.1 compares the welfare of a second-best feasible candidate with every first-best feasible one.
--
--   **Formalization Note.** The two sides are separate finite types `M`, `W`, and every per-type quantity comes in an `M`-copy and a `W`-copy; one law `F m w` serves both $F_{mw}$ and $F_{wm}$. "Continuous" is `NullSingletonClass` (no atoms; the current name of `NoAtoms`). $\alpha_\theta>0$ and integrability of the identity are disclosed additions the paper uses implicitly. Tails are taken over $[a,\infty)$ (`Set.Ici`), immaterial for atomless laws; masses are `toReal` of the measure. $\rho_{mw}$ is the real supremum of $A$ over $[0,\infty)$, a nonempty set bounded above by $\mathbb E|u|/\delta$; that it is attained is Lemma 4.5. $\beta\ge0$ is implicit in the paper through (9).
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, pp. 8–14, 20–21, §2.1–§2.3 (1)–(3), §3.2.1 program (6)/(6a)–(6f), §4.1 first-best relaxation, Proposition 4.4 LP (7) and ρ_mw, Lemma 4.5 A(τ)

import Mathlib

namespace DirectedSearch.Approx

open MeasureTheory

/-- The primitives of the directed-search market (§2, pp. 8–10): the life-event rate `δ`, the
arrival rates `α_m`, `α_w` of the two sides, and for each pair `(m, w)` the law `F m w` of the
common (symmetric) match utility `u ~ D_mw`; `D_wm := D_mw`, so one law serves both sides. -/
structure Market (M W : Type) where
  δ : ℝ
  αM : M → ℝ
  αW : W → ℝ
  F : M → W → Measure ℝ

/-- Standing assumptions of the model: `δ > 0`; `α_θ > 0` (implicit in the paper); every
`D_mw` is a probability law on `ℝ` with no atoms ("continuous distribution", p. 10) and an
integrable identity (implicit: `∫ u dF_mw` is used as a real number). -/
structure Market.Standing {M W : Type} (mk : Market M W) : Prop where
  delta_pos : 0 < mk.δ
  alphaM_pos : ∀ m, 0 < mk.αM m
  alphaW_pos : ∀ w, 0 < mk.αW w
  prob : ∀ m w, IsProbabilityMeasure (mk.F m w)
  noAtoms : ∀ m w, NullSingletonClass (mk.F m w)
  integrable : ∀ m w, Integrable id (mk.F m w)

/-- `∫_a^∞ dF`, the probability that the utility is at least `a`. -/
noncomputable def tailMass (μ : Measure ℝ) (a : ℝ) : ℝ := (μ (Set.Ici a)).toReal

/-- `∫_a^∞ u dF`, the expected utility on the event `u ≥ a`. -/
noncomputable def tailInt (μ : Measure ℝ) (a : ℝ) : ℝ := ∫ u in Set.Ici a, u ∂μ

/-- A candidate solution of program (6) (§3.2.1, p. 14): assortments `λ_m(w)`, `λ_w(m)`,
per-type thresholds `τ_θ`, matching rates `ξ_θ` and population masses `η_θ`. -/
structure Profile (M W : Type) where
  lamM : M → W → ℝ
  lamW : W → M → ℝ
  tauM : M → ℝ
  tauW : W → ℝ
  xiM : M → ℝ
  xiW : W → ℝ
  etaM : M → ℝ
  etaW : W → ℝ

/-- The acceptance threshold `max(τ_m, τ_w)` of the pair `(m, w)`. -/
def thr {M W : Type} (P : Profile M W) (m : M) (w : W) : ℝ := max (P.tauM m) (P.tauW w)

/-- Constraints (6a)–(6f) of program (6): the assortments induce a stationary equilibrium with
thresholds `τ`, matching rates `ξ` and masses `η`. -/
def SecondBestFeasible {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (P : Profile M W) : Prop :=
  -- (6a) stationarity
  (∀ m, mk.αM m = (mk.δ + P.xiM m) * P.etaM m) ∧
  (∀ w, mk.αW w = (mk.δ + P.xiW w) * P.etaW w) ∧
  -- (6b) flow balance
  (∀ m w, P.etaM m * P.lamM m w = P.etaW w * P.lamW w m) ∧
  -- (6c) capacity
  (∀ m, ∑ w, P.lamM m w ≤ 1) ∧
  (∀ w, ∑ m, P.lamW w m ≤ 1) ∧
  -- (6d) matching rates
  (∀ m, P.xiM m = ∑ w, P.lamM m w * tailMass (mk.F m w) (thr P m w)) ∧
  (∀ w, P.xiW w = ∑ m, P.lamW w m * tailMass (mk.F m w) (thr P m w)) ∧
  -- (6e) best response: thresholds equal expected utilities
  (∀ m, P.tauM m =
    (∑ w, P.lamM m w * tailInt (mk.F m w) (thr P m w)) / (mk.δ + P.xiM m)) ∧
  (∀ w, P.tauW w =
    (∑ m, P.lamW w m * tailInt (mk.F m w) (thr P m w)) / (mk.δ + P.xiW w)) ∧
  -- (6f) nonnegative assortments
  (∀ m w, 0 ≤ P.lamM m w) ∧
  (∀ w m, 0 ≤ P.lamW w m)

/-- The objective (6): the total flow of utility realised by matches. -/
noncomputable def sbWelfare {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (P : Profile M W) : ℝ :=
  (∑ m, ∑ w, P.etaM m * P.lamM m w * tailInt (mk.F m w) (thr P m w)) +
    ∑ w, ∑ m, P.etaW w * P.lamW w m * tailInt (mk.F m w) (thr P m w)

/-- A candidate solution of the first-best relaxation (§4.1, p. 20): as `Profile`, with a
pairwise threshold `τ_mw` in place of the per-type thresholds. -/
structure FBProfile (M W : Type) where
  lamM : M → W → ℝ
  lamW : W → M → ℝ
  tauMW : M → W → ℝ
  xiM : M → ℝ
  xiW : W → ℝ
  etaM : M → ℝ
  etaW : W → ℝ

/-- The first-best relaxation of (6) (§4.1, p. 20): (6a)–(6d) and (6f) with `τ_mw` in place of
`max(τ_m, τ_w)`, and without the best-response constraint (6e). -/
def FirstBestFeasible {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (Q : FBProfile M W) : Prop :=
  (∀ m, mk.αM m = (mk.δ + Q.xiM m) * Q.etaM m) ∧
  (∀ w, mk.αW w = (mk.δ + Q.xiW w) * Q.etaW w) ∧
  (∀ m w, Q.etaM m * Q.lamM m w = Q.etaW w * Q.lamW w m) ∧
  (∀ m, ∑ w, Q.lamM m w ≤ 1) ∧
  (∀ w, ∑ m, Q.lamW w m ≤ 1) ∧
  (∀ m, Q.xiM m = ∑ w, Q.lamM m w * tailMass (mk.F m w) (Q.tauMW m w)) ∧
  (∀ w, Q.xiW w = ∑ m, Q.lamW w m * tailMass (mk.F m w) (Q.tauMW m w)) ∧
  (∀ m w, 0 ≤ Q.lamM m w) ∧
  (∀ w m, 0 ≤ Q.lamW w m)

/-- The objective (6) of the first-best relaxation, with `τ_mw` as the pair's threshold. -/
noncomputable def fbWelfare {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (Q : FBProfile M W) : ℝ :=
  (∑ m, ∑ w, Q.etaM m * Q.lamM m w * tailInt (mk.F m w) (Q.tauMW m w)) +
    ∑ w, ∑ m, Q.etaW w * Q.lamW w m * tailInt (mk.F m w) (Q.tauMW m w)

/-- `A(τ) = ∫_τ^∞ u dF / (δ + ∫_τ^∞ dF)` (Lemma 4.5, p. 21; expression (11)). -/
noncomputable def ratio (μ : Measure ℝ) (δ : ℝ) (τ : ℝ) : ℝ := tailInt μ τ / (δ + tailMass μ τ)

/-- `ρ_mw := max_{τ ≥ 0} ∫_τ^∞ u dF_mw / (δ + ∫_τ^∞ dF_mw)` (Proposition 4.4, p. 20), as the
supremum of `A` over `[0, ∞)`. -/
noncomputable def rho {M W : Type} (mk : Market M W) (m : M) (w : W) : ℝ :=
  sSup (ratio (mk.F m w) mk.δ '' Set.Ici 0)

/-- Feasibility for the linear program (7) (Proposition 4.4, p. 20): `β ≥ 0`, (7a) and (7b). -/
def LPFeasible {M W : Type} [Fintype M] [Fintype W] (mk : Market M W) (β : M → W → ℝ) : Prop :=
  (∀ m w, 0 ≤ β m w) ∧ (∀ m, ∑ w, β m w ≤ mk.αM m) ∧ (∀ w, ∑ m, β m w ≤ mk.αW w)

/-- The objective of the linear program (7): `2 · Σ_m Σ_w ρ_mw · β_mw`. -/
noncomputable def lpObj {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (β : M → W → ℝ) : ℝ :=
  2 * ∑ m, ∑ w, rho mk m w * β m w

end DirectedSearch.Approx


