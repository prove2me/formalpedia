-- Prove2me | Definitions.Def_DirectedSearch_Equilibrium_Setting
-- name    : DirectedSearch_Equilibrium_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:25.556654+00:00
-- url     : https://prove2.me/theorems/381b45c7-8bb3-4259-8625-d2f531ab0125
-- title:
--   §2, §3.1, (5), App. A.3 — directed-search market, tail integrals, expected utility under threshold play, and the best-response map
-- statement:
--   This file sets up the model of a two-sided matching platform with directed search (Immorlica, Lucier, Manshadi, Wei, §2–§3.1).
--
--   **Market.** There are finitely many agent types on each side, $\mathcal M$ and $\mathcal W$. A market consists of a life-event (departure) rate $\delta$, arrival rates $\alpha_m$, $\alpha_w$, and for every pair $(m,w)\in\mathcal M\times\mathcal W$ the law $F_{mw}$ of the common utility $u$ that an $m$-agent and a $w$-agent both derive if they match (symmetric valuations; $F_{wm}:=F_{mw}$). The **standing assumptions** are: $\delta>0$; $\alpha_\theta>0$ for every type; each $F_{mw}$ is a probability law on $\mathbb R$ without atoms (a "continuous distribution") whose identity is integrable.
--
--   **Tails.** For a law $F$ on $\mathbb R$ and $a\in\mathbb R$,
--   $$\int_a^\infty dF = F([a,\infty)),\qquad \int_a^\infty u\,dF = \int_{[a,\infty)} u\,dF(u).$$
--
--   **One type's expected utility.** Given finitely many opposite types $i$ with meeting rates $\lambda_i$, thresholds $\tau_i$ and laws $F_i$, a type that thresholds at $t$ has expected payoff
--   $$B(t)=\frac{\sum_i \lambda_i\int_{\max(t,\tau_i)}^\infty u\,dF_i}{\delta+\sum_i \lambda_i\int_{\max(t,\tau_i)}^\infty dF_i},$$
--   and $\rho:=\sup_{t\ge 0}B(t)$ (Lemma B.1).
--
--   **Equation (5).** For assortments $\lambda_m(w)$, $\lambda_w(m)$ and a threshold profile $\tau=(\tau_m)_{m}\cup(\tau_w)_{w}$, the expected utility of type $m$ is
--   $$\bar u_m(\tau)=\frac{\sum_{w}\lambda_m(w)\int_{\max(\tau_m,\tau_w)}^\infty u\,dF_{mw}}{\delta+\sum_{w}\lambda_m(w)\int_{\max(\tau_m,\tau_w)}^\infty dF_{mw}},$$
--   and symmetrically for type $w$ with the sum over $m$. This is $B$ evaluated at $t=\tau_m$ with the opposite side's thresholds $\tau_w$.
--
--   **Best-response map (Appendix A.3).** A profile $\tau'$ is a best-response step from $\tau$ when each type's new threshold $t=\tau'_\theta$ solves its own equation $t=B(t)$, with the opposite side's thresholds taken from the input profile $\tau$. A **best-response sequence** starts at the all-zero profile and takes a best-response step at every iteration.
--
--   These objects are shared by every statement of the mission: the fixed point of (5) (Proposition 3.1), the one-type equation (Lemmas A.3, B.1) and the iteration (Proposition A.4).
--
--   **Formalization Note.** The two sides are separate finite types; a threshold profile is a pair $(\tau_{\mathcal M},\tau_{\mathcal W})$. "Continuous distribution" is the absence of atoms (`NullSingletonClass`, Mathlib's current name for `NoAtoms`). Integrability of the identity and $\alpha_\theta>0$ are implicit in the paper and stated explicitly. Tails use $[a,\infty)$; for atomless laws this agrees with $(a,\infty)$. The best-response map is a relation, not a function: Lemma A.3 shows it is total and single-valued.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, pp. 8–13, 36, 40, §2.1–§2.3, §3.1 eq. (5), Appendix A.3 (best response map), Lemma B.1 (map B)

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting

namespace DirectedSearch.Equilibrium

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

/-- One type's expected utility as a function of its own threshold `t`, the opposite types'
thresholds `τ' i`, meeting rates `lam i` and utility laws `F i` (the map `B` of Lemma B.1;
equation (5) with the opposite side fixed):
`B(t) = Σ_i lam_i ∫_{max(t,τ'_i)}^∞ u dF_i / (δ + Σ_i lam_i ∫_{max(t,τ'_i)}^∞ dF_i)`. -/
noncomputable def ownU {ι : Type} [Fintype ι] (δ : ℝ) (lam τ' : ι → ℝ) (F : ι → Measure ℝ)
    (t : ℝ) : ℝ :=
  (∑ i, lam i * DirectedSearch.Approx.tailInt (F i) (max t (τ' i))) /
    (δ + ∑ i, lam i * DirectedSearch.Approx.tailMass (F i) (max t (τ' i)))

/-- `ρ = max_{τ ≥ 0} B(τ)` of Lemma B.1, as the supremum of `B` over `[0, ∞)`. -/
noncomputable def ownRho {ι : Type} [Fintype ι] (δ : ℝ) (lam τ' : ι → ℝ) (F : ι → Measure ℝ) :
    ℝ :=
  sSup (ownU δ lam τ' F '' Set.Ici 0)

/-- Equation (5) for a type `m ∈ M` under the threshold profile `(τM, τW)` and assortments
`lamM`. -/
noncomputable def uM {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (lamM : M → W → ℝ) (τM : M → ℝ) (τW : W → ℝ) (m : M) : ℝ :=
  (∑ w, lamM m w * DirectedSearch.Approx.tailInt (mk.F m w) (max (τM m) (τW w))) /
    (mk.δ + ∑ w, lamM m w * DirectedSearch.Approx.tailMass (mk.F m w) (max (τM m) (τW w)))

/-- Equation (5) for a type `w ∈ W` under the threshold profile `(τM, τW)` and assortments
`lamW` (with `F_wm := F_mw`). -/
noncomputable def uW {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (lamW : W → M → ℝ) (τM : M → ℝ) (τW : W → ℝ) (w : W) : ℝ :=
  (∑ m, lamW w m * DirectedSearch.Approx.tailInt (mk.F m w) (max (τW w) (τM m))) /
    (mk.δ + ∑ m, lamW w m * DirectedSearch.Approx.tailMass (mk.F m w) (max (τW w) (τM m)))

theorem uM_eq_ownU {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (lamM : M → W → ℝ) (τM : M → ℝ) (τW : W → ℝ) (m : M) :
    uM mk lamM τM τW m = ownU mk.δ (lamM m) τW (mk.F m) (τM m) := rfl

theorem uW_eq_ownU {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (lamW : W → M → ℝ) (τM : M → ℝ) (τW : W → ℝ) (w : W) :
    uW mk lamW τM τW w = ownU mk.δ (lamW w) τM (fun m => mk.F m w) (τW w) := rfl

/-- One step of the best-response map of Appendix A.3 (p. 36), as a relation: `τ'` is the image
of the input profile `τ` when every type's new threshold `t` solves its own equation
`t = B(t)` (Lemma A.3) with the opposite side's thresholds taken from `τ`. -/
def IsBRStep {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (lamM : M → W → ℝ) (lamW : W → M → ℝ) (τ τ' : (M → ℝ) × (W → ℝ)) : Prop :=
  (∀ m, τ'.1 m = ownU mk.δ (lamM m) τ.2 (mk.F m) (τ'.1 m)) ∧
    (∀ w, τ'.2 w = ownU mk.δ (lamW w) τ.1 (fun m => mk.F m w) (τ'.2 w))

/-- A best-response sequence started at the all-zero threshold profile (p. 37):
`seq 0 = 0` and `seq (k+1)` is a best-response step from `seq k` for every `k`. -/
def IsBRSequence {M W : Type} [Fintype M] [Fintype W] (mk : Market M W)
    (lamM : M → W → ℝ) (lamW : W → M → ℝ) (seq : ℕ → (M → ℝ) × (W → ℝ)) : Prop :=
  seq 0 = 0 ∧ ∀ k, IsBRStep mk lamM lamW (seq k) (seq (k + 1))

end DirectedSearch.Equilibrium


