-- Prove2me | Definitions.Def_PolyContract_Supplement_HypC15
-- name    : PolyContract_Supplement_HypC15
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:01:04.789369+00:00
-- url     : https://prove2.me/theorems/4675ceac-7c18-4287-9a6e-8b1412a22541
-- title:
--   Hypotheses (W1)–(W6) of Lemma C.15, (T1)–(T3) of Theorem C.18, and $S_2$
-- statement:
--   At the step $k\to k+1$, with $\mu:=\mu_{k+1}$, $R_1:=R^{(k)}_1$, window $\mathcal R:=[R_0,R_1]$, $E:=E_k\cup\{\tau_1,\tau_2\}$, $b:=b_{k+1}$, $t_b=m_b/\beta_b$ and $t_{\tau_i}=m_\delta/\beta_\delta$:
--   $$\theta_1(\alpha):=\frac{\alpha(t_b+t_{\tau_1})-(K-d(E)+F_{\tau_1})}{1/\beta_b+1/\beta_\delta},\qquad \theta_2(\alpha):=\frac{\alpha(t_b+t_{\tau_2})-(K+F_{\tau_2}-w/\beta_\delta)}{1/\beta_b+1/\beta_\delta},$$
--   $u_1:=\theta_1-\rho^f_{\tau_1}$, $u_2:=\theta_2-\rho^f_{\tau_2}$, $\varphi:=\beta_\delta\Delta F/w$. The **hypotheses of Lemma C.15** are:
--
--   1. (W1) $s\iota<u_1(R_0)$ and $u_1(R_1)<w$;
--   2. (W2) $0<u_2(R_0+\mu)$ and $u_2(R_1+\mu)<w$;
--   3. (W3) $\rho^{(k)}_e(\alpha)>\rho^h_{\tau_1}(\alpha)$ for all $e\in E_k$, $\alpha\in\mathcal R$;
--   4. (W4) $\rho^h_e(\alpha)<\theta_2(\alpha)$ for all $e\in E_k$, $\alpha\in\mathcal R+\mu$;
--   5. (W5) $\varphi>1$;
--   6. (W6) $t_b/\beta^{-1}(E\cup\{b\})>M$.
--
--   With the weighted mean $\bar m_D:=t(D)/\beta^{-1}(D)$ and $S_2(D):=\sum_{e\in D}(m_e-\bar m_D)^2/\beta_e$, the hypotheses of Theorem C.18 for old elements $e_t,e_l$ are: (T1) $\psi_{k+1}\ge S_2((E_k\setminus\{e_t\})\cup\{b\})$ and $S_2(\{b,e_t\})\ge q_{k+1}$, and, if $e_l\ne e_t$, also $S_2(\{b,\tau_2,e_l\})\ge q_{k+1}$; (T2) on the transition $[R_1,R_0+\mu]$, $\rho^h_{\tau_1}<\rho^f_e<\rho^f_{\tau_2}<\rho^h_{e'}\le\rho^h_{e_l}$ for all $e,e'\in E_k$; (T3) $\theta_2\le\rho^h_{e_l}$ at $R_0+\mu-\iota$.
--
--   **Formalization Note** $u_1,u_2$ use the full-plane marginals $\rho^f_{\tau_i}$, as the page does, not their closed forms.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Lemma C.15, p.61 (PDF p.62); §C.6.1, p.60; App. B.6.1, p.29 ((B.8)–(B.9)); Theorem C.18, p.64

import Mathlib
import Definitions.Def_PolyContract_Supplement_gfun

set_option autoImplicit false

namespace PolyContract.Supplement

open LevelParams

/-- `θ₁(α) := (α(t_b + t_{τ1}) − (K − d(E) + F_{τ1}))/(1/β_b + 1/β_δ)` at the step `k → k+1`
(Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…,
§C.6.1, p.60), with `t_b = m_b/β_b`, `t_{τ1} = m_δ/β_δ`, and `K = K_{k+1}`, `F_{τ1} = F^{(k+1)}_{τ1}`. -/
noncomputable def θ1 (μin : List ℕ) (k : ℕ) (α : ℝ) : ℝ :=
  (α * (mb k / βb k + mδ k / βδ k) - ((params μin (k + 1)).K - dE μin k + (params μin (k + 1)).Fτ1)) /
    (1 / βb k + 1 / βδ k)

/-- `θ₂(α) := (α(t_b + t_{τ2}) − (K + F_{τ2} − w/β_δ))/(1/β_b + 1/β_δ)` at the step `k → k+1`
(arXiv:2611.04934, §C.6.1, p.60). -/
noncomputable def θ2 (μin : List ℕ) (k : ℕ) (α : ℝ) : ℝ :=
  (α * (mb k / βb k + mδ k / βδ k) - ((params μin (k + 1)).K + (params μin (k + 1)).Fτ2 - w μin k / βδ k)) /
    (1 / βb k + 1 / βδ k)

/-- `u₁ := θ₁ − ρ^f_{τ1}` at the step `k → k+1` (arXiv:2611.04934, §C.6.1, p.60). -/
noncomputable def u1 (μin : List ℕ) (k : ℕ) (α : ℝ) : ℝ := θ1 μin k α - rhoF μin k α (tau1 (k + 1))

/-- `u₂ := θ₂ − ρ^f_{τ2}` at the step `k → k+1` (arXiv:2611.04934, §C.6.1, p.60). -/
noncomputable def u2 (μin : List ℕ) (k : ℕ) (α : ℝ) : ℝ := θ2 μin k α - rhoF μin k α (tau2 (k + 1))

/-- `φ := β_δ ∆F/w` at the step `k → k+1` (arXiv:2611.04934, §C.6.1, p.60). -/
noncomputable def φ (μin : List ℕ) (k : ℕ) : ℝ := βδ k * ΔF μin k (params μin k) / w μin k

/-- The **hypotheses (W1)–(W6) of Lemma C.15** at the step `k → k+1` (arXiv:2611.04934,
Lemma C.15, p.61), with `µ := µ_{k+1}`, `R₁ := R^{(k)}_1` and the window `𝓡 = R_k = [R₀, R₁]`:
(W1) `sι < u₁(R₀)` and `u₁(R₁) < w`; (W2) `0 < u₂(R₀ + µ)` and `u₂(R₁ + µ) < w`;
(W3) `ρ^{(k)}_e(α) > ρ^h_{τ1}(α)` for all `e ∈ E_k` and `α ∈ 𝓡`;
(W4) `ρ^h_e(α) < θ₂(α)` for all `e ∈ E_k` and `α ∈ 𝓡 + µ`; (W5) `φ > 1`;
(W6) `t_b/β⁻¹(E ∪ {b}) > M`. -/
def HypC15 (μin : List ℕ) (k : ℕ) : Prop :=
  (sSlope k * iotaC < u1 μin k R0 ∧ u1 μin k (R1 μin k) < w μin k) ∧
  (0 < u2 μin k (R0 + μs μin (k + 1)) ∧ u2 μin k (R1 μin k + μs μin (k + 1)) < w μin k) ∧
  (∀ e ∈ Elev k, ∀ α ∈ Set.Icc R0 (R1 μin k), rhoH μin k α (tau1 (k + 1)) < rhoLev μin k α e) ∧
  (∀ e ∈ Elev k, ∀ α ∈ Set.Icc (R0 + μs μin (k + 1)) (R1 μin k + μs μin (k + 1)),
      rhoH μin k α e < θ2 μin k α) ∧
  1 < φ μin k ∧
  Mseq k < (mb k / βb k) / ∑ e ∈ Elev (k + 1), 1 / βU e

/-- The mean reward of `D`, weighted by `1/β`: `m̄_D := t(D)/β⁻¹(D)` (arXiv:2611.04934, App. B.6.1,
p.29), for the rewards and curvatures of the comb gadget. -/
noncomputable def meanW (D : Finset CombU) : ℝ :=
  (∑ e ∈ D, mU e / βU e) / ∑ e ∈ D, 1 / βU e

/-- The weighted sum of squares `S2(D) := Σ_{e ∈ D} (m_e − m̄_D)²/β_e` (arXiv:2611.04934,
App. B.6.1, p.29). -/
noncomputable def S2 (D : Finset CombU) : ℝ := ∑ e ∈ D, (mU e - meanW D) ^ 2 / βU e

/-- Hypothesis **(T1)** of Theorem C.18 at the step `k → k+1` (arXiv:2611.04934, p.64), with
`b = b_{k+1}`, `τ₂ = τ_{2,k+1}`: `ψ_{k+1} ≥ S2((E_k ∖ {e_t}) ∪ {b})` and `S2({b, e_t}) ≥ q_{k+1}`,
and, if `e_l ≠ e_t`, also `S2({b, τ₂, e_l}) ≥ q_{k+1}`. -/
def HypT1 (μin : List ℕ) (k : ℕ) (et el : CombU) : Prop :=
  S2 (insert (bnew (k + 1)) ((Elev k).erase et)) ≤ ψ k ∧
  (params μin (k + 1)).q ≤ S2 {bnew (k + 1), et} ∧
  (el ≠ et → (params μin (k + 1)).q ≤ S2 {bnew (k + 1), tau2 (k + 1), el})

/-- Hypothesis **(T2)** of Theorem C.18 at the step `k → k+1` (arXiv:2611.04934, p.64): on the
transition `[R₁, R₀ + µ]`, `ρ^h_{τ1} < ρ^f_e < ρ^f_{τ2} < ρ^h_{e′} ≤ ρ^h_{e_l}` for all
`e, e′ ∈ E_k`. -/
def HypT2 (μin : List ℕ) (k : ℕ) (el : CombU) : Prop :=
  ∀ α ∈ Set.Icc (R1 μin k) (R0 + μs μin (k + 1)), ∀ e ∈ Elev k, ∀ e' ∈ Elev k,
    rhoH μin k α (tau1 (k + 1)) < rhoF μin k α e ∧ rhoF μin k α e < rhoF μin k α (tau2 (k + 1)) ∧
      rhoF μin k α (tau2 (k + 1)) < rhoH μin k α e' ∧ rhoH μin k α e' ≤ rhoH μin k α el

/-- Hypothesis **(T3)** of Theorem C.18 at the step `k → k+1` (arXiv:2611.04934, p.64):
`θ₂ ≤ ρ^h_{e_l}` at `R₀ + µ − ι`. -/
def HypT3 (μin : List ℕ) (k : ℕ) (el : CombU) : Prop :=
  θ2 μin k (R0 + μs μin (k + 1) - iotaC) ≤ rhoH μin k (R0 + μs μin (k + 1) - iotaC) el

end PolyContract.Supplement


