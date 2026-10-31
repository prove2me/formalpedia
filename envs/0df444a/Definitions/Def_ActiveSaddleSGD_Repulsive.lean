-- Prove2me | Definitions.Def_ActiveSaddleSGD_Repulsive
-- name    : ActiveSaddleSGD_Repulsive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:05.37897+00:00
-- url     : https://prove2.me/theorems/c7273a12-312e-41d3-86b7-e58a5b9e4107
-- title:
--   The repulsive setting of §7: Lemma 8–9 type bounds and $U_n=\|w_n^-\|_Q$
-- statement:
--   Step sizes are nonnegative with $\sum\gamma_i=+\infty$ and $\sum\gamma_i^2<+\infty$. The **repulsion bounds** say that almost surely, for all $n$,
--   $$
--   \mathbb E_ne_{n+1}=0,\quad\mathbb E_n\|e_{n+1}\|^4\le C_{e,1},\quad\mathbb E_n\|\ell_{n+1}\|\ge C_{e,2},\quad\sum_i\|r_{i+1}\|^2\le c_r,
--   $$
--   $$
--   \mathbb E_n\|\tilde r_{n+1}\|^4\le C_{\tilde r},\quad\mathbb E_n\|\tilde r_{n+1}\|^2\le c_{\tilde r,1},\quad\chi_n^{-1/2}\mathbb E_n\Big[\sum_{i\ge n}\gamma_i\|\tilde r_{i+1}\|\Big]\le c_{\tilde r,2}.
--   $$
--   In the **repulsive setting**, $d^-\ge1$, the eigenvalues of $J^-$ have negative real parts, $Q$ is positive definite with $QJ^-+(J^-)^\top Q=-2I$, and $w^-$, $H$, $e$, $r$, $\tilde r$ are adapted with
--   $$
--   w_{n+1}^-=w_n^-+\gamma_nH_nw_n^-+\gamma_n(e_{n+1}+r_{n+1}+\tilde r_{n+1}),
--   $$
--   with, almost surely, $\|H_n+J^-\|\le c_H$, $\|Q(H_n+J^-)\|\le1/2$ and the bounds above with $\ell=e$. Finally $U_n=\sqrt{\langle w_n^-,Qw_n^-\rangle}$.
--
--   This is the setting in which $U_n$ is shown not to converge to $0$.
--
--   **Formalization Note** $\ell$ is the variable of the lower bound: $\tilde\eta^-$ in Lemma 8, $e$ in Lemma 9. Moments are `condLExp` of extended norms and the sums are in $[0,\infty]$, so no junk values arise, and the fourth moment bound makes the conditional mean genuine.
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Proposition 3, p.17; Lemma 8, pp.26–27; Lemma 9, p.27; §7.1–7.2, pp.28–29

import Mathlib
import Definitions.Def_ActiveSaddleSGD_ProjectedIterates
import Definitions.Def_ActiveSaddleSGD_CenterStable

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ActiveSaddleSGD

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Proposition 3, p.17: deterministic nonnegative
step sizes with `Σ γ_i = +∞` and `Σ γ_i² < +∞`. -/
structure IsStepSequence (γ : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ γ n
  not_summable : ¬ Summable γ
  summable_sq : Summable fun n => γ n ^ 2

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 8 iii)–ix), pp.26–27 and Lemma 9 ii)–viii),
p.27, which have the same shape: almost surely, for all `n`, `E_n e_{n+1} = 0`,
`E_n‖e_{n+1}‖⁴ ≤ Ce1`, `E_n‖ℓ_{n+1}‖ ≥ Ce2`, `Σ_i ‖r_{i+1}‖² ≤ cr`, `E_n‖r̃_{n+1}‖⁴ ≤ Crt`,
`E_n‖r̃_{n+1}‖² ≤ cr1`, and `χ_n^{-1/2} E_n[Σ_{i≥n} γ_i ‖r̃_{i+1}‖] ≤ cr2`.

**Formalization Note** `ℓ` is the variable in the lower bound: `η̃⁻` in Lemma 8 v), `e` in Lemma 9 iv).
Moments are `condLExp` of extended norms, and the sums are in `ℝ≥0∞`, so no value is a junk `0`. The
fourth moment bound makes `μ[e (n+1)|ℱ n]` a genuine conditional expectation. -/
structure RepulsionBounds {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [ENorm W] [ENorm X]
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (γ : ℕ → ℝ) (e : ℕ → Ω → V) (l : ℕ → Ω → W)
    (r rt : ℕ → Ω → X) (Ce1 Ce2 cr Crt cr1 cr2 : ℝ) : Prop where
  mean_zero : ∀ᵐ ω ∂μ, ∀ n, (μ[e (n + 1) | ℱ n]) ω = 0
  fourth : ∀ᵐ ω ∂μ, ∀ n, condLExp (ℱ n) μ (fun a => ‖e (n + 1) a‖ₑ ^ 4) ω ≤ ENNReal.ofReal Ce1
  lower : ∀ᵐ ω ∂μ, ∀ n, ENNReal.ofReal Ce2 ≤ condLExp (ℱ n) μ (fun a => ‖l (n + 1) a‖ₑ) ω
  sum_sq : ∀ᵐ ω ∂μ, ∑' i, ‖r (i + 1) ω‖ₑ ^ 2 ≤ ENNReal.ofReal cr
  rt_fourth : ∀ᵐ ω ∂μ, ∀ n, condLExp (ℱ n) μ (fun a => ‖rt (n + 1) a‖ₑ ^ 4) ω ≤ ENNReal.ofReal Crt
  rt_second : ∀ᵐ ω ∂μ, ∀ n, condLExp (ℱ n) μ (fun a => ‖rt (n + 1) a‖ₑ ^ 2) ω ≤ ENNReal.ofReal cr1
  rt_weighted : ∀ᵐ ω ∂μ, ∀ n,
    ENNReal.ofReal (tailChi γ n ^ (-(1 / 2) : ℝ)) *
      condLExp (ℱ n) μ
        (fun a => ∑' i, ENNReal.ofReal (γ (n + i)) * ‖rt (n + i + 1) a‖ₑ) ω ≤ ENNReal.ofReal cr2

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.29: `U_n = √⟨w_n⁻, Q w_n⁻⟩`, the norm of
`w_n⁻` for the scalar product `⟨·,·⟩_Q`. -/
noncomputable def lyapNorm {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (w : Ω → EuclideanSpace ℝ (Fin m)) (ω : Ω) : ℝ :=
  Real.sqrt (inner ℝ (w ω) (matCLM Q (w ω)))

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, §7.1–7.3, pp.27–30: the repulsive setting of
Lemmas 13 and 15. `J⁻ ∈ ℝ^{d⁻×d⁻}`, `d⁻ ≥ 1`, has eigenvalues with negative real parts; `Q` is
positive definite with `QJ⁻ + (J⁻)ᵀQ = −2I`; `(γ_n)` is as in Proposition 3; `w`, `H`, `e`, `r`,
`r̃` are adapted, with `w_{n+1}⁻ = w_n⁻ + γ_n H_n w_n⁻ + γ_n (e_{n+1} + r_{n+1} + r̃_{n+1})`, and
almost surely `‖H_n + J⁻‖ ≤ cH`, `‖Q(H_n + J⁻)‖ ≤ 1/2` and items ii)–viii) of Lemma 9.

**Formalization Note** The matrix norms are operator norms on Euclidean space. -/
structure RepulsiveSetting {m : ℕ} (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (γ : ℕ → ℝ)
    (Jm Q : Matrix (Fin m) (Fin m) ℝ) (w : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (H : ℕ → Ω → Matrix (Fin m) (Fin m) ℝ) (e r rt : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (cH Ce1 Ce2 cr Crt cr1 cr2 : ℝ) : Prop where
  dim_pos : 0 < m
  neg : HasNegRealParts Jm
  posDef : Q.PosDef
  lyapunov : Q * Jm + Jm.transpose * Q = -(2 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ)
  step : IsStepSequence γ
  adapted_w : StronglyAdapted ℱ w
  adapted_H : StronglyAdapted ℱ H
  adapted_e : StronglyAdapted ℱ e
  adapted_r : StronglyAdapted ℱ r
  adapted_rt : StronglyAdapted ℱ rt
  recursion : ∀ n ω, w (n + 1) ω = w n ω + γ n • matCLM (H n ω) (w n ω) +
    γ n • (e (n + 1) ω + r (n + 1) ω + rt (n + 1) ω)
  H_bound : ∀ᵐ ω ∂μ, ∀ n, ‖matCLM (H n ω + Jm)‖ ≤ cH
  QH_bound : ∀ᵐ ω ∂μ, ∀ n, ‖matCLM (Q * (H n ω + Jm))‖ ≤ 1 / 2
  bounds : RepulsionBounds μ ℱ γ e e r rt Ce1 Ce2 cr Crt cr1 cr2

end ActiveSaddleSGD


