-- Prove2me | Definitions.Def_PooledRationing_MaxWeighted_Algorithm
-- name    : PooledRationing_MaxWeighted_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:54.52044+00:00
-- url     : https://prove2.me/theorems/306592ba-98db-49ec-a8e4-498e3c143cf2
-- title:
--   Algorithm 1 and (25), (55), pp. 16–17, 53 — the step size γ_T, the dual iterates (26), G(w), G(w*) and L_t
-- statement:
--   This file defines the Max-Weighted-Service policy's learning procedure (Algorithm 1) and the quantities its analysis uses.
--
--   1. The **step size** for a horizon $T$ is $\gamma_T=T^{-(1/2+\epsilon)}$.
--   2. Given a selection $w\mapsto\varphi_w$ of deterministic policies, targets $\beta$, a constant step $\gamma$ and a demand path $D^{(1)},D^{(2)},\dots$, the **dual iterates** (26) start at $w^{(1)}=0$ and are
--   $$w^{(t+1)}_j=\Big[w^{(t)}_j+\gamma\cdot\Big(\beta_j-R_j\big(s_j(\varphi_{w^{(t)}},c,D^{(t)}),D^{(t)}_j\big)\Big)\Big]^+ ,\qquad j\in N.$$
--   3. The **dual function** of (25) is
--   $$G(w)=\sum_{j\in N}w_j\beta_j+E_{\tilde D}\big[g(w,c;\tilde D)\big],$$
--   with $g$ the optimal value of the Max-Weighted-Service problem (16); by Lemma 1, (17), the expectation equals $\min_{\varphi\in\Phi}F(w,\varphi)$, which is how (25) writes it.
--   4. $G(w^*)=\sup_{w\ge0}G(w)$, the optimal value of (25).
--   5. For the $T$-th run with step $\gamma$, the term (55) is
--   $$L_t=\frac{2}{T\gamma}\sum_{j\in N}\Big(w^{(t)}_j\,E_{D^{(t)}}\big[R_j(s_j(\varphi_{w^{(t)}},c,D^{(t)}),D^{(t)}_j)\big]-w^{(t)}_j\,R_j\big(s_j(\varphi_{w^{(t)}},c,D^{(t)}),D^{(t)}_j\big)\Big),$$
--   where the expectation is over a fresh demand with $w^{(t)}$ held fixed.
--
--   These are the objects of (57), Lemma 6 and Theorem 3: the iterates are a projected stochastic subgradient method for the dual problem (25), and $L_t$ is its martingale noise.
--
--   **Formalization Note.** The iterates are indexed from $0$: the Lean value at index $t$ is the page's $w^{(t+1)}$, and the demand path entry at index $t$ is the page's $D^{(t+1)}$. So the page's $w^{(1)}=0$ is the value at index $0$, $w^{(T+1)}$ is the value at index $T$, and $\sum_{t=1}^T$ becomes a sum over indices $0,\dots,T-1$. The step $\gamma$ is a parameter, constant within a run; Theorem 3 instantiates it with $\gamma_T$, which depends on the horizon $T$ and not on $t$. $G(w^*)$ is a supremum: the paper never shows the maximum of (25) is attained, and its proof uses only the supremum.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), pp. 16–17, 53, (25), Algorithm 1, (26), (55), Theorem 3 (step size)

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

namespace PooledRationing.MaxWeighted

open MeasureTheory

variable {n m : ℕ}

/-- The step size `γ_T = T^{-(1/2 + ϵ)}` of Theorem 3 (`Real.rpow`). -/
noncomputable def stepSize (ϵ : ℝ) (T : ℕ) : ℝ :=
  (T : ℝ) ^ (-(1 / 2 + ϵ))

/-- The iterates (26) of Algorithm 1 with a constant step `γ` along a demand path `d`.
Index shift: `mwsIter … t` is the page's `w^{(t+1)}` and `d t` is the page's `D^{(t+1)}`;
so `mwsIter … 0 = 0` is `w^{(1)} = 0` and `mwsIter … T` is `w^{(T+1)}`. -/
noncomputable def mwsIter {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)} {c : Fin m → ℝ}
    (sel : (Fin n → ℝ) → PooledRationing.AsymFeas.DetPolicy P c) (β : Fin n → ℝ) (R : Fin n → ℝ → ℝ → ℝ) (γ : ℝ)
    (d : ℕ → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => 0
  | t + 1 => fun j =>
      max 0 (mwsIter sel β R γ d t j +
        γ * (β j - R j (((sel (mwsIter sel β R γ d t)).toFun (d t)).1 j) (d t j)))

/-- The dual function `G(w)` of (25), with `min_{φ ∈ Φ} F(w, φ)` written as `E_D̃[PooledRationing.AsymFeas.g(w, c; D̃)]`
(the two coincide by Lemma 1, (17)). -/
noncomputable def G (F : Measure (Fin n → ℝ)) (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)) (c : Fin m → ℝ) (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j * β j + ∫ D, PooledRationing.AsymFeas.g P c f R w D ∂F

/-- `G(w*) = sup_{w ≥ 0} G(w)`, the optimal value of (25) (attainment is not assumed). -/
noncomputable def Gstar (F : Measure (Fin n → ℝ)) (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)) (c : Fin m → ℝ) : ℝ :=
  sSup (G F f R β P c '' {w | 0 ≤ w})

/-- `L_t` of (55) for the `T`-th run with step `γ` along the demand path `d`
(0-based `t`: the page's `L_{t+1}`). -/
noncomputable def Lterm (F : Measure (Fin n → ℝ)) (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)} {c : Fin m → ℝ}
    (sel : (Fin n → ℝ) → PooledRationing.AsymFeas.DetPolicy P c) (γ : ℝ) (T : ℕ) (d : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  2 / (T * γ) * ∑ j, (mwsIter sel β R γ d t j * PooledRationing.AsymFeas.detService F R (sel (mwsIter sel β R γ d t)) j -
    mwsIter sel β R γ d t j *
      R j (((sel (mwsIter sel β R γ d t)).toFun (d t)).1 j) (d t j))

end PooledRationing.MaxWeighted


