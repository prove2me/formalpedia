-- Prove2me | Definitions.Def_JSEQDelay_Diffusion_Example3
-- name    : JSEQDelay_Diffusion_Example3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:35.813475+00:00
-- url     : https://prove2.me/theorems/b0788cdf-7333-4964-8394-3e819336df72
-- title:
--   Example 3, pp. 12–13, (34)–(36) — estimators built from a function h, with η uniform in T
-- statement:
--   Let $h:\mathbb R_+\times\mathbb R_+^K\times\mathbb R^K\to\mathbb R_+^K$ satisfy $h(0,0,0)=0$ and the continuity property (34): there is $\eta\in[0,1)$ such that for each $T<\infty$ there is a non-decreasing continuous $\kappa:[0,T]\to\mathbb R_+$ with $\kappa(0)=0$ and, for all $t,t'\in[0,T]$, $v,v'\in\mathbb R_+^K$, $u,u'\in\mathbb R^K$ and $k$,
--   $$|h_k(t,v,u)-h_k(t',v',u')|\le\kappa(|t-t'|)+|v_k-v'_k|+\eta|u_k-u'_k|.$$
--   The Example 3 estimator is (35)
--   $$\Psi^n(q,a)(t)=\sqrt n\,h\Big(t,\frac{q(\tau(t))}{\sqrt n},\frac{a[\tau(t),t]-\nu^n(t)}{\sqrt n}\Big),\qquad \nu^n_k(t)=\mu^n_k(t-\tau_k(t)),$$
--   and its limiting estimator is (36) $\hat\Psi(q,a)(t)=h(t,q(\tau(t)),a[\tau(t),t])$.
--
--   This class contains the first three estimators of §7 and is the paper's main example of estimators satisfying Assumptions 3.5, 3.8 and 3.9 (Lemma 3.10).
--
--   **Formalization Note** The page lets the constant $\eta$ depend on $T$. Under that reading Lemma 3.10 is false: with $\tau\equiv0$ and $h_k(t,v,u)=\frac{t}{1+t}\min(u_k^+,1)$, condition (34) holds with $\eta_T=T/(1+T)$, but a jump of size $\varepsilon\le1$ in $a_k$ at time $t_0$ forces $\frac{t_0}{1+t_0}\le\zeta_1$ in (37) for every $t_0$. The condition here takes one $\eta$ for all $T$ ($\kappa$ still depends on $T$). The printed (35) has an unbalanced parenthesis; it is read as above.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), pp. 12–13, Example 3, (33)–(36)

import Mathlib
import Definitions.Def_JSEQDelay_Diffusion_Model

namespace JSEQDelay.Diffusion

/-!
Atar & Lipshutz (authors' manuscript of January 12, 2020), Example 3, pp. 12–13: the class of
estimators built from a function `h : ℝ₊ × ℝ₊^K × ℝ^K → ℝ₊^K`.
-/

/-- The conditions of Example 3 (p. 13) on `h : ℝ₊ × ℝ₊^K × ℝ^K → ℝ₊^K`, **with the constant
`η` uniform in `T`** (the page lets `η` depend on `T`, under which Lemma 3.10 fails):
`h` is non-negative on its domain, `h(0, 0, 0) = 0`, and there is `η ∈ [0, 1)` such that for each
`T ≥ 0` there is a non-decreasing continuous `κ : [0, T] → ℝ₊` with `κ(0) = 0` and, for all
`t, t' ∈ [0, T]`, `v, v' ∈ ℝ₊^K`, `u, u' ∈ ℝ^K` and `k`, (34):
`|h_k(t, v, u) − h_k(t', v', u')| ≤ κ(|t − t'|) + |v_k − v'_k| + η |u_k − u'_k|`. -/
def Example3Uniform {K : ℕ} (h : ℝ → (Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  (∀ t, 0 ≤ t → ∀ v : Fin K → ℝ, (∀ k, 0 ≤ v k) → ∀ u k, 0 ≤ h t v u k) ∧
  h 0 0 0 = 0 ∧
  ∃ η : ℝ, 0 ≤ η ∧ η < 1 ∧ ∀ T : ℝ, 0 ≤ T → ∃ κ : ℝ → ℝ,
    MonotoneOn κ (Set.Icc 0 T) ∧ ContinuousOn κ (Set.Icc 0 T) ∧ κ 0 = 0 ∧
    (∀ x ∈ Set.Icc 0 T, 0 ≤ κ x) ∧
    ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ∀ v v' : Fin K → ℝ, (∀ k, 0 ≤ v k) →
      (∀ k, 0 ≤ v' k) → ∀ (u u' : Fin K → ℝ) (k : Fin K),
        |h t v u k - h t' v' u' k| ≤ κ |t - t'| + |v k - v' k| + η * |u k - u' k|

/-- The Example 3 estimator (35), p. 13:
`Ψⁿ(q, a)(t) = √n h(t, q(τ(t))/√n, (a[τ(t), t] − νⁿ(t))/√n)` with `νⁿ_k(t) = μⁿ_k(t − τ_k(t))`. -/
noncomputable def ex3Psi {K : ℕ} (n : ℕ) (mu : Fin K → ℝ) (τ : ℝ → Fin K → ℝ)
    (h : ℝ → (Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ) : Path K → Path K → Path K :=
  fun q a t k => Real.sqrt n *
    h t (fun j => q (τ t j) j / Real.sqrt n)
      (fun j => (a t j - a (τ t j) j - mu j * (t - τ t j)) / Real.sqrt n) k

/-- The Example 3 limiting estimator (36), p. 13: `Ψ̂(q, a)(t) = h(t, q(τ(t)), a[τ(t), t])`. -/
noncomputable def ex3PsiLim {K : ℕ} (τ : ℝ → Fin K → ℝ)
    (h : ℝ → (Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ) : Path K → Path K → Path K :=
  fun q a t k => h t (fun j => q (τ t j) j) (fun j => a t j - a (τ t j) j) k

end JSEQDelay.Diffusion


