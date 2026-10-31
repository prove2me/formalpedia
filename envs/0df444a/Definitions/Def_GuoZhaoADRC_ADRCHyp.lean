-- Prove2me | Definitions.Def_GuoZhaoADRC_ADRCHyp
-- name    : GuoZhaoADRC_ADRCHyp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:11.450195+00:00
-- url     : https://prove2.me/theorems/b304e755-bf9d-45d2-8f4d-67a4c6bc8a4a
-- title:
--   Standing hypotheses of Theorem 3.1: (1.1), A1 (corrected), A2, A3, GA1, GA2 with (3.1) (corrected), GA3
-- statement:
--   The hypotheses under which Theorem 3.1 is stated, as a single predicate on the data:
--
--   1. **(1.1)** $f_i$ and $F_0$ are $C^1$; the disturbance $w$ is differentiable on $[0,\infty)$ and $\sup_{t\ge0}\|(w(t),\dot w(t))\|<\infty$.
--   2. **GA1** All partial derivatives of $f_i$, in all its arguments $(x,\xi,w_i)$, are bounded.
--   3. **GA2** The gains $a_{ik}$ are constants, the nominal matrix $(b_{ik})$ is invertible with inverse $(b^*_{kl})$, and
--   $$\min_i\lambda^i_{13}-\sqrt m\sum_{i,k,l=1}^m\beta^i_1\,|a_{ik}-b_{ik}|\,|b^*_{kl}|\,\Lambda^l_{n_l+1}>0. \tag{3.1}$$
--   4. **GA3** $\|F_0(x,\xi,w)\|\le K_1+K_2(\|x\|+\|w\|)$ for some $K_1,K_2>0$.
--   5. **A1 (corrected)** The reference satisfies $\dot z^i_j=z^i_{j+1}$ for $1\le j\le n_i$, $z^i_{n_i+1}$ is differentiable, and all components $z^i_1,\dots,z^i_{n_i+1}$ as well as $\dot z^i_{n_i+1}$ are bounded on $[0,\infty)$.
--   6. **A2** and **A3** (with $\varphi_i(0)=0$ from (1.4)).
--
--   Condition (3.1) says that the mismatch between the true and the nominal control gains is small compared with the decay rate of the observer.
--
--   **Formalization Note** Three printed hypotheses are corrected, each because the printed version makes Theorem 3.1 false (counterexamples in the mission description and in the goal's list of differences): the page's $a_{ik}(w_i)$ is a constant $a_{ik}$; (3.1) has $|b^*_{kl}|$ where the page has $b^*_{kl}$; A1, which bounds only $z^i_1,\dots,z^i_{n_i}$, is replaced by the bound on all $n_i+1$ components and on $\dot z^i_{n_i+1}$. The reference is any signal with the integrator chain property (every solution of the tracking differentiator (1.3) covered by Lemma 1.1 has it). GA1 is a bound on the operator norm of the Fréchet derivative of $(x,\xi,w_i)\mapsto f_i(x,\xi,w_i)$, equivalent in finite dimension to bounded partial derivatives. Derivatives along trajectories are taken within $[0,\infty)$.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, (1.1)–(1.2), p.1728; Assumption A1, p.1729; Assumptions A2, A3, pp.1729–1730; GA1, GA2, p.1736; (3.1), GA3, p.1737

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_minOver
import Definitions.Def_GuoZhaoADRC_AssumptionA2
import Definitions.Def_GuoZhaoADRC_AssumptionA3

namespace GuoZhaoADRC

/-- **The standing hypotheses of Theorem 3.1: the plant conditions of (1.1), A1 (corrected),
A2, A3, GA1, GA2 with (3.1) (corrected), GA3.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), (1.1)–(1.2), p.1728; A1, A2, p.1729; A3, p.1730;
GA1, GA2, p.1736; (3.1), GA3, p.1737.

* (1.1): `f_i` and `F₀` are `C¹`; `w` is differentiable on `[0, ∞)` with
  `sup_{t ≥ 0} ‖(w, ẇ)‖ < ∞`.
* GA1: all partial derivatives of `f_i`, in all its arguments `(x, ξ, w_i)`, are bounded.
* GA2: the gains `a_ik` are constants, the nominal matrix `(b_ik)` is invertible with inverse
  `(b*_kl)`, and (3.1):
  `min_i λ^i_13 − √m ∑_{i,k,l} β^i_1 |a_ik − b_ik| |b*_kl| Λ^l_{n_l+1} > 0`.
* GA3: `‖F₀(x, ξ, w)‖ ≤ K₁ + K₂(‖x‖ + ‖w‖)` with `K₁, K₂ > 0`.
* A1 (corrected): `ż^i_j = z^i_{j+1}` for `1 ≤ j ≤ n_i` (the integrator chain of the TD (1.3)),
  `z^i_{n_i+1}` is differentiable, and all components `z^i_j`, `1 ≤ j ≤ n_i + 1`, and
  `ż^i_{n_i+1}` are bounded on `[0, ∞)`.
* A2 and A3 (with (1.4)'s `φ_i(0) = 0`).

**Formalization Note.** Corrections of the printed hypotheses (each with a counterexample to
the printed version, see the mission description): `a_ik(w_i)` is replaced by a constant
`a_ik`; `b*_kl` in (3.1) is replaced by `|b*_kl|`; A1 (a bound on `z^i_1, …, z^i_{n_i}` only)
is replaced by the bound on all `n_i + 1` components and on `ż^i_{n_i+1}`. The reference is any
signal with the integrator-chain property, not necessarily a TD solution. GA1 is stated as a
bound on the operator norm of the Fréchet derivative of `(x, ξ, w_i) ↦ f_i(x, ξ, w_i)`, which in
finite dimension is equivalent to bounded partial derivatives. Derivatives along trajectories
are one-sided at `t = 0` (`HasDerivWithinAt … (Set.Ici 0) t`). -/
structure ADRCHyp {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s) : Prop where
  /-- `f_i` is `C¹` (1.1). -/
  f_contDiff : ∀ i, ContDiff ℝ 1
    (fun p : EuclideanSpace ℝ (Σ i : Fin m, Fin (n i)) × EuclideanSpace ℝ (Fin s) × ℝ =>
      D.f i p.1 p.2.1 p.2.2)
  /-- GA1: the derivative of `f_i` (in all arguments) is bounded. -/
  GA1 : ∀ i, ∃ K : ℝ, ∀ p, ‖fderiv ℝ
    (fun p : EuclideanSpace ℝ (Σ i : Fin m, Fin (n i)) × EuclideanSpace ℝ (Fin s) × ℝ =>
      D.f i p.1 p.2.1 p.2.2) p‖ ≤ K
  /-- `F₀` is `C¹` (1.1). -/
  F0_contDiff : ContDiff ℝ 1
    (fun p : EuclideanSpace ℝ (Σ i : Fin m, Fin (n i)) × EuclideanSpace ℝ (Fin s) ×
        EuclideanSpace ℝ (Fin m) => D.F0 p.1 p.2.1 p.2.2)
  /-- GA3: linear growth of the zero dynamics in `(x, w)`. -/
  GA3 : ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ x ξ w, ‖D.F0 x ξ w‖ ≤ K₁ + K₂ * (‖x‖ + ‖w‖)
  /-- GA2: the nominal gain matrix `(b_ik)` is invertible; `(b*_kl) = b⁻¹`. -/
  b_invertible : IsUnit D.b.det
  /-- (3.1), corrected (`a_ik` constant, `|b*_kl|`). -/
  cond_3_1 : 0 < minOver D.hm D.lam13 - Real.sqrt m *
    ∑ i, ∑ k, ∑ l, D.beta1 i * |D.a i k - D.b i k| * |D.b⁻¹ k l| * D.Λ l (Fin.last (n l))
  /-- `w` is differentiable on `[0, ∞)` with derivative `w'` (1.1). -/
  w_hasDeriv : ∀ t, 0 ≤ t → HasDerivWithinAt D.w (D.w' t) (Set.Ici 0) t
  /-- `sup_{t ≥ 0} ‖(w, ẇ)‖ < ∞` (1.1). -/
  w_bdd : ∃ C : ℝ, ∀ t, 0 ≤ t → ‖D.w t‖ ≤ C ∧ ‖D.w' t‖ ≤ C
  /-- The integrator chain `ż^i_j = z^i_{j+1}`, `1 ≤ j ≤ n_i`. -/
  z_chain : ∀ i (j : Fin (n i + 1)) (h : j.val < n i) t, 0 ≤ t →
    HasDerivWithinAt (fun τ => D.z τ i j) (D.z t i ⟨j.val + 1, by omega⟩) (Set.Ici 0) t
  /-- `z^i_{n_i+1}` is differentiable with derivative `zLast' i`. -/
  z_last : ∀ i t, 0 ≤ t →
    HasDerivWithinAt (fun τ => D.z τ i (Fin.last (n i))) (D.zLast' i t) (Set.Ici 0) t
  /-- A1 (corrected): every component of the reference is bounded. -/
  z_bdd : ∃ C : ℝ, ∀ t, 0 ≤ t → ∀ i j, |D.z t i j| ≤ C
  /-- A1 (corrected): `ż^i_{n_i+1}` is bounded. -/
  zLast'_bdd : ∃ C : ℝ, ∀ t, 0 ≤ t → ∀ i, |D.zLast' i t| ≤ C
  /-- Assumption A2. -/
  a2 : AssumptionA2 D
  /-- Assumption A3 and (1.4). -/
  a3 : AssumptionA3 D

end GuoZhaoADRC


