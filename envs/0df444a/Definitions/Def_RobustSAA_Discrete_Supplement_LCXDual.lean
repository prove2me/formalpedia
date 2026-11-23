-- Prove2me | Definitions.Def_RobustSAA_Discrete_Supplement_LCXDual
-- name    : RobustSAA_Discrete_Supplement_LCXDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:40:51.007343+00:00
-- url     : https://prove2.me/theorems/203af403-61b0-4767-b601-02c841d36626
-- title:
--   Theorem 14, (38)–(39) — the branch set $\mathcal G$, concave conjugates and the program $C'(x;\nu,\eta)$
-- statement:
--   Let $c(x;\xi)=\max_{k=1,\dots,K}c_k(x;\xi)$ as in (37), $\Xi\subseteq\mathbb R^d$, and data $\xi^1,\dots,\xi^N\in\Xi$.
--
--   1. $\mathcal G=\{0,1\}^K\setminus\{(0,\dots,0)\}$.
--   2. The concave conjugate $c_{k*}(x;\zeta)=\inf_{\xi\in\Xi}(\zeta^\top\xi-c_k(x;\xi))\in[-\infty,+\infty]$.
--   3. $C'(x;\nu,\eta)$, the optimal value of the linear program (38)–(39):
--   $$\min\ \nu f+\eta r+\sum_{\gamma\in\mathcal G}\sum_{i=1}^Nz_{\gamma,i}$$
--   over $r\in\mathbb R$, $z\in\mathbb R_+^{|\mathcal G|\times N}$, $y\in\mathbb R_+^{|\mathcal G|\times d}$, $y'\in\mathbb R_+^{|\mathcal G|}$, $w\in\mathbb R^{|\mathcal G|\times d}$, $w'\in\mathbb R^{|\mathcal G|}$, $f\ge0$, $g\in\mathbb R^K$, $h\in\mathbb R^{K\times d}$ subject to
--   $g_k-\sum_\gamma\gamma_kw'_\gamma+r\ge0$; $\tfrac1N(w_\gamma^\top\xi^i-w'_\gamma)\le z_{\gamma,i}$; $\pm w_\gamma\le y_\gamma$, $\pm w'_\gamma\le y'_\gamma$; $\sum_\gamma(\sum_jy_{\gamma,j}+y'_\gamma)\le f$; $h_k=\sum_\gamma\gamma_kw_\gamma$; $g_k\le c_{k*}(x;h_k)$.
--
--   **Formalization Note** $C'$ is the infimum of the objective over the feasible set in the extended reals ($+\infty$ if infeasible). The variables $w,w'$ are sign-free, whereas the page prints $w\in\mathbb R_+^{|\mathcal G|\times d}$, $w'\in\mathbb R_+^{|\mathcal G|}$; see the correction recorded with Theorem 14.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, (37)–(39) and Theorem 14, p. 21; §10.17 pp. 43–45

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Supplement_LCX

namespace RobustSAA.Discrete.Supplement

open MeasureTheory RobustSAA.Convergence
open scoped BigOperators

variable {d : ℕ} {Ξ : Set (Pt d)}

/-- The branch set `𝒢 = {0,1}^K ∖ {(0,…,0)}` of Theorem 14 (p. 21). -/
abbrev Branch (K : ℕ) := {γ : Fin K → Bool // γ ≠ fun _ => false}

/-- The `k`-th entry `γ_k ∈ {0, 1}` of a branch, as a real number. -/
def Branch.val {K : ℕ} (γ : Branch K) (k : Fin K) : ℝ :=
  if γ.1 k then 1 else 0

/-- The concave conjugate `c_{k*}(x; ζ) = inf_{ξ ∈ Ξ} (ζᵀξ − c_k(x; ξ))` (p. 21), valued in
`EReal` (`−∞` when the infimum is unbounded below, `+∞` when `Ξ = ∅`). -/
noncomputable def concConj {dx : ℕ} (Ξ : Set (Pt d)) (ck : Pt dx → Pt d → ℝ) (x : Pt dx)
    (ζ : Pt d) : EReal :=
  ⨅ ξ ∈ Ξ, ((inner ℝ ζ ξ - ck x ξ : ℝ) : EReal)

/-- Objective values `νf + ηr + Σ_{γ∈𝒢} Σᵢ z_{γ,i}` of the linear program (38)–(39) of
Theorem 14 at the feasible points
`r ∈ ℝ, z ∈ ℝ₊^{|𝒢|×N}, y ∈ ℝ₊^{|𝒢|×d}, y′ ∈ ℝ₊^{|𝒢|}, w ∈ ℝ^{|𝒢|×d}, w′ ∈ ℝ^{|𝒢|},
f ∈ ℝ₊, g ∈ ℝ^K, h ∈ ℝ^{K×d}` with
`g_k − Σ_γ γ_k w′_γ + r ≥ 0`; `(1/N)(w_γᵀξⁱ − w′_γ) ≤ z_{γ,i}`;
`±w_γ ≤ y_γ`, `±w′_γ ≤ y′_γ`; `Σ_γ (Σⱼ y_{γ,j} + y′_γ) ≤ f`; `h_k = Σ_γ γ_k w_γ`;
`g_k ≤ c_{k*}(x; h_k)`. The variables `w, w′` are sign-free (the page prints `ℝ₊`). -/
def lcxDualValues {dx K N : ℕ} (Ξ : Set (Pt d)) (ck : Fin K → Pt dx → Pt d → ℝ) (x : Pt dx)
    (s : Fin N → ↥Ξ) (ν η : ℝ) : Set ℝ :=
  {v | ∃ (r : ℝ) (z : Branch K → Fin N → ℝ) (y : Branch K → Fin d → ℝ) (y' : Branch K → ℝ)
      (w : Branch K → Pt d) (w' : Branch K → ℝ) (f : ℝ) (g : Fin K → ℝ) (h : Fin K → Pt d),
    (∀ γ i, 0 ≤ z γ i) ∧ (∀ γ j, 0 ≤ y γ j) ∧ (∀ γ, 0 ≤ y' γ) ∧ 0 ≤ f ∧
    (∀ k, 0 ≤ g k - (∑ γ, γ.val k * w' γ) + r) ∧
    (∀ γ i, (1 / (N : ℝ)) * (inner ℝ (w γ) ((s i : ↥Ξ) : Pt d) - w' γ) ≤ z γ i) ∧
    (∀ γ j, w γ j ≤ y γ j) ∧ (∀ γ j, -w γ j ≤ y γ j) ∧
    (∀ γ, w' γ ≤ y' γ) ∧ (∀ γ, -w' γ ≤ y' γ) ∧
    (∑ γ, ((∑ j, y γ j) + y' γ)) ≤ f ∧
    (∀ k, h k = ∑ γ, γ.val k • w γ) ∧
    (∀ k, ((g k : ℝ) : EReal) ≤ concConj Ξ (ck k) x (h k)) ∧
    v = ν * f + η * r + ∑ γ, ∑ i, z γ i}

/-- `C′(x; ν, η)` of Theorem 14: the optimal value of (38)–(39), i.e. the infimum (in `EReal`) of
its objective over its feasible set (`+∞` if infeasible, `−∞` if unbounded below). -/
noncomputable def lcxCprime {dx K N : ℕ} (Ξ : Set (Pt d)) (ck : Fin K → Pt dx → Pt d → ℝ)
    (x : Pt dx) (s : Fin N → ↥Ξ) (ν η : ℝ) : EReal :=
  sInf ((fun v : ℝ => (v : EReal)) '' lcxDualValues Ξ ck x s ν η)

end RobustSAA.Discrete.Supplement


