-- Prove2me | Definitions.Def_NAPPAL_Subreg_Subregularity
-- name    : NAPPAL_Subreg_Subregularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:10:04.570757+00:00
-- url     : https://prove2.me/theorems/c84b48d5-1552-4ea5-9f1a-3f3404a5426a
-- title:
--   Definition 6.2, Assumption 3, p. 23 — metric subregularity of ∂L_γ around (w̄, 0) and the local value condition on stationary points
-- statement:
--   Let $\bar{\mathbf W}$ be the set of stationary points, $\bar{\mathbf W}=\{w:0\in\partial\mathcal L_\gamma(w)\}=(\partial\mathcal L_\gamma)^{-1}(0)$, and for $S\subseteq\mathbb R^n\times\mathbb R^d\times\mathbb R^m$ let $\mathrm{dist}(w,S)=\inf_{z\in S}\|w-z\|\in[0,+\infty]$, which is $+\infty$ when $S=\emptyset$.
--
--   **Metric subregularity (Definition 6.2, for $\mathcal H=\partial\mathcal L_\gamma$).** The map $\partial\mathcal L_\gamma$ is metrically subregular around $(\bar w,0)$ with radius $\eta>0$ and modulus $\kappa_3>0$ if
--   $$\mathrm{dist}\big(w,\bar{\mathbf W}\big)\le\kappa_3\,\mathrm{dist}\big(0,\partial\mathcal L_\gamma(w)\big)\qquad\text{for all } w\in\mathbb B(\bar w;\eta),$$
--   where $\mathbb B(\bar w;\eta)$ is the open Euclidean ball of radius $\eta$ around $\bar w$.
--
--   **Assumption 3 at a stationary $\bar w\in\bar{\mathbf W}$.** There is $\delta>0$ such that $\mathcal L_\gamma(w)\le\mathcal L_\gamma(\bar w)$ for every $w\in\bar{\mathbf W}$ with $\|w-\bar w\|\le\delta$.
--
--   These two conditions are the hypotheses of Proposition 6.2: subregularity converts a small stationarity residual into closeness to $\bar{\mathbf W}$, and Assumption 3 controls the value of $\mathcal L_\gamma$ at nearby stationary points.
--
--   **Formalization Note** Distances are computed in $[0,+\infty]$, so an empty $\partial\mathcal L_\gamma(w)$ gives $\mathrm{dist}(0,\partial\mathcal L_\gamma(w))=+\infty$ (p. 5's convention) and an empty $\bar{\mathbf W}$ gives $\mathrm{dist}(w,\bar{\mathbf W})=+\infty$. As on the page, metric subregularity does not require $0\in\partial\mathcal L_\gamma(\bar w)$, while Assumption 3 does require $\bar w$ to be stationary. Assumption 3's radius is named `δ3` in Lean to keep it apart from the step sequence $\delta_k$ of (8).
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, p. 23, Definition 6.2 and Assumption 3; p. 19, Definition 5.1 (the set W̄); p. 5 (dist(x, ∅) = +∞)

import Mathlib
import Definitions.Def_NAPPAL_Subreg_Setting

namespace NAPPAL.Subreg

open NAPPAL.Rate (qseq)
open NAPPAL.KL (wseq)

variable {n d m : ℕ}

/-- `dist(w, S) = inf {‖w − z‖ : z ∈ S}` in `[0, +∞]`, equal to `+∞` when `S = ∅` (p. 5). -/
noncomputable def distTo (w : NAPPAL.KL.W n d m) (S : Set (NAPPAL.KL.W n d m)) : ENNReal :=
  ⨅ z ∈ S, ENNReal.ofReal (NAPPAL.KL.wdist w z)

/-- The set `W̄` of all stationary points, `W̄ = (∂L_γ)^{-1}(0)` (Definition 5.1, p. 19). -/
def statSet (P : NAPPAL.KL.Problem n d m) (γ : ℝ) : Set (NAPPAL.KL.W n d m) := {z | NAPPAL.KL.IsStationary P γ z}

/-- Definition 6.2 (p. 23) for the set-valued map `ℋ = ∂L_γ`: `∂L_γ` is metrically subregular
around `(wbar, 0)` with radius `η > 0` and modulus `κ₃ > 0`:
`dist(w, (∂L_γ)^{-1}(0)) ≤ κ₃ dist(0, ∂L_γ(w))` for every `w` in the open ball `𝔹(wbar; η)`. -/
def MetricSubregularAt (P : NAPPAL.KL.Problem n d m) (γ : ℝ) (wbar : NAPPAL.KL.W n d m) (η κ3 : ℝ) : Prop :=
  0 < η ∧ 0 < κ3 ∧ ∀ w : NAPPAL.KL.W n d m, NAPPAL.KL.wdist w wbar < η →
    distTo w (statSet P γ) ≤ ENNReal.ofReal κ3 * NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ w)

/-- Assumption 3 (p. 23) at `wbar` with radius `δ₃ > 0`: `L_γ(w) ≤ L_γ(wbar)` for every
stationary point `w` with `‖w − wbar‖ ≤ δ₃`. -/
def Assumption3 (P : NAPPAL.KL.Problem n d m) (γ : ℝ) (wbar : NAPPAL.KL.W n d m) (δ3 : ℝ) : Prop :=
  NAPPAL.KL.IsStationary P γ wbar ∧ 0 < δ3 ∧
    ∀ w : NAPPAL.KL.W n d m, NAPPAL.KL.IsStationary P γ w → NAPPAL.KL.wdist w wbar ≤ δ3 →
    NAPPAL.KL.augLag P γ w ≤ NAPPAL.KL.augLag P γ wbar

end NAPPAL.Subreg


