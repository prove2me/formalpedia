-- Prove2me | Definitions.Def_SetConstrSOC_Directional_VarAnalysis
-- name    : SetConstrSOC_Directional_VarAnalysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:22.545001+00:00
-- url     : https://prove2.me/theorems/8733eb89-c3f1-43de-b772-debc51f964aa
-- title:
--   Variational-analysis objects: outer limits, tangent sets, normal cones, directional metric subregularity
-- statement:
--   For subsets $S$ of Euclidean space, this module defines the contingent cone $T_S(x)$, the outer second-order tangent set $T^2_S(x;d)$, the regular normal cone $\widehat N_S(x)$, the limiting normal cone $N_S(x)$, and the directional limiting normal cone $N_S(x;d)$. It also defines the sequential outer limit of a set-valued map. For a constraint map $g$ and set $\Lambda$, directional metric subregularity at $(\bar x,0)$ along $d$ means that some positive $\kappa,\rho,\delta$ satisfy
--
--   $$
--   \operatorname{dist}(\bar x+w,\{x:g(x)\in\Lambda\})\le\kappa\operatorname{dist}(g(\bar x+w),\Lambda)
--   \quad(w\in V_{\rho,\delta}(d)),
--   $$
--   where $V_{\rho,\delta}(d)=\{w:\|w\|\le\rho,\;\|\|d\|w-\|w\|d\|\le\delta\|w\|\|d\|\}$.
--
--   These objects form the reusable variational-analysis layer for the mission.
--
--   **Formalization Note** The limit definitions use sequences with positive $t_k\to0$; a decreasing sequence can be extracted. The tangent sets and normal cones are empty when their base point lies outside $S$, matching the definitions' stated domain $x\in S$.
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, pp. 3–8, outer limit, Definitions 1, 3, 4, 6

import Mathlib

open Filter
open scoped Topology
noncomputable section

namespace SetConstrSOC.Directional

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The sequential Painlevé–Kuratowski outer limit on p. 3. -/
def outerLimit {m n : ℕ} (C : E m → Set (E n)) (u : E m) : Set (E n) :=
  {v | ∃ (uk : ℕ → E m) (vk : ℕ → E n), Tendsto uk atTop (𝓝 u) ∧
    Tendsto vk atTop (𝓝 v) ∧ ∀ k, vk k ∈ C (uk k)}

/-- Definition 1, p. 4: the contingent cone. -/
def tangentCone {n : ℕ} (S : Set (E n)) (x : E n) : Set (E n) :=
  {d | x ∈ S ∧ ∃ (t : ℕ → ℝ) (dk : ℕ → E n), (∀ k, 0 < t k) ∧
    Tendsto t atTop (𝓝 0) ∧ Tendsto dk atTop (𝓝 d) ∧
    ∀ k, x + t k • dk k ∈ S}

/-- Definition 1, p. 4: the outer second-order tangent set. -/
def secondOrderTangentSet {n : ℕ} (S : Set (E n)) (x d : E n) : Set (E n) :=
  {w | x ∈ S ∧ ∃ (t : ℕ → ℝ) (wk : ℕ → E n), (∀ k, 0 < t k) ∧
    Tendsto t atTop (𝓝 0) ∧ Tendsto wk atTop (𝓝 w) ∧
    ∀ k, x + t k • d + ((1 / 2 : ℝ) * (t k)^2) • wk k ∈ S}

/-- Definition 3, p. 6: the Fréchet normal cone, empty off the set. -/
def regNormal {n : ℕ} (S : Set (E n)) (x : E n) : Set (E n) :=
  {v | x ∈ S ∧ ∀ ε > (0 : ℝ), ∀ᶠ y in 𝓝[S] x,
    inner ℝ v (y - x) ≤ ε * ‖y - x‖}

/-- Definition 3, p. 6: the limiting normal cone. -/
def limNormal {n : ℕ} (S : Set (E n)) (x : E n) : Set (E n) :=
  {v | x ∈ S ∧ ∃ (xk vk : ℕ → E n), Tendsto xk atTop (𝓝 x) ∧
    Tendsto vk atTop (𝓝 v) ∧ ∀ k, vk k ∈ regNormal S (xk k)}

/-- Definition 4, p. 6: the directional limiting normal cone. -/
def dirLimNormal {n : ℕ} (S : Set (E n)) (x d : E n) : Set (E n) :=
  {v | x ∈ S ∧ ∃ (t : ℕ → ℝ) (dk vk : ℕ → E n), (∀ k, 0 < t k) ∧
    Tendsto t atTop (𝓝 0) ∧ Tendsto dk atTop (𝓝 d) ∧
    Tendsto vk atTop (𝓝 v) ∧
    ∀ k, vk k ∈ regNormal S (x + t k • dk k)}

/-- Definition 6, p. 8: the directional neighborhood V_{ρ,δ}(d). -/
def dirNbhd {n : ℕ} (ρ δ : ℝ) (d : E n) : Set (E n) :=
  {w | ‖w‖ ≤ ρ ∧ ‖‖d‖ • w - ‖w‖ • d‖ ≤ δ * ‖w‖ * ‖d‖}

/-- Definition 6, p. 8, with an admissible error-bound constant κ. -/
def MetricSubregularDir {n m : ℕ} (g : E n → E m) (Λ : Set (E m))
    (x d : E n) (κ : ℝ) : Prop :=
  g x ∈ Λ ∧ 0 < κ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ w ∈ dirNbhd ρ δ d,
      Metric.infDist (x + w) {y | g y ∈ Λ} ≤ κ * Metric.infDist (g (x + w)) Λ

/-- Directional metric subregularity with some admissible κ. -/
def MetricSubregularDirAt {n m : ℕ} (g : E n → E m) (Λ : Set (E m))
    (x d : E n) : Prop :=
  ∃ κ : ℝ, MetricSubregularDir g Λ x d κ

end SetConstrSOC.Directional


