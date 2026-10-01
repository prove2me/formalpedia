-- Prove2me | Definitions.Def_Def_CAH21_SparsityInLevels
-- name    : Def_CAH21_SparsityInLevels
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T17:10:54.020032+00:00
-- url     : https://prove2.me/theorems/925cb997-934f-466f-a2d9-50605d2369d0
-- title:
--   Sparsity in levels and the weighted rNSP in levels (Defs. 1.6–1.7)
-- statement:
--   Sparsity in levels and the weighted robust null space property in levels (SI Appendix, Definitions 1.6 and 1.7).
--
--   Let $M=(M_1,\dots,M_r)$ with $1\le M_1<\dots<M_r=N$ and $M_0=0$, and let $s=(s_1,\dots,s_r)$ with $0<s_k\le M_k-M_{k-1}$. Level $k$ is the block of coordinates $\{M_{k-1}+1,\dots,M_k\}$. A vector $x\in\mathbb C^N$ is $(s,M)$-**sparse in levels** if it has at most $s_k$ nonzero entries in level $k$ for every $k$; a set $\Delta$ of coordinates is an $(s,M)$ **support set** if it has at most $s_k$ elements in level $k$. Weights $w_i>0$ are constant on levels, $w_i=w_{(k)}$ for $i$ in level $k$ (assumption (1.15)). Define
--   $$\|x\|_{l^1_w}=\sum_{i}w_i|x_i|,\qquad \sigma_{s,M}(x)_{l^1_w}=\inf\{\|x-z\|_{l^1_w}: z\in\Sigma_{s,M}\},$$
--   $$\xi=\sum_{k=1}^r w_{(k)}^2 s_k,\qquad \zeta=\min_{k} w_{(k)}^2 s_k,\qquad \kappa=\xi/\zeta .$$
--   A matrix $A\in\mathbb C^{m\times N}$ has the **weighted rNSP in levels** of order $(s,M)$ with constants $0<\rho<1$, $\gamma>0$ if for every $(s,M)$ support set $\Delta$,
--   $$\|x_\Delta\|_{l^2}\le \frac{\rho\,\|x_{\Delta^c}\|_{l^1_w}}{\sqrt\xi}+\gamma\|Ax\|_{l^2}\qquad\text{for all }x\in\mathbb C^N.$$
--   The file also defines the Euclidean norm, the spectral norm $\|A\|=\sup_{\|x\|_{l^2}\le1}\|Ax\|_{l^2}$, and the constants $C_1=\big(\tfrac{1+\rho}{2}+\tfrac{(3+\rho)\kappa^{1/4}}{4}\big)\tfrac{3+\rho}{1-\rho}$ and $C_2=2\big(\tfrac{3+\rho}{1-\rho}+\tfrac{7+\rho}{1-\rho}\tfrac{\kappa^{1/4}}{2}\big)\gamma$ of Theorem 3.
--
--   These definitions are the shared model for every statement of the mission.
--
--   **Formalization Note** Coordinates are numbered from $0$, so level $k$ is $\{i: M_{k-1}\le i<M_k\}$; the sequences $M,s,w_{(\cdot)}$ are indexed by $\mathbb N$ and only indices $0,\dots,r$ are used. The standing assumptions (including $r\ge1$ and (1.15)) are bundled in the predicate `LevelData.Valid`. The rNSPL predicate includes the constraints $0<\rho<1$, $\gamma>0$.
-- source:
--   Colbrook, Antun, Hansen, Can stable and accurate neural networks be computed? On the barriers of deep learning and Smale's 18th problem, arXiv:2101.08286v2 (PNAS 119(12), 2022), https://arxiv.org/abs/2101.08286, SI Appendix, p. 5, Definitions 1.6 and 1.7, assumption (1.15); constants C1, C2 from Theorem 3 (p. 6)

import Mathlib

/-!
Colbrook–Antun–Hansen (PNAS 2022, arXiv:2101.08286v2), SI Appendix §1.2.2:
sparsity in levels (Definition 1.6), the quantities `ξ, ζ, κ` and the weighted
robust null space property in levels (Definition 1.7).

Conventions: coordinates of `ℂ^N` are indexed by `Fin N` starting at `0`, so the
paper's level `{M_{k-1}+1, …, M_k}` is `{i : M (k-1) ≤ i < M k}`. Levels are
indexed by `k = 1, …, r` and the sequences `M, s, wl` are indexed by `ℕ`, with
`M 0 = 0` (the paper's convention `M_0 = 0`); values at indices outside
`0, …, r` are never used.
-/

namespace ColbrookAntunHansen

open Finset

/-- Sparsity-in-levels data: number of levels `r`, level boundaries `M`,
local sparsities `s`, coordinate weights `w` and level weights `wl`
(the paper's `w_{(k)}`). -/
structure LevelData (N : ℕ) where
  r : ℕ
  M : ℕ → ℕ
  s : ℕ → ℕ
  w : Fin N → ℝ
  wl : ℕ → ℝ

namespace LevelData

variable {N : ℕ} (L : LevelData N)

/-- Coordinate `i` lies in the `k`-th level `{M_{k-1}+1, …, M_k}` (0-indexed). -/
def InLevel (k : ℕ) (i : Fin N) : Prop := L.M (k - 1) ≤ i.val ∧ i.val < L.M k

instance (k : ℕ) : DecidablePred (L.InLevel k) := fun i => by
  unfold InLevel; infer_instance

/-- The standing assumptions of Definition 1.6 and of SI §1.2.2:
`M_0 = 0`, `1 ≤ M_1 < ⋯ < M_r = N` (with `r ≥ 1`), `0 < s_k ≤ M_k - M_{k-1}`,
positive weights, and (1.15): `w_i = w_{(k)}` whenever `i` is in level `k`. -/
def Valid : Prop :=
  1 ≤ L.r ∧ L.M 0 = 0 ∧ (∀ k, 1 ≤ k → k ≤ L.r → L.M (k - 1) < L.M k) ∧ L.M L.r = N ∧
  (∀ k, 1 ≤ k → k ≤ L.r → 0 < L.s k ∧ L.s k ≤ L.M k - L.M (k - 1)) ∧
  (∀ i, 0 < L.w i) ∧
  (∀ k, 1 ≤ k → k ≤ L.r → ∀ i, L.InLevel k i → L.w i = L.wl k)

/-- `Δ ⊆ {1,…,N}` is an `(s, M)` support set: it has at most `s_k` elements in level `k`. -/
def IsSupportSet (Δ : Finset (Fin N)) : Prop :=
  ∀ k, 1 ≤ k → k ≤ L.r → (Δ.filter (L.InLevel k)).card ≤ L.s k

/-- `x` is `(s, M)`-sparse in levels, i.e. `x ∈ Σ_{s,M}`. -/
def IsSparse (x : Fin N → ℂ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ L.r →
    ((Finset.univ.filter (fun i => x i ≠ 0)).filter (L.InLevel k)).card ≤ L.s k

/-- `ξ = ∑_{k=1}^r w_{(k)}^2 s_k`. -/
def xi : ℝ := ∑ k ∈ Finset.Icc 1 L.r, L.wl k ^ 2 * (L.s k : ℝ)

/-- `ζ = min_{k=1,…,r} w_{(k)}^2 s_k`. -/
noncomputable def zeta : ℝ := ⨅ k : Finset.Icc 1 L.r, L.wl k ^ 2 * (L.s k : ℝ)

/-- `κ = ξ / ζ`. -/
noncomputable def kappa : ℝ := L.xi / L.zeta

/-- `min_{k=1,…,r} w_{(k)}`. -/
noncomputable def minWeight : ℝ := ⨅ k : Finset.Icc 1 L.r, L.wl k

end LevelData

/-- Euclidean norm `‖x‖_{l^2}`. -/
noncomputable def l2norm {n : ℕ} (x : Fin n → ℂ) : ℝ := Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- Weighted `l^1` norm `‖x‖_{l^1_w} = ∑ w_i |x_i|`. -/
noncomputable def wl1norm {N : ℕ} (w : Fin N → ℝ) (x : Fin N → ℂ) : ℝ := ∑ i, w i * ‖x i‖

/-- Projection `P_Δ x` (keep the coordinates in `Δ`, zero the others). -/
def restrict {N : ℕ} (Δ : Finset (Fin N)) (x : Fin N → ℂ) : Fin N → ℂ :=
  fun i => if i ∈ Δ then x i else 0

/-- Euclidean operator norm `‖A‖ = sup {‖A x‖_{l^2} : ‖x‖_{l^2} ≤ 1}`. -/
noncomputable def opNorm {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℂ) : ℝ :=
  sSup ((fun x => l2norm (A.mulVec x)) '' {x | l2norm x ≤ 1})

/-- `σ_{s,M}(x)_{l^1_w} = inf {‖x - z‖_{l^1_w} : z ∈ Σ_{s,M}}`. -/
noncomputable def sigmaSM {N : ℕ} (L : LevelData N) (x : Fin N → ℂ) : ℝ :=
  sInf ((fun z => wl1norm L.w (x - z)) '' {z | L.IsSparse z})

/-- Definition 1.7: `A` has the weighted rNSP in levels of order `(s, M)` with constants
`0 < ρ < 1`, `γ > 0`: for every `(s, M)` support set `Δ` and every `x ∈ ℂ^N`,
`‖x_Δ‖_{l^2} ≤ ρ ‖x_{Δᶜ}‖_{l^1_w} / √ξ + γ ‖A x‖_{l^2}`. -/
def WeightedRNSPL {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℂ) (L : LevelData N) (ρ γ : ℝ) : Prop :=
  0 < ρ ∧ ρ < 1 ∧ 0 < γ ∧
  ∀ Δ : Finset (Fin N), L.IsSupportSet Δ → ∀ x : Fin N → ℂ,
    l2norm (restrict Δ x) ≤ ρ * wl1norm L.w (restrict Δᶜ x) / Real.sqrt L.xi + γ * l2norm (A.mulVec x)

/-- The constant `C₁ = ((1+ρ)/2 + (3+ρ) κ^{1/4}/4) · (3+ρ)/(1-ρ)` of Theorem 3. -/
noncomputable def constC1 (ρ κ : ℝ) : ℝ :=
  ((1 + ρ) / 2 + (3 + ρ) * κ ^ ((1 : ℝ) / 4) / 4) * ((3 + ρ) / (1 - ρ))

/-- The constant `C₂ = 2 ((3+ρ)/(1-ρ) + (7+ρ)/(1-ρ) · κ^{1/4}/2) γ` of Theorem 3. -/
noncomputable def constC2 (ρ κ γ : ℝ) : ℝ :=
  2 * ((3 + ρ) / (1 - ρ) + (7 + ρ) / (1 - ρ) * (κ ^ ((1 : ℝ) / 4) / 2)) * γ

end ColbrookAntunHansen


