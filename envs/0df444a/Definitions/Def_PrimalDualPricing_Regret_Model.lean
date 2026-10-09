-- Prove2me | Definitions.Def_PrimalDualPricing_Regret_Model
-- name    : PrimalDualPricing_Regret_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:06.177605+00:00
-- url     : https://prove2.me/theorems/c1eb3c9c-8c28-4755-bfac-878e669a2c2a
-- title:
--   Assumptions 1–2 and Remark 2, pp. 5–8 — demand functions $d_m$, revenue rates $r_m$, the fluid dual $\mathcal R_m$, $\mathcal P_m$, $g$, $z^*$, $p^*_m$
-- statement:
--   This file fixes the pricing model of Chen and Gallego and the standing assumptions of the paper.
--
--   A firm sells a single product over a selling season $[0,T]$, $T>0$, starting with $c>0$ units of inventory. There are $M$ types of consumers, $m=1,\dots,M$. When the firm charges price $p$ to type $m$, type-$m$ consumers arrive at the rate $d_m(p)$. The **choke price** $p_\infty>0$ turns off the demand of every type: $d_m(p_\infty)=0$. The price domain is $[0,p_\infty]$.
--
--   **Assumption 1** (p. 5). For every $m$:
--   1. $d_m$ is strictly decreasing on $[0,p_\infty]$, with inverse $d_m^{-1}$ on its image $[d_m(p_\infty),d_m(0)]$, and $d_m(p)\le M_1$.
--   2. With the revenue rate $r_m(\lambda)=\lambda\,d_m^{-1}(\lambda)$, the functions $r_m$, $d_m$ and $d_m^{-1}$ are Lipschitz continuous with factor $M_2$.
--   3. $r_m$ is twice differentiable and strictly concave, with $0<M_3\le -r_m''(\lambda)\le M_4$.
--
--   **The fluid dual** (p. 6). For a dual variable (unit cost of inventory) $z$,
--   $$\mathcal R_m(z)=\max_{p\in[0,p_\infty]} d_m(p)(p-z),\qquad \mathcal P_m(z)=\operatorname*{argmax}_{p\in[0,p_\infty]} d_m(p)(p-z),$$
--   and the dual function of the fluid problem is
--   $$g(z)=cz+T\sum_{m=1}^M\mathcal R_m(z).$$
--   $z^*$ is a minimizer of $g$ over $z\ge0$, and $p^*_m=\mathcal P_m(z^*)$ are the optimal fluid prices.
--
--   **Assumption 2** (p. 8) and **Remark 2** (p. 6) form the structure `Setting`. There are intervals $[\underline p,\overline p]\subseteq[0,p_\infty]$ and $[0,\overline z]$, known to the firm, with $p^*_m\in(\underline p,\overline p)$ for all $m$, $z^*\in[0,\overline z)$, and $\mathcal P_m(z)\in[\underline p,\overline p]$ for all $z\in[0,\overline z]$. As Remark 2 assumes, $g$ is twice differentiable on $[0,\overline z]$ with $M_3\le g''\le M_4$, and each $\mathcal P_m$ is Lipschitz with factor $M_2$.
--
--   Every theorem of the mission is stated for this model. The learning algorithm sees only $T$, $c$ and the intervals of Assumption 2. It never sees $d_m$, $\mathcal P_m$ or $z^*$.
--
--   **Formalization Note** Types are indexed by `Fin M`. $d_m$ is a total function on $\mathbb R$. Assumption 1 constrains it on $[0,p_\infty]$ only, and outside that domain it is an arbitrary extension with $0\le d_m\le M_1$, because the algorithm's last-phase prices can leave $[0,p_\infty]$ and every price must give a nonnegative arrival rate. The page leaves $d_m(p_\infty)=0$ implicit in "choke price … at which future demand from all types is turned off" (p. 5); here it is a field. Twice differentiability on the closed interval uses one-sided derivatives at the endpoints (`HasDerivWithinAt`). $\mathcal P_m$ and $z^*$ are fields, each with its defining optimality property. The page states they are well defined, and $\mathcal P_m(z)$ is unique by strict concavity of $\lambda\mapsto r_m(\lambda)-\lambda z$. Assumption 2 prints $z^*\in(0,\overline z)$; it is read as $z^*\in[0,\overline z)$, because §4.1 and Proposition 2 treat the case $z^*=0$ and Theorem 1 covers it. The price interval is placed in the domain, $0\le\underline p<\overline p\le p_\infty$. Remark 2 gives no domain for $g''$. Globally its bound would be unsatisfiable, since $g$ is affine once every $\mathcal P_m(z)=p_\infty$, so it is read on the dual domain $[0,\overline z]$.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, pp. 4–8, §2, Assumption 1 (p. 5), Eqs. (4)–(5), Proposition 1.4 (definition of z*), Remark 2 (p. 6), Assumption 2 (p. 8)

import Mathlib

namespace PrimalDualPricing.Regret

open Set

/-- The pricing model of Chen and Gallego (arXiv:1812.09234v3, §2, pp. 4–6) under **Assumption 1**
(p. 5): a firm sells one product over the season `[0, T]` with initial inventory `c` to `M` types of
consumers (indexed by `Fin M`, the paper's `m = 1, …, M`). A type-`m` consumer buys at the rate
`d m p` when charged the price `p`. `pinf` is the choke price `p_∞` (p. 5): the price domain of
Assumption 1 is `[0, p_∞]`, and at `p_∞` the demand of every type is turned off.

* `d m : ℝ → ℝ` is a total function; Assumption 1 constrains it on `[0, p_∞]` only. Outside that
  domain it is any extension with `0 ≤ d m p ≤ M₁` (prices are Poisson intensities, so the extension
  is nonnegative and bounded).
* Assumption 1.1: `d m` is strictly decreasing on `[0, p_∞]` with inverse `dinv m` on the image
  `[d m p_∞, d m 0]`, and `d m p ≤ M₁`.
* Assumption 1.2: with the revenue rate `r_m(λ) = λ d_m⁻¹(λ)` (`revRate`), the functions `r_m`, `d_m`
  and `d_m⁻¹` are Lipschitz with factor `M₂` (on `[d m p_∞, d m 0]`, resp. `[0, p_∞]`).
* Assumption 1.3: `r_m` is twice differentiable on `[d m p_∞, d m 0]` (one-sided derivatives at the
  endpoints, `r'`, `r''`), strictly concave, and `0 < M₃ ≤ -r''_m(λ) ≤ M₄`.
* `P m z` is the maximizer `𝒫_m(z) = argmax_{p ∈ [0, p_∞]} d_m(p)(p − z)` of (5) (the paper states it is
  well defined under Assumption 1; it is unique because `λ ↦ r_m(λ) − λ z` is strictly concave).
* `zstar` is `z* = argmin_{z ≥ 0} g(z)` of Proposition 1.4 (p. 6), with `g` the dual function `dualFn`.
-/
structure Model (M : ℕ) where
  /-- length of the selling season `T` -/
  T : ℝ
  /-- initial inventory `c` (before scaling) -/
  c : ℝ
  /-- the choke price `p_∞` -/
  pinf : ℝ
  T_pos : 0 < T
  c_pos : 0 < c
  pinf_pos : 0 < pinf
  /-- demand function `d_m` of type `m` -/
  d : Fin M → ℝ → ℝ
  /-- the constants `M₁, M₂, M₃, M₄` of Assumption 1 -/
  M₁ : ℝ
  M₂ : ℝ
  M₃ : ℝ
  M₄ : ℝ
  M₃_pos : 0 < M₃
  /-- demand rates are nonnegative (all prices, including the extension outside `[0, p_∞]`) -/
  d_nonneg : ∀ m p, 0 ≤ d m p
  /-- Assumption 1.1: `d_m(p) ≤ M₁` (imposed on all prices for the extension) -/
  d_le : ∀ m p, d m p ≤ M₁
  /-- `p_∞` is a choke price: the demand of every type is turned off there (p. 5) -/
  d_pinf : ∀ m, d m pinf = 0
  /-- Assumption 1.1: `d_m` is strictly decreasing on `[0, p_∞]` -/
  d_strictAnti : ∀ m, StrictAntiOn (d m) (Icc 0 pinf)
  /-- the inverse demand function `d_m⁻¹` -/
  dinv : Fin M → ℝ → ℝ
  dinv_d : ∀ m, ∀ p ∈ Icc 0 pinf, dinv m (d m p) = p
  d_dinv : ∀ m, ∀ l ∈ Icc (d m pinf) (d m 0), d m (dinv m l) = l
  /-- Assumption 1.2: `d_m` is Lipschitz with factor `M₂` -/
  d_lip : ∀ m, LipschitzOnWith (Real.toNNReal M₂) (d m) (Icc 0 pinf)
  /-- Assumption 1.2: `d_m⁻¹` is Lipschitz with factor `M₂` -/
  dinv_lip : ∀ m, LipschitzOnWith (Real.toNNReal M₂) (dinv m) (Icc (d m pinf) (d m 0))
  /-- Assumption 1.2: `r_m(λ) = λ d_m⁻¹(λ)` is Lipschitz with factor `M₂` -/
  rev_lip : ∀ m,
    LipschitzOnWith (Real.toNNReal M₂) (fun l => l * dinv m l) (Icc (d m pinf) (d m 0))
  /-- first derivative `r'_m` -/
  r' : Fin M → ℝ → ℝ
  /-- second derivative `r''_m` -/
  r'' : Fin M → ℝ → ℝ
  /-- Assumption 1.3: `r_m` is differentiable on `[d m p_∞, d m 0]` with derivative `r'_m` -/
  rev_hasDeriv : ∀ m, ∀ l ∈ Icc (d m pinf) (d m 0),
    HasDerivWithinAt (fun l => l * dinv m l) (r' m l) (Icc (d m pinf) (d m 0)) l
  /-- Assumption 1.3: `r'_m` is differentiable with derivative `r''_m` -/
  rev'_hasDeriv : ∀ m, ∀ l ∈ Icc (d m pinf) (d m 0),
    HasDerivWithinAt (r' m) (r'' m l) (Icc (d m pinf) (d m 0)) l
  /-- Assumption 1.3: `r_m` is strictly concave -/
  rev_strictConcave : ∀ m, StrictConcaveOn ℝ (Icc (d m pinf) (d m 0)) (fun l => l * dinv m l)
  /-- Assumption 1.3: `0 < M₃ ≤ -r''_m(λ) ≤ M₄` -/
  rev''_bounds : ∀ m, ∀ l ∈ Icc (d m pinf) (d m 0), M₃ ≤ -r'' m l ∧ -r'' m l ≤ M₄
  /-- the optimal price map `𝒫_m(z)` of (5) -/
  P : Fin M → ℝ → ℝ
  P_mem : ∀ m z, P m z ∈ Icc 0 pinf
  P_isMax : ∀ m z, ∀ p ∈ Icc 0 pinf, d m p * (p - z) ≤ d m (P m z) * (P m z - z)
  /-- the dual optimal solution `z*` (Proposition 1.4) -/
  zstar : ℝ
  zstar_nonneg : 0 ≤ zstar
  zstar_isMin : ∀ z, 0 ≤ z →
    c * zstar + T * ∑ m, sSup ((fun p => d m p * (p - zstar)) '' Icc 0 pinf)
      ≤ c * z + T * ∑ m, sSup ((fun p => d m p * (p - z)) '' Icc 0 pinf)

namespace Model

variable {M : ℕ} (μ : Model M)

/-- The revenue rate `r_m(λ) = λ d_m⁻¹(λ)` (Assumption 1.2). -/
noncomputable def revRate (m : Fin M) (l : ℝ) : ℝ := l * μ.dinv m l

/-- `ℛ_m(z) = max_{p ∈ [0, p_∞]} d_m(p)(p − z)` of (5) (p. 6). The set is nonempty and bounded above,
so the supremum is the maximum. -/
noncomputable def Rm (m : Fin M) (z : ℝ) : ℝ :=
  sSup ((fun p => μ.d m p * (p - z)) '' Icc 0 μ.pinf)

/-- The dual function `g(z) = c z + T ∑_m ℛ_m(z)` of (4) (p. 6). -/
noncomputable def dualFn (z : ℝ) : ℝ := μ.c * z + μ.T * ∑ m, μ.Rm m z

/-- The optimal fluid prices `p*_m = 𝒫_m(z*)` (Proposition 1.4, p. 6). -/
noncomputable def pstar (m : Fin M) : ℝ := μ.P m μ.zstar

end Model

/-- A model together with **Assumption 2** (p. 8) and **Remark 2** (p. 6).

* Assumption 2: intervals `[p̲, p̄]` (`pLow`, `pHigh`) and `[0, z̄]` (`zHigh`), known to the firm, with
  `p*_m ∈ (p̲, p̄)` for every `m`, `z* ∈ [0, z̄)`, and `𝒫_m(z) ∈ [p̲, p̄]` for `z ∈ [0, z̄]`. The page prints
  `z* ∈ (0, z̄)`; the half-open reading keeps the sufficient-capacity case `z* = 0`, which §4.1 and
  Proposition 2 treat and Theorem 1 covers. The price interval lies in the domain: `0 ≤ p̲ < p̄ ≤ p_∞`.
* Remark 2 (assumed by the paper): `g` is twice differentiable on `[0, z̄]` with `M₃ ≤ g'' ≤ M₄`
  (derivatives within `[0, z̄]`), and every `𝒫_m` is Lipschitz with factor `M₂`. The page gives no
  domain for `g''`; globally it would be unsatisfiable (`g` is affine once every `𝒫_m(z) = p_∞`), so it
  is read on the dual domain `[0, z̄]`. -/
structure Setting (M : ℕ) extends Model M where
  /-- `p̲` -/
  pLow : ℝ
  /-- `p̄` -/
  pHigh : ℝ
  /-- `z̄` -/
  zHigh : ℝ
  pLow_nonneg : 0 ≤ pLow
  pLow_lt_pHigh : pLow < pHigh
  pHigh_le_pinf : pHigh ≤ pinf
  pstar_mem : ∀ m, P m zstar ∈ Ioo pLow pHigh
  zstar_mem : zstar ∈ Ico 0 zHigh
  P_mem_of_dual : ∀ m, ∀ z ∈ Icc 0 zHigh, P m z ∈ Icc pLow pHigh
  /-- Remark 2: first derivative of `g` on `[0, z̄]` -/
  g' : ℝ → ℝ
  /-- Remark 2: second derivative of `g` on `[0, z̄]` -/
  g'' : ℝ → ℝ
  g_hasDeriv : ∀ z ∈ Icc 0 zHigh,
    HasDerivWithinAt toModel.dualFn (g' z) (Icc 0 zHigh) z
  g'_hasDeriv : ∀ z ∈ Icc 0 zHigh, HasDerivWithinAt g' (g'' z) (Icc 0 zHigh) z
  g''_bounds : ∀ z ∈ Icc 0 zHigh, M₃ ≤ g'' z ∧ g'' z ≤ M₄
  P_lip : ∀ m, LipschitzWith (Real.toNNReal M₂) (P m)

end PrimalDualPricing.Regret


