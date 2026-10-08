-- Prove2me | Definitions.Def_BesbesZeevi_SingleParam_Family
-- name    : BesbesZeevi_SingleParam_Family
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:00:17.835511+00:00
-- url     : https://prove2.me/theorems/9ebe5c22-8883-4875-8c78-f6652299b6b0
-- title:
--   One-parameter demand family with Assumptions 2 and 3, and measurable selections $p^u,p^c$
-- statement:
--   Fix a market. A **one-parameter demand family** is a function $\lambda(p;\theta)$ of the price $p$ and a scalar parameter $\theta\in\Theta=[\theta_{\mathrm{lo}},\theta_{\mathrm{hi}}]$ (a nonempty compact interval) together with constants $M,\underline K,\overline K,m>0$ ($\underline K\le\overline K$), $l_0,\alpha,\overline K_2>0$, a test price $p_1$ and a map $g$, such that
--
--   1. every $\lambda(\cdot;\theta)$, $\theta\in\Theta$, belongs to $\mathcal L(M,\underline K,\overline K,m)$;
--   2. (Assumption 2(i)) $p_1\in[\underline p,\overline p]$ and $\theta\mapsto\sqrt{\lambda(p_1;\theta)}$ is differentiable on $\Theta$;
--   3. (Assumption 2(ii)) $|\lambda(p;\theta)-\lambda(p;\theta')|\le\overline K_2|\theta-\theta'|$ for $p\in[\underline p,\overline p]$ and $\theta,\theta'\in\Theta$;
--   4. (Assumption 3) $\inf_{p\in[\underline p,\overline p]}\inf_{\theta\in\Theta}\lambda(p;\theta)>l_0$, and for each $p\in[\underline p,\overline p]$ the solution map $g(p,\cdot)$ of $\lambda(p;\cdot)=d$ satisfies: $g(p,d)\in\Theta$ for $d\ge0$, $g(p,\lambda(p;\theta))=\theta$ for $\theta\in\Theta$, and $|g(p,d)-g(p,d')|\le\alpha|d-d'|$ for $d,d'\ge0$; moreover $g$ is jointly measurable.
--
--   A **selection** is a pair of measurable maps $p^u,p^c$ such that, for every $\theta\in\Theta$, $p^u(\theta)\in[\underline p,\overline p]$ maximizes $p\lambda(p;\theta)$ over $[\underline p,\overline p]$ and $p^c(\theta)\in[\underline p,\overline p]$ minimizes $|\lambda(p;\theta)-x/T|$ over $[\underline p,\overline p]$. Write $p^D(\theta)=\max\{p^u(\theta),p^c(\theta)\}$.
--
--   These are the standing assumptions of Proposition 5, the single-unknown-parameter result of the paper.
--
--   **Formalization Note** Assumption 3 asks that $\lambda(p;\cdot)=d$ have a unique solution for *every* $d\ge0$; no $\theta\in\Theta$ solves it when $d$ exceeds $\sup_\theta\lambda(p;\theta)$. It is read as: $g(p,\cdot)$ maps $[0,\infty)$ into $\Theta$, inverts $\lambda(p;\cdot)$ on $\Theta$ (so the solution in $\Theta$ is unique when it exists) and is $\alpha$-Lipschitz. Joint measurability of $g$ is added so that the estimate $\hat\theta=g(\hat p,\hat d)$ at a random price is a random variable. Assumption 2(i)a and (i)b with $k=1$ are implied by Assumption 3. The selections are any measurable choice of maximizer and minimizer; the statements hold for each of them.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 13 (PDF p. 15), §5; p. 15 (PDF p. 17), Assumption 2; p. 17 (PDF p. 19), Algorithm 3 Step 2(b) and Assumption 3; p. 31 (PDF p. 33), definition of p^D(θ)

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_Model

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- A one-parameter family of demand functions `λ(p; θ)`, `θ ∈ Θ = [θLo, θHi] ⊂ ℝ`, satisfying
the standing assumptions of Proposition 5 of Besbes–Zeevi (2009): `L(Θ) ⊂ 𝓛(M, K̲, K̄, m)`
(§5, p. 13), Assumption 2 with `k = 1` (p. 15) and Assumption 3 (p. 17).

* `Θ` convex and compact in `ℝ` is a nonempty closed interval `[θLo, θHi]`;
* every `λ(·; θ)`, `θ ∈ Θ`, is in the class `𝓛(M, K̲, K̄, m)` with the same constants;
* Assumption 2(i): a test price `p₁ ∈ [p̲, p̄]` with `√λ(p₁; ·)` differentiable on `Θ`
  (2(i)a, `inf_θ λ(p₁; θ) > l₀`, is implied by Assumption 3 below);
* Assumption 2(ii): `|λ(p; θ) - λ(p; θ')| ≤ K̄₂ |θ - θ'|` on `[p̲, p̄] × Θ`;
* Assumption 3: `inf_{p ∈ [p̲, p̄]} inf_{θ ∈ Θ} λ(p; θ) > l₀ > 0`, and for every `p ∈ [p̲, p̄]`
  the solution map `d ↦ g(p, d)` of `λ(p; ·) = d` is `α`-Lipschitz on `d ≥ 0`.

Reading of Assumption 3 (recorded deviation): an exact solution in `Θ` cannot exist for
`d > sup_θ λ(p; θ)`, so `g(p, ·)` is taken to be a map `[0, ∞) → Θ` that inverts `λ(p; ·)` on
`Θ` (`g(p, λ(p; θ)) = θ`, hence the solution in `Θ` is unique whenever it exists) and is
`α`-Lipschitz. `g` is also assumed jointly measurable, so that the estimates
`θ̂ = g(p̂, d̂)` at random prices are random variables. -/
structure Family (D : Market) where
  M : ℝ
  KLo : ℝ
  KHi : ℝ
  m : ℝ
  M_pos : 0 < M
  KLo_pos : 0 < KLo
  KLo_le_KHi : KLo ≤ KHi
  m_pos : 0 < m
  θLo : ℝ
  θHi : ℝ
  θLo_le_θHi : θLo ≤ θHi
  /-- The family: `lam p θ` is the demand rate `λ(p; θ)` at price `p` under parameter `θ`. -/
  lam : ℝ → ℝ → ℝ
  inClass : ∀ θ ∈ Set.Icc θLo θHi, InClass D M KLo KHi m (fun p => lam p θ)
  /-- The test price `p₁` of Assumption 2(i). -/
  p1 : ℝ
  p1_mem : p1 ∈ Set.Icc D.pLo D.pHi
  sqrt_differentiableOn : DifferentiableOn ℝ (fun θ => Real.sqrt (lam p1 θ)) (Set.Icc θLo θHi)
  K2 : ℝ
  K2_pos : 0 < K2
  lipschitz_param : ∀ p ∈ Set.Icc D.pLo D.pHi, ∀ θ ∈ Set.Icc θLo θHi,
    ∀ θ' ∈ Set.Icc θLo θHi, |lam p θ - lam p θ'| ≤ K2 * |θ - θ'|
  l0 : ℝ
  l0_pos : 0 < l0
  inf_gt : l0 < sInf ((fun q : ℝ × ℝ => lam q.1 q.2) ''
    (Set.Icc D.pLo D.pHi ×ˢ Set.Icc θLo θHi))
  /-- The solution map `g(p, d)` of `λ(p; ·) = d` (Assumption 3). -/
  g : ℝ → ℝ → ℝ
  g_mem : ∀ p ∈ Set.Icc D.pLo D.pHi, ∀ d : ℝ, 0 ≤ d → g p d ∈ Set.Icc θLo θHi
  g_inv : ∀ p ∈ Set.Icc D.pLo D.pHi, ∀ θ ∈ Set.Icc θLo θHi, g p (lam p θ) = θ
  α : ℝ
  α_pos : 0 < α
  g_lipschitz : ∀ p ∈ Set.Icc D.pLo D.pHi, ∀ d d' : ℝ, 0 ≤ d → 0 ≤ d' →
    |g p d - g p d'| ≤ α * |d - d'|
  g_measurable : Measurable (Function.uncurry g)

/-- The parameter set `Θ = [θLo, θHi]`. -/
def Family.Θ {D : Market} (F : Family D) : Set ℝ := Set.Icc F.θLo F.θHi

/-- A measurable selection of the maximizer `p^u(θ)` of the revenue rate `p λ(p; θ)` and of
the minimizer `p^c(θ)` of `|λ(p; θ) - x/T|` over `[p̲, p̄]`, for every `θ ∈ Θ`
(Algorithm 3, Step 2(b), p. 17; §A.2, p. 31). Any such selection may be used. -/
structure Selection (D : Market) (F : Family D) where
  pu : ℝ → ℝ
  pc : ℝ → ℝ
  pu_measurable : Measurable pu
  pc_measurable : Measurable pc
  pu_mem : ∀ θ ∈ F.Θ, pu θ ∈ Set.Icc D.pLo D.pHi
  pc_mem : ∀ θ ∈ F.Θ, pc θ ∈ Set.Icc D.pLo D.pHi
  pu_max : ∀ θ ∈ F.Θ, IsMaxOn (fun p => p * F.lam p θ) (Set.Icc D.pLo D.pHi) (pu θ)
  pc_min : ∀ θ ∈ F.Θ, IsMinOn (fun p => |F.lam p θ - D.x / D.T|) (Set.Icc D.pLo D.pHi) (pc θ)

/-- `p^D(θ) = max {p^u(θ), p^c(θ)}` (§A.2, p. 31). -/
noncomputable def Selection.pD {D : Market} {F : Family D} (σ : Selection D F) (θ : ℝ) : ℝ :=
  max (σ.pu θ) (σ.pc θ)

end BesbesZeevi.SingleParam


