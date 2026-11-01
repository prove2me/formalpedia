-- Prove2me | Definitions.Def_OnlineWass_Model
-- name    : OnlineWass_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:01.230258+00:00
-- url     : https://prove2.me/theorems/33989cd3-fd87-45e3-a635-a04f0df53436
-- title:
--   The parameterized convex program, the metric $\rho$ and Assumption 1
-- statement:
--   The model has a compact convex decision set $\mathcal X\subset\mathbb R^k$, an objective $f(x;\theta)$ and constraint functions $g(x;\theta)=(g_1(x;\theta),\dots,g_m(x;\theta))$, indexed by a parameter $\theta\in\Theta$. Over $T$ periods the offline problem is
--
--   $$
--   \max\ \sum_{t=1}^T f(x_t;\theta_t)\quad\text{s.t.}\quad\sum_{t=1}^T g_i(x_t;\theta_t)\le c_i,\ i=1,\dots,m,\qquad x_t\in\mathcal X.
--   $$
--
--   The distance on the parameter space, display (2), is
--
--   $$
--   \rho(\theta,\theta')=\sup_{x\in\mathcal X}\bigl\|(f(x;\theta),g(x;\theta))-(f(x;\theta'),g(x;\theta'))\bigr\|_\infty ,
--   $$
--
--   with $\|\cdot\|_\infty$ the supremum norm on $\mathbb R^{m+1}$. Parameters at distance zero are identified, so $\Theta$ is a metric space, and it carries its Borel $\sigma$-algebra.
--
--   Assumption 1 asks that (a) $|f(x;\theta)|\le1$; (b) $g_i(x;\theta)\in[0,1]$, $0\in\mathcal X$ and $g_i(0;\theta)=0$; (c) there is $q>0$ with $f(x;\theta)\le q\,g_i(x;\theta)$ whenever $g_i(x;\theta)>0$; (d) the $\theta_t\sim\mathcal P_t$ are independent; (e) $f(\cdot;\theta)$ is concave and $g_i(\cdot;\theta)$ convex. Also $f(\cdot;\theta)$, $g_i(\cdot;\theta)$ are continuous on $\mathcal X$.
--
--   Every object of the mission is built on this model.
--
--   **Formalization Note** `Assumption1ab` is the part without convexity, used by Lemma 3 and the measurability statements. Part (d) is the product law `Measure.pi` in each statement. The functions are typed on all of $\mathbb R^k$, but every hypothesis and every action is on $\mathcal X$. Separability of $\Theta$ and measurability of $f,g$ in $\theta$ are not assumed: they follow from (2).
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, §2.1, p.8, display (2); Assumption 1, p.9; (PCP), p.8; continuity and compactness p.7

import Mathlib

namespace OnlineWass

/-- **The parameterized convex program (PCP).** Jiang, Li & Zhang, *Online Stochastic Optimization
with Wasserstein Based Non-stationarity*, arXiv:2012.06961v3, §2, pp.7–8: a decision set `X ⊂ ℝᵏ`,
an objective `f(x; θ)` and `m` constraint functions `g(x; θ) = (g₁(x; θ), …, g_m(x; θ))`, indexed by
a parameter `θ ∈ Θ`.

**Formalization Note.** `f` and `g` are typed on all of `ℝᵏ` but have no meaning off `X`: every
hypothesis of this mission is stated on `X`, and every action of the mission lies in `X`. `Θ ⊂ ℝˡ`
is not used; `ρ` of (2) is the only structure the paper puts on `Θ` (see `DistEqRho`). -/
structure Model (k m : ℕ) (Θ : Type*) where
  /-- The decision set `𝒳`. -/
  X : Set (Fin k → ℝ)
  /-- The objective `f(x; θ)`. -/
  f : (Fin k → ℝ) → Θ → ℝ
  /-- The constraint functions `gᵢ(x; θ)`. -/
  g : (Fin k → ℝ) → Θ → Fin m → ℝ

variable {k m : ℕ} {Θ : Type*}

/-- The Lagrangian `f(x; θ) − pᵀg(x; θ)` maximized in line 4 of Algorithm 1 (p.17) and in the
definition of `h` (p.14). -/
noncomputable def Model.lagrangian (M : Model k m Θ) (p : Fin m → ℝ) (x : Fin k → ℝ) (θ : Θ) : ℝ :=
  M.f x θ - ∑ i, p i * M.g x θ i

/-- **Display (2), p.8: the distance of `Θ` is `ρ`.**
`ρ(θ, θ') = sup_{x∈𝒳} ‖(f(x; θ), g(x; θ)) − (f(x; θ'), g(x; θ'))‖∞`, "where ‖·‖∞ is the supremum
norm in R^{m+1}". The paper's "let Θ be a set of class representatives, that is, for any θ ≠ θ' ∈ Θ,
ρ(θ, θ') > 0" is `MetricSpace Θ`, and `𝓑_Θ` of p.9 is `BorelSpace Θ`.

**Formalization Note.** The norm on `ℝ × (Fin m → ℝ)` is the sup norm, so the norm in the set is
`max(|Δf|, maxᵢ|Δgᵢ|)`. The set is nonempty (`0 ∈ 𝒳`) and bounded by 2 under `Assumption1ab`, so the
real `sSup` is the true supremum. Neither separability of `Θ` nor measurability of `f`, `g` in `θ` is
assumed anywhere: `θ ↦ (f(·; θ), g(·; θ))` is an isometry of `Θ` into `C(𝒳, ℝ^{m+1})`, so `Θ` is
separable, and `f`, `g` are 1-Lipschitz in `θ`, both by this hypothesis. -/
def DistEqRho [PseudoMetricSpace Θ] (M : Model k m Θ) : Prop :=
  ∀ θ θ' : Θ, dist θ θ' =
    sSup ((fun x => ‖((M.f x θ, M.g x θ) : ℝ × (Fin m → ℝ)) - (M.f x θ', M.g x θ')‖) '' M.X)

/-- **The model of p.7 with Assumption 1 (a), (b), p.9.** `𝒳` is compact and `f(·; θ)`, `gᵢ(·; θ)`
are continuous on it (p.7); `|f(x; θ)| ≤ 1`; `gᵢ(x; θ) ∈ [0, 1]`; `0 ∈ 𝒳` and `gᵢ(0; θ) = 0`.

**Formalization Note.** Split from `Assumption1` because Lemma 3 and the measurability statements
need no convexity (the remark on p.54). -/
structure Assumption1ab (M : Model k m Θ) : Prop where
  isCompact_X : IsCompact M.X
  continuousOn_f : ∀ θ, ContinuousOn (fun x => M.f x θ) M.X
  continuousOn_g : ∀ θ i, ContinuousOn (fun x => M.g x θ i) M.X
  /-- Assumption 1 (a). -/
  abs_f_le : ∀ x ∈ M.X, ∀ θ, |M.f x θ| ≤ 1
  /-- Assumption 1 (b). -/
  g_nonneg : ∀ x ∈ M.X, ∀ θ i, 0 ≤ M.g x θ i
  /-- Assumption 1 (b). -/
  g_le_one : ∀ x ∈ M.X, ∀ θ i, M.g x θ i ≤ 1
  /-- Assumption 1 (b), "In particular". -/
  zero_mem : (0 : Fin k → ℝ) ∈ M.X
  /-- Assumption 1 (b), "In particular". -/
  g_zero : ∀ θ i, M.g 0 θ i = 0

/-- **Assumption 1 (Boundedness and Independence), p.9**, parts (a), (b), (c), (e), with the convexity
of `𝒳` of p.7. Part (c) is `f(x; θ) ≤ q · gᵢ(x; θ)` whenever `gᵢ(x; θ) > 0`, for a positive constant
`q`, and (e) is concavity of `f(·; θ)` and convexity of `gᵢ(·; θ)`.

**Formalization Note.** Part (d), "θₜ ∼ 𝒫ₜ and 𝒫ₜ's are independent", is the product law
`Measure.pi` in each statement. The correction `f(0; θ) ≥ 0` is deliberately not a field here: it
appears as a separate visible hypothesis of exactly the statements that need it. -/
structure Assumption1 (M : Model k m Θ) (q : ℝ) : Prop extends Assumption1ab M where
  convex_X : Convex ℝ M.X
  q_pos : 0 < q
  /-- Assumption 1 (c). -/
  f_le_q_mul_g : ∀ x ∈ M.X, ∀ θ i, 0 < M.g x θ i → M.f x θ ≤ q * M.g x θ i
  /-- Assumption 1 (e). -/
  concaveOn_f : ∀ θ, ConcaveOn ℝ M.X (fun x => M.f x θ)
  /-- Assumption 1 (e). -/
  convexOn_g : ∀ θ i, ConvexOn ℝ M.X (fun x => M.g x θ i)

end OnlineWass


