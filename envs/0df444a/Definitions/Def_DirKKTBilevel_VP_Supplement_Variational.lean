-- Prove2me | Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
-- name    : DirKKTBilevel_VP_Supplement_Variational
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:19:58.67718+00:00
-- url     : https://prove2.me/theorems/93838486-1e4c-4ba3-bc25-9b137729c951
-- title:
--   Definitions 2.3, 2.7, 2.8, 3.2, pp. 6–9 — directional set limits, directional Clarke subdifferential, directional MSCQ, directional quasi-normality
-- statement:
--   Throughout, $X$ is a finite-dimensional real inner product space (in the paper $X=\mathbb R^n$), $V_{\varepsilon,\delta}(u)$ is the directional neighbourhood of the published base model, and "$t_k\downarrow0$" means $t_k>0$, $t_k\to0$.
--
--   1. **Directional set limits** (Definition 2.3). For $\Phi:X\rightrightarrows Y$ and a direction $u$,
--   $$\liminf_{x\xrightarrow{u}\bar x}\Phi(x)=\{y\mid \forall t_k\downarrow0,\ u_k\to u\ \exists y_k\to y,\ y_k\in\Phi(\bar x+t_ku_k)\text{ for all large }k\},$$
--   $$\limsup_{x\xrightarrow{u}\bar x}\Phi(x)=\{y\mid \exists t_k\downarrow0,\ u_k\to u,\ y_k\to y,\ y_k\in\Phi(\bar x+t_ku_k)\}.$$
--   2. **Directional Clarke subdifferential** (Definition 2.7): $\partial^c\varphi(\bar x;u)=\operatorname{co}\partial\varphi(\bar x;u)$, the convex hull of the directional limiting subdifferential of the base model; for $u=0$ it is the Clarke subdifferential $\partial^c\varphi(\bar x)$.
--   3. **Directional MSCQ** (Definition 2.8). The system $h(z)\le0$, $h:X\to\mathbb R^q$, with $h(\bar x)\le0$, satisfies MSCQ at $\bar x$ in direction $u$ if for some $\kappa,\varepsilon,\delta>0$
--   $$\operatorname{dist}(z,h^{-1}(\mathbb R^q_-))\le\kappa\|h_+(z)\|\qquad\forall z\in\bar x+V_{\varepsilon,\delta}(u).$$
--   4. **Directional quasi-normality** (Definition 3.2). With $d=h'(\bar z;u)$: there is no $\zeta\ne0$ with $0\le\zeta\perp h(\bar z)$, $\zeta\perp d$, $0\in\partial\langle\zeta,h\rangle(\bar z;u)$, and sequences $t_k\downarrow0$, $u_k\to u$ with $h_j(\bar z+t_ku_k)>0$ for every active $j$ with $\zeta_j>0$.
--
--   These objects state Proposition 2.1, Lemma 3.1 and Proposition 3.1.
--
--   **Formalization Note** The inner limit requires $y_k\in\Phi(\bar x+t_ku_k)$ for all sufficiently large $k$ (the Painlevé–Kuratowski convention the paper says it recovers at $u=0$). The distance is the extended distance `Metric.infEDist`. The directional Clarke subdifferential is defined for an extended-real function; real functions enter through the coercion.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, pp. 6–9, Definitions 2.3, 2.7, 2.8, 3.2

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

namespace DirKKTBilevel.VP.Supplement

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Definition 2.3, p. 6: the inner (lower) limit of a set-valued map `Φ` as `x → x̄` in
direction `u`: `y` such that for every `t_k ↓ 0`, `u_k → u` there are `y_k → y` with
`y_k ∈ Φ(x̄ + t_k u_k)` (for all large `k`, the Painlevé–Kuratowski convention). -/
def dirLiminf {Y : Type*} [TopologicalSpace Y] (Φ : X → Set Y) (x u : X) : Set Y :=
  {y | ∀ (t : ℕ → ℝ) (us : ℕ → X), (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) →
    Tendsto us atTop (𝓝 u) →
    ∃ ys : ℕ → Y, Tendsto ys atTop (𝓝 y) ∧ ∀ᶠ k in atTop, ys k ∈ Φ (x + t k • us k)}

/-- Definition 2.3, p. 6: the outer (upper) limit of `Φ` as `x → x̄` in direction `u`: `y` such
that there are `t_k ↓ 0`, `u_k → u`, `y_k → y` with `y_k ∈ Φ(x̄ + t_k u_k)`. -/
def dirLimsup {Y : Type*} [TopologicalSpace Y] (Φ : X → Set Y) (x u : X) : Set Y :=
  {y | ∃ (t : ℕ → ℝ) (us : ℕ → X) (ys : ℕ → Y), (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
    Tendsto us atTop (𝓝 u) ∧ Tendsto ys atTop (𝓝 y) ∧ ∀ k, ys k ∈ Φ (x + t k • us k)}

/-- Definition 2.7, p. 6: the directional Clarke subdifferential
`∂ᶜφ(x̄; u) = co ∂φ(x̄; u)`, the convex hull of the directional limiting subdifferential.
With `u = 0` it is the Clarke subdifferential `∂ᶜφ(x̄)` (p. 7). -/
def dirClarke (φ : X → EReal) (x u : X) : Set X :=
  convexHull ℝ (dirSubdiff φ x u)

/-- Definition 2.8, p. 7: the system `h(z) ≤ 0` satisfies the directional metric subregularity
constraint qualification (MSCQ) at the solution `x̄` in direction `u`: there are `κ, ε, δ > 0` with
`dist(z, h⁻¹(ℝ^q_−)) ≤ κ‖h₊(z)‖` for all `z ∈ x̄ + V_{ε,δ}(u)`. The distance is the extended
distance `infEDist`. -/
def DirMSCQ {q : ℕ} (h : X → E q) (x u : X) : Prop :=
  (∀ j, h x j ≤ 0) ∧ ∃ κ ε δ : ℝ, 0 < κ ∧ 0 < ε ∧ 0 < δ ∧
    ∀ z, z - x ∈ dirNbhd ε δ u →
      Metric.infEDist z {w | ∀ j, h w j ≤ 0} ≤ ENNReal.ofReal (κ * ‖posPart (h z)‖)

/-- Definition 3.2 (third item), p. 9: directional quasi-normality of `h(z) ≤ 0` at `z̄` in
direction `u`, where `d = h'(z̄; u)`: there is no `ζ ≠ 0` with `0 ≤ ζ ⊥ h(z̄)`, `ζ ⊥ d`,
`0 ∈ ∂⟨ζ, h⟩(z̄; u)` (4) and sequences `t_k ↓ 0`, `u_k → u` with `h_j(z̄ + t_k u_k) > 0` whenever
`j` is active and `ζ_j > 0` (5). -/
def DirQuasiNormal {q : ℕ} (h : X → E q) (x u : X) (d : E q) : Prop :=
  ¬ ∃ ζ : E q, ζ ≠ 0 ∧ (∀ j, 0 ≤ ζ j) ∧ ∑ j, ζ j * h x j = 0 ∧ ∑ j, ζ j * d j = 0 ∧
    (0 : X) ∈ dirSubdiff (fun z => ((∑ j, ζ j * h z j : ℝ) : EReal)) x u ∧
    ∃ (t : ℕ → ℝ) (us : ℕ → X), (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
      Tendsto us atTop (𝓝 u) ∧
      ∀ k, ∀ j, h x j = 0 → 0 < ζ j → 0 < h (x + t k • us k) j

end

end DirKKTBilevel.VP.Supplement


