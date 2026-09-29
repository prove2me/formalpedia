-- Prove2me | Definitions.Def_DistInterpRO_Shrinkage_Model
-- name    : DistInterpRO_Shrinkage_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:51:19.357807+00:00
-- url     : https://prove2.me/theorems/dd631478-4a13-4ed6-ac04-ad1394e52a27
-- title:
--   Two-scenario distribution set, its DRSP value, the radius D, and the bounded-Hessian condition
-- statement:
--   Throughout, $\mathbb{R}^m$ carries the Euclidean norm $\|\cdot\|_2$ and its Borel $\sigma$-algebra, and $\mathcal P$ denotes the set of Borel probability measures on $\mathbb{R}^m$. Fix a nominal parameter $x_0\in\mathbb{R}^m$ and a deviation set $\Delta\subseteq\mathbb{R}^m$, and write $x_0+\Delta=\{x_0+x : x\in\Delta\}$.
--
--   1. **Two-scenario set.** For a number $p$, the set
--   $$\mathcal S(x_0,\Delta,p)=\{\mu\in\mathcal P \mid \mu(\{x_0\})\ge p,\ \mu(x_0+\Delta)=1\}.$$
--   The paper's set of §4.2 is $\hat{\mathcal P}'=\mathcal S(x_0,\Delta,1-\alpha)$; the set of Corollary 4.3 is $\hat{\mathcal P}''=\mathcal S(x_0,\Delta,\max(0,1-\alpha-\alpha D^2h))$.
--   2. **DRSP value.** For $F:\mathbb{R}^m\to\mathbb{R}$,
--   $$V(F;x_0,\Delta,p)=\inf_{\mu\in\mathcal S(x_0,\Delta,p)}\int_{\mathbb{R}^m}F(x)\,d\mu(x).$$
--   3. **Radius.** $D(\Delta)=\sup\{\|x\|_2 : x\in\Delta\}$, which equals the paper's $D=\max_{x\in\Delta}\|x\|_2$ when $\Delta$ is compact and nonempty.
--   4. **Bounded Hessian.** $F$ has Hessian bounded by $h$ if $F$ and its derivative $DF$ are differentiable everywhere and $|D^2F(x)[y,y]|\le h\|y\|_2^2$ for all $x,y$; that is, $-hI\preceq H(x)\preceq hI$ for the Hessian $H(x)$ of $F$ at $x$.
--
--   These objects are the vocabulary of §4.2: shrinking an uncertainty set $\Delta$ to $\alpha\Delta$ is compared with a distributionally robust problem in which the parameter equals $x_0$ with probability at least $1-\alpha$ and otherwise deviates within $\Delta$.
--
--   **Formalization Note** $\mathbb{R}^m$ is `EuclideanSpace ℝ (Fin m)`. Measures are `Measure`s with `IsProbabilityMeasure` inside the set, and the lower bound on $\mu(\{x_0\})$ uses `ENNReal.ofReal p` (so a negative $p$ imposes nothing). The infimum is a real infimum over the subtype of the set with Bochner integrals: it is $0$ if the set is empty or the integrals unbounded below, so every theorem using it assumes $0\in\Delta$ (which puts the Dirac mass at $x_0$ in the set) and $\Delta$ compact with $F$ continuous (which makes $F$ bounded on $x_0+\Delta$, which carries every member). $D$ is `sSup` of the image of the norm, which is $0$ on an empty or unbounded set; the theorems assume $\Delta$ compact and nonempty.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 104, §4.2 (definition of 𝒫̂′) and Theorem 4.1 (D, Hessian bound); p. 105, Corollary 4.3 (𝒫̂″)

import Mathlib

open MeasureTheory

namespace DistInterpRO.Shrinkage

/-- The two-scenario distribution set of §4.2 (Xu–Caramanis–Mannor 2012, p. 104), with the
nominal mass `p` as a parameter:
`{μ ∈ 𝒫 | μ({x₀}) ≥ p, μ(x₀ + Δ) = 1}`, where `𝒫` is the set of Borel probability measures
on `ℝᵐ = EuclideanSpace ℝ (Fin m)` and `x₀ + Δ = {x₀ + x | x ∈ Δ}`.
The paper's `𝒫̂′` (Theorem 4.1) is `scenarioSet x₀ Δ (1 - α)`, and its `𝒫̂″` (Corollary 4.3)
is `scenarioSet x₀ Δ (max 0 (1 - α - α * D ^ 2 * h))`. -/
def scenarioSet {m : ℕ} (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m)))
    (p : ℝ) : Set (Measure (EuclideanSpace ℝ (Fin m))) :=
  {μ | IsProbabilityMeasure μ ∧ ENNReal.ofReal p ≤ μ {x₀} ∧
    μ ((fun x => x₀ + x) '' Δ) = 1}

/-- The value of the distributionally robust problem over `scenarioSet x₀ Δ p`:
`inf_{μ ∈ scenarioSet x₀ Δ p} ∫ F dμ`, an infimum in `ℝ` over the subtype of the set
(Bochner integrals). It is a genuine infimum when the set is nonempty and `F` is continuous
and `Δ` is compact (then `F` is bounded on `x₀ + Δ`, which carries every member). -/
noncomputable def drspValue {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (p : ℝ) : ℝ :=
  ⨅ μ : scenarioSet x₀ Δ p, ∫ x, F x ∂(μ : Measure (EuclideanSpace ℝ (Fin m)))

/-- The radius `D = max_{x ∈ Δ} ‖x‖₂` of the deviation set (Theorem 4.1, p. 104), written as
`sSup {‖x‖ | x ∈ Δ}`; for compact nonempty `Δ` the supremum is attained. -/
noncomputable def devRadius {m : ℕ} (Δ : Set (EuclideanSpace ℝ (Fin m))) : ℝ :=
  sSup ((fun x => ‖x‖) '' Δ)

/-- "`F` is twice differentiable with Hessian bounded by `h`" (Theorem 4.1, p. 104):
`F` and its derivative `DF` are (Fréchet) differentiable everywhere, and the Hessian quadratic
form satisfies `|D²F(x)[y, y]| ≤ h ‖y‖²` for all `x, y`, i.e. `−hI ⪯ H(x) ⪯ hI`. -/
def HasBoundedHessian {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ) (h : ℝ) : Prop :=
  Differentiable ℝ F ∧ Differentiable ℝ (fderiv ℝ F) ∧
    ∀ x y : EuclideanSpace ℝ (Fin m), |fderiv ℝ (fderiv ℝ F) x y y| ≤ h * ‖y‖ ^ 2

end DistInterpRO.Shrinkage


