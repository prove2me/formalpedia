-- Prove2me | Definitions.Def_SGHMCOpt_Euler_Transport
-- name    : SGHMCOpt_Euler_Transport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:12.161992+00:00
-- url     : https://prove2.me/theorems/07362dca-665d-4ad8-b48a-2bb045755648
-- title:
--   pp. 9, 39 — the 2-Wasserstein distance on ℝ^{2d}, the semi-metric ℋ_ρ (A.12) and the class of functions h of Eberle–Guillin–Zimmer
-- statement:
--   Distances between probability laws on the phase space $\mathbb R^{2d}=\mathbb R^d\times\mathbb R^d$, built on the optimal-transport cost $D_c(\mu,\nu)=\inf_{\pi}\int c\,d\pi$, the infimum over couplings $\pi$ of $\mu$ and $\nu$.
--
--   1. The **2-Wasserstein distance** on a normed space: $\mathcal W_2(\mu,\nu)=\big(\inf_\pi\int\|w-w'\|^2\pi(dw,dw')\big)^{1/2}$. The phase space with its Euclidean norm $\|(x,v)\|^2=\|x\|^2+\|v\|^2$ is `Phase d`.
--   2. For $(x,v),(x',v')\in\mathbb R^{2d}$ (p. 39),
--   $$r((x,v),(x',v'))=\alpha_1\|x-x'\|+\|x-x'+\gamma^{-1}(v-v')\|,\qquad \rho((x,v),(x',v'))=h(r)\,(1+\varepsilon_1\mathcal V(x,v)+\varepsilon_1\mathcal V(x',v')),$$
--   with $\alpha_1$ of (A.15), $\varepsilon_1$ of (A.16) and the Lyapunov function $\mathcal V$ of the dataset $z$.
--   3. The semi-metric (A.12): $\mathcal H_\rho(\mu,\nu)=\inf_{(X,V)\sim\mu,(X',V')\sim\nu}\mathbb E[\rho((X,V),(X',V'))]$, valued in $[0,\infty]$.
--   4. The admissible $h$ (p. 39): $h:[0,\infty)\to[0,\infty)$ continuous, non-decreasing, concave, $h(0)=0$, $C^2$ on $(0,R_1)$ for some $R_1>0$, with right derivative $h'_+(0)=1$, left derivative $h'_-(R_1)>0$, and constant on $[R_1,\infty)$.
--
--   $\mathcal H_\rho$ is the quantity in which Eberle, Guillin and Zimmer measure contraction of underdamped Langevin dynamics; the paper bounds it at the initial law (Lemma 20), and $\mathcal W_2$ converts it into a bound on expectations (Lemma 26).
--
--   **Formalization Note** Both infima use the published definition `RWPI.SqrtLasso.transportCost`: the infimum over probability measures on the product with the two prescribed marginals of the lower Lebesgue integral of a $[0,\infty]$-valued cost. $\mathcal W_2$ is the real square root of `.toReal` of that cost, which is the paper's value whenever both laws have finite second moments (then a finite-cost coupling exists). $\mathcal H_\rho$ stays in $[0,\infty]$. $h$ is a function on $\mathbb R$ whose properties are required on $[0,\infty)$; one-sided derivatives are derivatives within $[0,\infty)$ at $0$ and within $(-\infty,R_1]$ at $R_1$.
-- source:
--   arXiv:1809.04618v4, §2 (2-Wasserstein distance and couplings), pp. 8–9; r, ρ and the class of h, p. 39; (A.12), p. 39

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_SGHMCOpt_Euler_Model

open MeasureTheory

namespace SGHMCOpt.Euler

/-- The phase space `ℝ^{2d} = ℝ^d × ℝ^d` with its Euclidean norm `‖(x, v)‖² = ‖x‖² + ‖v‖²`. -/
abbrev Phase (d : ℕ) := WithLp 2 (E d × E d)

/-- The 2-Wasserstein distance `𝒲₂(μ, ν) = (inf_{couplings} E‖W − W′‖²)^{1/2}`, through the
published optimal-transport cost `RWPI.SqrtLasso.transportCost` with cost `‖w − w′‖²`. -/
noncomputable def W2 {X : Type*} [NormedAddCommGroup X] [MeasurableSpace X] (μ ν : Measure X) : ℝ :=
  Real.sqrt (RWPI.SqrtLasso.transportCost (fun w w' => ENNReal.ofReal (‖w - w'‖ ^ 2)) μ ν).toReal

variable {d n : ℕ} {𝒵 : Type*}

/-- `r((x, v), (x′, v′)) = α₁‖x − x′‖ + ‖x − x′ + γ⁻¹(v − v′)‖` (p. 39). -/
noncomputable def rdist (p : Params) (q q' : E d × E d) : ℝ :=
  p.α1 * ‖q.1 - q'.1‖ + ‖q.1 - q'.1 + p.γ⁻¹ • (q.2 - q'.2)‖

/-- `ρ((x, v), (x′, v′)) = h(r((x, v), (x′, v′)))·(1 + ε₁𝒱(x, v) + ε₁𝒱(x′, v′))` (p. 39), with
`ε₁` of (A.16) and the Lyapunov function `𝒱` of the dataset `z`. -/
noncomputable def rho (p : Params) (h : ℝ → ℝ) (f : E d → 𝒵 → ℝ) (z : Fin n → 𝒵)
    (q q' : E d × E d) : ℝ :=
  h (rdist p q q') * (1 + eps1 p d * lyap p f z q.1 q.2 + eps1 p d * lyap p f z q'.1 q'.2)

/-- `ℋ_ρ(μ, ν) = inf_{(X,V)∼μ, (X′,V′)∼ν} E[ρ((X, V), (X′, V′))]` (A.12), valued in `[0, ∞]`. -/
noncomputable def Hrho (p : Params) (h : ℝ → ℝ) (f : E d → 𝒵 → ℝ) (z : Fin n → 𝒵)
    (μ ν : Measure (E d × E d)) : ENNReal :=
  RWPI.SqrtLasso.transportCost (fun q q' => ENNReal.ofReal (rho p h f z q q')) μ ν

/-- The class of functions `h` on p. 39: `h : [0, ∞) → [0, ∞)` continuous, non-decreasing,
concave, `h(0) = 0`, `C²` on `(0, R₁)` with `R₁ > 0`, right derivative `h′₊(0) = 1`, left
derivative `h′₋(R₁) > 0`, and `h` constant on `[R₁, ∞)`. -/
def IsEGZProfile (h : ℝ → ℝ) (R1 : ℝ) : Prop :=
  0 < R1 ∧ ContinuousOn h (Set.Ici 0) ∧ MonotoneOn h (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) h ∧ (∀ r, 0 ≤ r → 0 ≤ h r) ∧ h 0 = 0 ∧
    ContDiffOn ℝ 2 h (Set.Ioo 0 R1) ∧ HasDerivWithinAt h 1 (Set.Ici 0) 0 ∧
    (∃ c, 0 < c ∧ HasDerivWithinAt h c (Set.Iic R1) R1) ∧ ∀ r, R1 ≤ r → h r = h R1

end SGHMCOpt.Euler


