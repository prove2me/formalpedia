-- Prove2me | Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves
-- name    : GlobalInexactNewton_Backtracking_Supplement_EqualityCurves
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:44:13.814704+00:00
-- url     : https://prove2.me/theorems/994ce676-bb95-4abe-90b9-3bc38806f726
-- title:
--   Continuous equality curves, ECMR/ECTL runs, and the angle (7.3)
-- statement:
--   Let $F$ map a finite-dimensional real normed space to itself. An equality curve at $x$ with initial level $\bar\eta$ is continuous on $[\bar\eta,1]$, has $\sigma(1)=0$, and satisfies
--
--   $$\|F(x)+F'(x)\sigma(\eta)\|=\eta\|F(x)\|\quad(\bar\eta\le\eta\le1).$$
--
--   ECMR and ECTL are the published MR and TL runs with this additional restriction at every iteration. Their rejected trials, accepted trials, parameter ranges and TL level updates are inherited unchanged. For an inner product norm, the absolute cosine is $a(x,s)=|\langle F(x),F'(x)s\rangle|/(\|F(x)\|\|F'(x)s\|)$ and the curve angle is $\gamma_x=\inf_{\bar\eta\le\eta<1}a(x,\sigma(\eta))$. A uniform angle condition means that there exist $\gamma,\delta>0$ such that $a(x_k,\sigma_k(\eta))\ge\gamma$ for every nonzero-residual iterate in $N_\delta(x_*)$ and every $\eta\in[\bar\eta_k,1)$.
--
--   These definitions isolate the extra data of §7 without changing either algorithm. **Formalization Note** A run on infinite sequences means no breakdown. The derivative is `fderiv ℝ F`; theorems assume continuous differentiability. In the real infimum's intended domain, the interval is nonempty and the angle values lie in $[0,1]$. Equality at levels below one ensures nonzero denominator when $F(x)\ne0$. Uniform lower bounds use the equivalent pointwise formulation, with a single neighborhood and constant.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 412, Continuous equality curves (7.1); DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Extras

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The additional restrictions in (7.1). -/
def IsEqualityCurve (F : E → E) (x : E) (ηbar : ℝ) (σ : ℝ → E) : Prop :=
  ContinuousOn σ (Set.Icc ηbar 1) ∧ σ 1 = 0 ∧
    ∀ η ∈ Set.Icc ηbar 1, ‖F x + fderiv ℝ F x (σ η)‖ = η * ‖F x‖

/-- ECMR is the published MR run with continuous equality curves. -/
def IsECMRRun (F : E → E) (ηmax t θmin θmax : ℝ) (x : ℕ → E)
    (ηbar : ℕ → ℝ) (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) : Prop :=
  IsMRRun F ηmax t θmin θmax x ηbar σ θ m ∧
    ∀ k, IsEqualityCurve F (x k) (ηbar k) (σ k)

/-- ECTL is the published TL run with continuous equality curves; no ηmax bound. -/
def IsECTLRun (F : E → E) (t u θmin θmax : ℝ) (x : ℕ → E)
    (ηbar : ℕ → ℝ) (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) : Prop :=
  IsTLRun F t u θmin θmax x ηbar σ θ m ∧
    ∀ k, IsEqualityCurve F (x k) (ηbar k) (σ k)

section Inner
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Absolute cosine with a derivative image, only used with nonzero denominator. -/
noncomputable def residualAngle (F : H → H) (x s : H) : ℝ :=
  |inner ℝ (F x) (fderiv ℝ F x s)| / (‖F x‖ * ‖fderiv ℝ F x s‖)

/-- (7.3): the endpoint 1 is excluded. -/
noncomputable def curveAngle (F : H → H) (x : H) (ηbar : ℝ) (σ : ℝ → H) : ℝ :=
  sInf ((fun η => residualAngle F x (σ η)) '' Set.Ico ηbar 1)

/-- Equivalent pointwise form of (7.7), with one γ and one neighborhood. -/
def UniformCurveAngle (F : H → H) (xstar : H) (x : ℕ → H) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → H) : Prop :=
  ∃ γ > 0, ∃ δ > 0, ∀ k, x k ∈ Metric.ball xstar δ → F (x k) ≠ 0 →
    ∀ η ∈ Set.Ico (ηbar k) 1, γ ≤ residualAngle F (x k) (σ k η)
end Inner

end GlobalInexactNewton.Backtracking.Supplement


