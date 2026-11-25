-- Prove2me | Definitions.Def_Arxiv2405_10327_Basic
-- name    : Arxiv2405_10327_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T17:50:30.856702+00:00
-- url     : https://prove2.me/theorems/c94a7839-4dd0-549f-8b7f-2079570fa5e9
-- title:
--   WISER refinement objectives: constrained form (eq. 1), weak form (eq. 2) and Algorithm 1 losses
-- statement:
--   Objects of Section 3 (physics-based refinements), eq. (1), eq. (2) and Algorithm 1 of Yin, Orozco and Herrmann (2024).
--
--   1. **Spaces.** Velocity models and latent codes are vectors of $\mathbb{R}^d$, seismic data are vectors of $\mathbb{R}^m$, and the weights of the refinement network are vectors $\phi\in\mathbb{R}^p$, all with the Euclidean norm $\|\cdot\|_2$.
--   2. **Given maps.** $\mathcal F:\mathbb{R}^d\to\mathbb{R}^m$ is the forward operator, $y_{\mathrm{obs}}\in\mathbb{R}^m$ the observed data, and $\sigma$ the noise standard deviation. $f_{\theta^*}^{-1}(\cdot\,;\bar y_{\mathrm{obs}})$ is the inverse of the trained conditional normalizing flow at the common-image gathers $\bar y_{\mathrm{obs}}$. $h_\phi:\mathbb{R}^d\to\mathbb{R}^d$ is the refinement network with weights $\phi$, and $z_1,\dots,z_M\in\mathbb{R}^d$ are the latent draws of Algorithm 1.
--   3. **Terms.** The data misfit is $\|\mathcal F(x)-y_{\mathrm{obs}}\|_2^2/(2\sigma^2)$. The latent terms are $\tfrac12\|h_\phi(z)\|_2^2-\log|\det J_{h_\phi}(z)|$, where $J_{h_\phi}(z)$ is the Jacobian of $h_\phi$ at $z$. The corrected velocity model is $f_{\theta^*}^{-1}(h_\phi(z);\bar y_{\mathrm{obs}})$.
--   4. **Constrained objective (eq. 1), sample form.** $\phi\mapsto\frac1M\sum_{i=1}^M\Big[\frac1{2\sigma^2}\|\mathcal F\circ f_{\theta^*}^{-1}(h_\phi(z_i);\bar y_{\mathrm{obs}})-y_{\mathrm{obs}}\|_2^2+\tfrac12\|h_\phi(z_i)\|_2^2-\log|\det J_{h_\phi}(z_i)|\Big]$. This is the integrand of eq. (1) averaged over the draws $z_i$ instead of integrated against $\mathrm N(0,I)$.
--   5. **Weak objective (eq. 2).** For $\gamma>0$, $J_\gamma(x_{1:M},\phi)=\frac1M\sum_{i=1}^M\Big[\frac1{2\sigma^2}\|\mathcal F(x_i)-y_{\mathrm{obs}}\|_2^2+\frac1{2\gamma^2}\|x_i-f_{\theta^*}^{-1}(h_\phi(z_i);\bar y_{\mathrm{obs}})\|_2^2+\tfrac12\|h_\phi(z_i)\|_2^2-\log|\det J_{h_\phi}(z_i)|\Big]$.
--   6. **Weak objective at $\gamma=0$.** $J_0$ takes values in $(-\infty,+\infty]$. It equals the $\gamma$-independent terms of eq. (2) when $x_i=f_{\theta^*}^{-1}(h_\phi(z_i);\bar y_{\mathrm{obs}})$ for every $i$, and $+\infty$ otherwise. The penalty is $0$ at $v=0$ and $+\infty$ elsewhere, which is the pointwise limit of $\|v\|_2^2/(2\gamma^2)$ as $\gamma\to0^+$.
--   7. **Algorithm 1 losses.** The inner-loop loss (line 29) is $\mathcal L(\phi)=\sum_{i=1}^M\Big[\frac1{2\gamma^2}\|x_i-f_{\theta^*}^{-1}(h_\phi(z_i);\bar y_{\mathrm{obs}})\|_2^2+\tfrac12\|h_\phi(z_i)\|_2^2-\log|\det J_{h_\phi}(z_i)|\Big]$. The outer-loop step $g_i$ (line 25) is the gradient of $v\mapsto\frac1{2\sigma^2}\|\mathcal F(v)-y_{\mathrm{obs}}\|_2^2+\frac1{2\gamma^2}\|v-f_{\theta^*}^{-1}(h_\phi(z_i);\bar y_{\mathrm{obs}})\|_2^2$ at $x_i$.
--
--   **Formalization Note** The forward operator, the inverse flow and the refinement networks are arbitrary given maps, because the paper's statements about eqs. (1) and (2) do not depend on their form. The paper writes $\log|\det J_{h_\phi}|$ without an argument; here the Jacobian is taken at the latent draw $z_i$ (at $z$ in eq. (1)). Where $\det J_{h_\phi}(z_i)=0$ the paper's term $-\log|\det J|$ would be $+\infty$; the formal term is then $0$. It enters both sides of every statement identically. The weak objective is used for $\gamma>0$ only, and its $\gamma=0$ value is the separate extended-real objective of item 6.
-- source:
--   Yin, Orozco and Herrmann, WISER: multimodal variational inference for full-waveform inversion without dimensionality reduction, arXiv:2405.10327v2 (2024), Section 3 (Physics-based refinements), eqs. (1)-(2), PDF p. 4; Algorithm 1 lines 18-34, PDF p. 3

import Mathlib

/-!
Yin, Orozco and Herrmann, *WISER: multimodal variational inference for full-waveform inversion
without dimensionality reduction*, arXiv:2405.10327v2 (2024): the objects of Section 3
(physics-based refinements), eq. (1), eq. (2) and Algorithm 1, lines 22-32.

Velocity models, latent codes and seismic data are vectors of Euclidean spaces; the forward
operator `F`, the inverse of the trained conditional normalizing flow at a fixed conditioning
`fInv (·) c` and the refinement networks `h φ` (weights `φ ∈ ℝ^p`) are given maps.
-/

noncomputable section

namespace Arxiv2405_10327

/-- Euclidean space `ℝ^n` with the `ℓ₂` norm, used for velocity models, latent codes, seismic
data and network weights (Section 1 and Section 3). -/
abbrev Vec (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- `log |det J_h(z)|`, the log-absolute-determinant of the Jacobian of a map `h : ℝ^d → ℝ^d` at
`z` (the term `log |det J_{h_φ}|` of eq. (1), eq. (2) and Algorithm 1 line 29, Section 3). -/
def logAbsDetJac {d : ℕ} (h : Vec d → Vec d) (z : Vec d) : ℝ :=
  Real.log |(fderiv ℝ h z).det|

/-- The data-misfit term `‖F(x) - y_obs‖₂² / (2σ²)` of eq. (2) and Algorithm 1 line 25
(Section 3). -/
def dataMisfit {d m : ℕ} (σ : ℝ) (F : Vec d → Vec m) (yobs : Vec m) (x : Vec d) : ℝ :=
  ‖F x - yobs‖ ^ 2 / (2 * σ ^ 2)

/-- The latent terms `½‖h_φ(z)‖₂² - log |det J_{h_φ}(z)|` of eq. (1), eq. (2) and Algorithm 1
line 29 (Section 3). -/
def latentTerm {d : ℕ} (h : Vec d → Vec d) (z : Vec d) : ℝ :=
  ‖h z‖ ^ 2 / 2 - logAbsDetJac h z

/-- The corrected velocity model `f_{θ*}^{-1}(h_φ(z); ȳ_obs)`: the refinement network `h_φ`
followed by the inverse `fInv` of the trained CNF conditioned on the CIGs `ȳ_obs`
(Algorithm 1 lines 19 and 34, Section 3). -/
def corrected {d : ℕ} {C : Type*} (fInv : Vec d → C → Vec d) (ybar : C)
    (h : Vec d → Vec d) (z : Vec d) : Vec d :=
  fInv (h z) ybar

/-- The integrand of eq. (1) (Section 3, p. 4):
`‖F ∘ f_{θ*}^{-1}(h_φ(z); ȳ_obs) - y_obs‖₂²/(2σ²) + ½‖h_φ(z)‖₂² - log |det J_{h_φ}(z)|`. -/
def strongIntegrand {d m : ℕ} {C : Type*} (σ : ℝ) (F : Vec d → Vec m) (yobs : Vec m)
    (fInv : Vec d → C → Vec d) (ybar : C) (h : Vec d → Vec d) (z : Vec d) : ℝ :=
  dataMisfit σ F yobs (corrected fInv ybar h z) + latentTerm h z

/-- The constrained objective of eq. (1) evaluated with the latent draws `z_1, …, z_M` of
Algorithm 1 line 18 in place of the expectation over `z ∼ N(0, I)`:
`φ ↦ (1/M) ∑ᵢ [integrand of eq. (1) at zᵢ]` (Section 3, p. 4). -/
def strongSampleObjective {d m p M : ℕ} {C : Type*} (σ : ℝ) (F : Vec d → Vec m) (yobs : Vec m)
    (fInv : Vec d → C → Vec d) (ybar : C) (h : Vec p → Vec d → Vec d) (z : Fin M → Vec d)
    (φ : Vec p) : ℝ :=
  (1 / (M : ℝ)) * ∑ i, strongIntegrand σ F yobs fInv ybar (h φ) (z i)

/-- The weak (penalty) objective of eq. (2) (Section 3, p. 4), for `γ > 0`:
`(1/M) ∑ᵢ [‖F(xᵢ) - y_obs‖₂²/(2σ²) + ‖xᵢ - f_{θ*}^{-1}(h_φ(zᵢ); ȳ_obs)‖₂²/(2γ²)
+ ½‖h_φ(zᵢ)‖₂² - log |det J_{h_φ}(zᵢ)|]`. (At `γ = 0` the formula is not defined by the paper;
see `weakObjectiveHard`.) -/
def weakObjective {d m p M : ℕ} {C : Type*} (σ γ : ℝ) (F : Vec d → Vec m) (yobs : Vec m)
    (fInv : Vec d → C → Vec d) (ybar : C) (h : Vec p → Vec d → Vec d) (z : Fin M → Vec d)
    (x : Fin M → Vec d) (φ : Vec p) : ℝ :=
  (1 / (M : ℝ)) * ∑ i, (dataMisfit σ F yobs (x i)
    + ‖x i - corrected fInv ybar (h φ) (z i)‖ ^ 2 / (2 * γ ^ 2)
    + latentTerm (h φ) (z i))

/-- The hard penalty that replaces `‖v‖₂²/(2γ²)` at `γ = 0` (Section 3, p. 4, "Setting `γ` to
`0`"): `0` if `v = 0` and `+∞` otherwise, i.e. the pointwise limit of `‖v‖₂²/(2γ²)` as
`γ → 0⁺` in the extended reals. -/
def hardPenalty {d : ℕ} (v : Vec d) : EReal :=
  if v = 0 then 0 else ⊤

/-- The weak objective of eq. (2) with `γ` set to `0` (Section 3, p. 4), with values in the
extended reals: the `γ`-independent terms of eq. (2) plus the hard penalty
`∑ᵢ hardPenalty (xᵢ - f_{θ*}^{-1}(h_φ(zᵢ); ȳ_obs))`. -/
def weakObjectiveHard {d m p M : ℕ} {C : Type*} (σ : ℝ) (F : Vec d → Vec m) (yobs : Vec m)
    (fInv : Vec d → C → Vec d) (ybar : C) (h : Vec p → Vec d → Vec d) (z : Fin M → Vec d)
    (x : Fin M → Vec d) (φ : Vec p) : EReal :=
  (((1 / (M : ℝ)) * ∑ i, (dataMisfit σ F yobs (x i) + latentTerm (h φ) (z i)) : ℝ) : EReal)
    + ∑ i, hardPenalty (x i - corrected fInv ybar (h φ) (z i))

/-- The inner-loop loss `𝓛(φ)` of Algorithm 1 line 29 (Algorithm 1 on p. 3; Section 3, p. 4):
`∑ᵢ [‖xᵢ - f_{θ*}^{-1}(h_φ(zᵢ); ȳ_obs)‖₂²/(2γ²) + ½‖h_φ(zᵢ)‖₂² - log |det J_{h_φ}(zᵢ)|]`,
for fixed velocity models `x₁, …, x_M`. It does not involve the forward operator. -/
def innerLoss {d p M : ℕ} {C : Type*} (γ : ℝ) (fInv : Vec d → C → Vec d) (ybar : C)
    (h : Vec p → Vec d → Vec d) (z : Fin M → Vec d) (x : Fin M → Vec d) (φ : Vec p) : ℝ :=
  ∑ i, (‖x i - corrected fInv ybar (h φ) (z i)‖ ^ 2 / (2 * γ ^ 2) + latentTerm (h φ) (z i))

/-- The function whose gradient in `xᵢ` is the outer-loop step `gᵢ` of Algorithm 1 line 25
(Algorithm 1 on p. 3; Section 3, p. 4): `‖F(v) - y_obs‖₂²/(2σ²) + ‖v - f_{θ*}^{-1}(h_φ(zᵢ); ȳ_obs)‖₂²/(2γ²)`. -/
def outerLoss {d m : ℕ} {C : Type*} (σ γ : ℝ) (F : Vec d → Vec m) (yobs : Vec m)
    (fInv : Vec d → C → Vec d) (ybar : C) (hφ : Vec d → Vec d) (zi : Vec d) (v : Vec d) : ℝ :=
  dataMisfit σ F yobs v + ‖v - corrected fInv ybar hφ zi‖ ^ 2 / (2 * γ ^ 2)

end Arxiv2405_10327


