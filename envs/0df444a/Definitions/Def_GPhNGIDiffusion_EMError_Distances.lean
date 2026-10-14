-- Prove2me | Definitions.Def_GPhNGIDiffusion_EMError_Distances
-- name    : GPhNGIDiffusion_EMError_Distances
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:44.942233+00:00
-- url     : https://prove2.me/theorems/8bfa3a21-f05b-4074-8781-fb3e3a7242cc
-- title:
--   Wasserstein-1 distance $d_W$ (dual form), total variation $\|\cdot\|_{\mathrm{TV}}$ and weighted total variation $\|\cdot\|_{\mathrm{TV},V}$
-- statement:
--   Let $\mathrm{Lip}(1)$ be the set of functions $h:\mathbb R^d\to\mathbb R$ with $|h(x)-h(y)|\le|x-y|$ for all $x,y$, and $\mathrm{Lip}_0(1)=\{h\in\mathrm{Lip}(1):h(0)=0\}$. For probability measures $\mu_1,\mu_2$ on $\mathbb R^d$ with finite first moments, the **Wasserstein-1 distance** is
--   $$
--   d_W(\mu_1,\mu_2)=\sup_{h\in\mathrm{Lip}(1)}\Big|\int h\,d\mu_1-\int h\,d\mu_2\Big|.
--   $$
--   The **total variation distance** is
--   $$
--   \|\mu_1-\mu_2\|_{\mathrm{TV}}=\sup\Big\{\Big|\int h\,d\mu_1-\int h\,d\mu_2\Big| : h \text{ measurable},\ |h|\le 1\Big\},
--   $$
--   and, for a weight $V:\mathbb R^d\to[0,\infty)$, the **weighted total variation norm** is
--   $$
--   \|\mu_1-\mu_2\|_{\mathrm{TV},V}=\sup\Big\{\Big|\int \phi\,d\mu_1-\int \phi\,d\mu_2\Big| : \phi \text{ measurable},\ |\phi(x)|\le 1+V(x)\ \forall x\Big\},
--   $$
--   i.e. the supremum over $\|\phi\|_V=\sup_x|\phi(x)|/(1+V(x))\le 1$.
--
--   These are the three distances in which the paper measures the error and the ergodicity of the diffusion and of its Euler–Maruyama scheme.
--
--   **Formalization Note** All three take values in $[0,\infty]$. $d_W$ is $+\infty$ unless both measures are finite with finite first moment, the total variation is $+\infty$ unless both are finite, and the weighted norm is $+\infty$ unless $\int(1+V)\,d\mu_i<\infty$ for both. Under these conditions every test function is integrable, so no integral takes Lean's default value $0$. The total variation norm is defined as printed, which is twice $\sup_A|\mu_1(A)-\mu_2(A)|$. $d_W$ is the dual (Lipschitz test function) form; its equality with the coupling form is the Kantorovich–Rubinstein theorem and is not used.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 8, (1.5) and the definitions of the total variation and weighted total variation norms

import Mathlib
import Definitions.Def_EthierKurtz_SDEState

open MeasureTheory
open scoped ENNReal

namespace GPhNGIDiffusion.EMError

variable {d : ℕ}

/-- `h ∈ Lip(1)`: `|h(x) − h(y)| ≤ |x − y|` for all `x, y ∈ ℝ^d` (§1.4, p. 8). -/
def IsLip1 (h : EthierKurtz.SDEState d → ℝ) : Prop :=
  ∀ x y, |h x - h y| ≤ ‖x - y‖

/-- `h ∈ Lip₀(1)`: `h ∈ Lip(1)` and `h(0) = 0` (§1.4, p. 8). -/
def IsLip1Zero (h : EthierKurtz.SDEState d → ℝ) : Prop :=
  IsLip1 h ∧ h 0 = 0

/-- The Wasserstein-1 distance in the dual form (1.5), p. 8:
`d_W(µ₁, µ₂) = sup_{h ∈ Lip(1)} |∫ h dµ₁ − ∫ h dµ₂|`.
It is valued in `[0, ∞]` and set to `∞` unless both measures are finite and have a finite first
moment; under those conditions every `h ∈ Lip(1)` is integrable, so no integral below takes Lean's
default value. -/
noncomputable def dW (μ₁ μ₂ : Measure (EthierKurtz.SDEState d)) : ℝ≥0∞ :=
  if μ₁ Set.univ < ∞ ∧ μ₂ Set.univ < ∞ ∧
      (∫⁻ x, ‖x‖ₑ ∂μ₁) < ∞ ∧ (∫⁻ x, ‖x‖ₑ ∂μ₂) < ∞ then
    ⨆ (h : EthierKurtz.SDEState d → ℝ) (_ : IsLip1 h),
      ENNReal.ofReal |∫ x, h x ∂μ₁ - ∫ x, h x ∂μ₂|
  else ⊤

/-- The total variation distance (p. 8):
`‖µ₁ − µ₂‖_TV = sup { |∫ h dµ₁ − ∫ h dµ₂| : h ∈ B_b(ℝ^d, ℝ), ‖h‖_∞ ≤ 1 }`
(twice the probabilists' `sup_A |µ₁(A) − µ₂(A)|`). Set to `∞` unless both measures are finite. -/
noncomputable def tvNorm (μ₁ μ₂ : Measure (EthierKurtz.SDEState d)) : ℝ≥0∞ :=
  if μ₁ Set.univ < ∞ ∧ μ₂ Set.univ < ∞ then
    ⨆ (h : EthierKurtz.SDEState d → ℝ) (_ : Measurable h ∧ ∀ x, |h x| ≤ 1),
      ENNReal.ofReal |∫ x, h x ∂μ₁ - ∫ x, h x ∂μ₂|
  else ⊤

/-- The weighted total variation norm (p. 8), for a weight `V : ℝ^d → ℝ₊`:
`‖µ₁ − µ₂‖_{TV,V} = sup { |∫ ϕ dµ₁ − ∫ ϕ dµ₂| : ‖ϕ‖_V ≤ 1 }`, where
`‖ϕ‖_V = sup_x |ϕ(x)| / (1 + V(x))`, i.e. the supremum over measurable `ϕ` with
`|ϕ(x)| ≤ 1 + V(x)` for all `x`. Set to `∞` unless `∫ (1 + V) dµᵢ < ∞` for both measures; under that
condition every admissible `ϕ` is integrable. -/
noncomputable def tvNormWeighted (V : EthierKurtz.SDEState d → ℝ)
    (μ₁ μ₂ : Measure (EthierKurtz.SDEState d)) : ℝ≥0∞ :=
  if (∫⁻ x, ENNReal.ofReal (1 + V x) ∂μ₁) < ∞ ∧ (∫⁻ x, ENNReal.ofReal (1 + V x) ∂μ₂) < ∞ then
    ⨆ (ϕ : EthierKurtz.SDEState d → ℝ) (_ : Measurable ϕ ∧ ∀ x, |ϕ x| ≤ 1 + V x),
      ENNReal.ofReal |∫ x, ϕ x ∂μ₁ - ∫ x, ϕ x ∂μ₂|
  else ⊤

end GPhNGIDiffusion.EMError


