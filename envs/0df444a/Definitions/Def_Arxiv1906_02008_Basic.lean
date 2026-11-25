-- Prove2me | Definitions.Def_Arxiv1906_02008_Basic
-- name    : Arxiv1906_02008_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T14:31:25.944277+00:00
-- url     : https://prove2.me/theorems/a4da3d6a-c101-4a71-8d20-825ac9bda638
-- title:
--   Hyperplanes, strips, model far field patterns and indicators for multi-frequency sparse backscattering
-- statement:
--   Objects of Sections 2-4 of Ji and Liu, *Inverse acoustic scattering problems with multi-frequency sparse backscattering far field data* (arXiv:1906.02008v2).
--
--   1. **Space and directions.** $\mathbb{R}^n$ with $n\in\{2,3\}$ (stated in each theorem), the Euclidean inner product $x\cdot y$ and Lebesgue measure. Directions $\hat x,\theta$ are unit vectors. Wave numbers lie in a band $(k_-,k^+)$ with $0<k_-<k^+$.
--   2. **Surface measure.** $ds$ is the $(n-1)$-dimensional Hausdorff measure, normalised by $\omega_{n-1}/2^{n-1}$ ($\omega_m$ the volume of the unit ball of $\mathbb{R}^m$), so that it equals Lebesgue measure on hyperplanes.
--   3. **Hyperplanes and strips (eqs. (3.11)-(3.12), p. 5; strip, p. 7).** $\phi=(\theta-\hat x)/|\theta-\hat x|$ and $\Pi_\alpha=\{y:\ y\cdot(\theta-\hat x)+\alpha=0\}$. For $D\subset\mathbb{R}^n$ and a direction $\theta$, the $\theta$-strip is $S_D(\theta)=\{y:\ \inf_{z\in D}z\cdot\theta\le y\cdot\theta\le\sup_{z\in D}z\cdot\theta\}$.
--   4. **Scatterers (Section 2).** A scattering domain is an open, bounded, nonempty set $D$ with Lipschitz boundary (near each boundary point, $D$ is the region above the graph of a Lipschitz function in some direction $e$) whose exterior $\mathbb{R}^n\setminus\overline D$ is connected. A medium is a refractive index $q>0$ with $q-1$ integrable and $\operatorname{supp}(q-1)=\overline D$, $D$ a scattering domain. An obstacle is sound-soft ($\gamma_D=-2$) or sound-hard ($\gamma_D=2$).
--   5. **Model far field patterns.**
--      - Point-like scatterers (eq. (3.10)): $\tilde u^\infty(\hat x,\theta,k)=\sum_{m=1}^M\tau_me^{ikz_m\cdot(\theta-\hat x)}$, $z_m\in\mathbb{R}^n$, $\tau_m\in\mathbb{C}$.
--      - Born approximation (eq. (3.14)): $u_B^\infty(\hat x,\theta,k)=k^2\int_{\mathbb{R}^n}e^{ik(\theta-\hat x)\cdot y}[q(y)-1]\,dy$, and $\hat q(\alpha)=\int_{\Pi_\alpha}[q(y)-1]\,ds(y)$ (eq. (3.15)).
--      - Kirchhoff approximation (eq. (3.21)): with $\nu$ the outward unit normal and $\partial D_-(\theta)=\{x\in\partial D:\ \nu(x)\cdot\theta<0\}$ the illuminated part (eq. (3.17)), $K(\hat x,\theta,k)=\gamma_D\int_{\partial D_-(\theta)}\partial_\nu e^{ik\theta\cdot y}\,e^{-ik\hat x\cdot y}\,ds(y)$, where $\partial_\nu e^{ik\theta\cdot y}=ik\,(\nu(y)\cdot\theta)e^{ik\theta\cdot y}$.
--      - Eq. (3.22): $U^\infty(\hat x,\theta,k)=-k^2\,\theta\cdot(\theta-\hat x)\,\gamma_D\int_{\mathbb{R}^n}\chi_D(y)e^{ik(\theta-\hat x)\cdot y}\,dy$.
--   6. **Indicators (eqs. (4.25)-(4.26)).** For far field data $u^\infty(\hat x,\theta,k)$,
--   $$I_1(z,\hat x,\theta)=\Big|\int_{k_-}^{k^+}u^\infty(\hat x,\theta,k)e^{-ikz\cdot(\theta-\hat x)}dk\Big|,\quad I_2(z,\hat x,\theta)=\Big|\int_{k_-}^{k^+}\big(u^\infty(\hat x,\theta,k)+\overline{u^\infty(-\hat x,-\theta,k)}\big)e^{-ikz\cdot(\theta-\hat x)}dk\Big|.$$
--
--   **Formalization Note** The outward normal of a convex obstacle at a boundary point $x$ is defined as the unique unit vector $v$ with $(y-x)\cdot v\le0$ for all $y\in D$ when it is unique (which is the case for $ds$-almost every boundary point of a convex body), and $0$ otherwise. The paper's direction sets $\mathcal A_1,\mathcal A_2,\mathcal A_3$ are not defined: every pair of unit vectors belongs to some $\mathcal A_3$, so "$(\hat x,\theta)\in\mathcal A_j$ for some $j$" is the hypothesis that $\hat x,\theta$ are unit vectors. The exact far field pattern $u^\infty$ of an obstacle or medium (a solution of an exterior Helmholtz problem) is not defined; the statements concern the paper's model far fields (3.10), (3.14), (3.21), (3.22), and Proposition 4.1 concerns arbitrary data $u^\infty$.
-- source:
--   Xia Ji and Xiaodong Liu, Inverse acoustic scattering problems with multi-frequency sparse backscattering far field data, arXiv:1906.02008v2 (2019), Sections 2-4 (eqs. (3.10)-(3.12), (3.14)-(3.15), (3.17), (3.21)-(3.22), (4.25)-(4.26))

import Mathlib

/-!
Xia Ji and Xiaodong Liu, *Inverse acoustic scattering problems with multi-frequency sparse
backscattering far field data*, arXiv:1906.02008v2 (2019): the geometric objects (hyperplanes,
strips, scattering domains, surface measure), the three model far field patterns (point-like
scatterers eq. (3.10), Born approximation eq. (3.14), Kirchhoff approximation eqs. (3.21)-(3.22))
and the indicators (4.25)-(4.26) of Sections 2-4.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Arxiv1906_02008

/-- Section 2: the ambient space `ℝ^n` (the paper takes `n = 2, 3`), with its Euclidean inner
product and Lebesgue measure. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The Lebesgue volume `ω_m` of the unit ball of `ℝ^m`. -/
def unitBallVolume (m : ℕ) : ℝ :=
  (volume (Metric.ball (0 : Rn m) 1)).toReal

/-- The surface measure `ds` on hypersurfaces of `ℝ^n` used in eqs. (3.15), (3.20)-(3.21) and
(3.24): the `(n-1)`-dimensional Hausdorff measure, normalised by `ω_{n-1} / 2^{n-1}` so that it
agrees with Lebesgue measure on hyperplanes. -/
def surfMeas (n : ℕ) : Measure (Rn n) :=
  ENNReal.ofReal (unitBallVolume (n - 1) / 2 ^ (n - 1)) • μH[((n - 1 : ℕ) : ℝ)]

/-- Eq. (3.12), p. 5: the hyperplane `Π_α = {y ∈ ℝ^n | y · (θ - x̂) + α = 0}` with normal along
`θ - x̂`. -/
def hyperplane {n : ℕ} (xh θ : Rn n) (α : ℝ) : Set (Rn n) :=
  {y | ⟪y, θ - xh⟫ + α = 0}

/-- Eq. (3.11), p. 5: the unit vector `φ = (θ - x̂) / |θ - x̂|`. -/
def phiDir {n : ℕ} (xh θ : Rn n) : Rn n :=
  ‖θ - xh‖⁻¹ • (θ - xh)

/-- Section 3, p. 7: the `θ`-strip hull
`S_D(θ) = {y ∈ ℝ^n | inf_{z ∈ D} z · θ ≤ y · θ ≤ sup_{z ∈ D} z · θ}` of a set `D`. -/
def strip {n : ℕ} (D : Set (Rn n)) (θ : Rn n) : Set (Rn n) :=
  {y | sInf ((fun z => ⟪z, θ⟫) '' D) ≤ ⟪y, θ⟫ ∧ ⟪y, θ⟫ ≤ sSup ((fun z => ⟪z, θ⟫) '' D)}

/-- Section 2, p. 3: `D` has Lipschitz boundary: near every boundary point `x`, in a direction
`e`, `D` is the region above the graph of a Lipschitz function over the hyperplane `e^⊥`. -/
def IsLipschitzDomain {n : ℕ} (D : Set (Rn n)) : Prop :=
  ∀ x ∈ frontier D, ∃ r > (0 : ℝ), ∃ e : Rn n, ‖e‖ = 1 ∧
    ∃ (g : Rn n → ℝ) (L : NNReal), LipschitzWith L g ∧
      D ∩ Metric.ball x r =
        {y | y ∈ Metric.ball x r ∧ g ((y - x) - ⟪y - x, e⟫ • e) < ⟪y - x, e⟫}

/-- Section 2, p. 3: the standing assumptions on a scatterer `D ⊂ ℝ^n`: an open, bounded,
nonempty domain with Lipschitz boundary whose exterior `ℝ^n \ D̄` is connected. -/
def IsScatteringDomain {n : ℕ} (D : Set (Rn n)) : Prop :=
  IsOpen D ∧ Bornology.IsBounded D ∧ D.Nonempty ∧ IsLipschitzDomain D ∧
    IsConnected (closure D)ᶜ

/-- Eq. (3.10), p. 5 (with eq. (2.3), p. 3): the far field pattern of `M` point-like scatterers at `z_m` with scattering
strengths `τ_m ∈ ℂ`, neglecting multiple scattering:
`ũ^∞(x̂, θ, k) = ∑_m τ_m e^{i k z_m · (θ - x̂)}`. -/
def pointFarField {n M : ℕ} (z : Fin M → Rn n) (τ : Fin M → ℂ) (xh θ : Rn n) (k : ℝ) : ℂ :=
  ∑ m, τ m * Complex.exp (Complex.I * (k : ℂ) * (⟪z m, θ - xh⟫ : ℂ))

/-- Section 2, p. 3 (penetrable medium): `q` is a refractive index (`q > 0`) such that `q - 1` is
integrable and has support `D̄`, where `D` satisfies the standing assumptions. -/
def IsMedium {n : ℕ} (q : Rn n → ℝ) (D : Set (Rn n)) : Prop :=
  IsScatteringDomain D ∧ (∀ y, 0 < q y) ∧ Integrable (fun y => q y - 1) ∧
    tsupport (fun y => q y - 1) = closure D

/-- Eq. (3.14), p. 6: the far field pattern of the Born approximation,
`u_B^∞(x̂, θ, k) = k² ∫_{ℝ^n} e^{i k (θ - x̂) · y} [q(y) - 1] dy`. -/
def bornFarField {n : ℕ} (q : Rn n → ℝ) (xh θ : Rn n) (k : ℝ) : ℂ :=
  (k : ℂ) ^ 2 * ∫ y, Complex.exp (Complex.I * (k : ℂ) * (⟪θ - xh, y⟫ : ℂ)) * ((q y - 1 : ℝ) : ℂ)

/-- Eq. (3.15), p. 6: `q̂(α) = ∫_{Π_α} [q(y) - 1] ds(y)`. -/
def qhat {n : ℕ} (q : Rn n → ℝ) (xh θ : Rn n) (α : ℝ) : ℝ :=
  ∫ y in hyperplane xh θ α, (q y - 1) ∂(surfMeas n)

/-- Section 3, p. 8 (after eq. (3.21)): `γ_D = -2` if `D` is sound-soft (`soft = true`) and `γ_D = 2` if `D` is
sound-hard (`soft = false`). -/
def gammaD (soft : Bool) : ℝ :=
  if soft then -2 else 2

/-- Eq. (3.22), p. 8: `U^∞(x̂, θ, k) = -k² θ · (θ - x̂) γ_D ∫_{ℝ^n} χ_D(y) e^{i k (θ - x̂) · y} dy`,
where `χ_D` is the characteristic function of `D`. -/
def kirchhoffU {n : ℕ} (soft : Bool) (D : Set (Rn n)) (xh θ : Rn n) (k : ℝ) : ℂ :=
  -((k : ℂ) ^ 2 * (⟪θ, θ - xh⟫ : ℂ) * (gammaD soft : ℂ)) *
    ∫ y in D, Complex.exp (Complex.I * (k : ℂ) * (⟪θ - xh, y⟫ : ℂ))

/-- Section 2, p. 4 ("`ν` is the unit outward normal"): `v` is an outward unit normal of the convex set `D` at `x`, i.e. the unit
normal of a supporting hyperplane of `D` at `x` pointing away from `D`. -/
def IsOutwardNormal {n : ℕ} (D : Set (Rn n)) (x v : Rn n) : Prop :=
  ‖v‖ = 1 ∧ ∀ y ∈ D, ⟪y - x, v⟫ ≤ 0

open Classical in
/-- Section 2, p. 4: the unit outward normal `ν(x)` of a convex obstacle `D` at `x ∈ ∂D`, where
it is unique (which holds for `ds`-almost every `x ∈ ∂D`); `0` elsewhere. -/
def outwardNormal {n : ℕ} (D : Set (Rn n)) (x : Rn n) : Rn n :=
  if h : ∃! v, IsOutwardNormal D x v then h.exists.choose else 0

/-- Eq. (3.17), p. 7: the illuminated region `∂D₋(θ) = {x ∈ ∂D | ν(x) · θ < 0}`. -/
def illuminated {n : ℕ} (D : Set (Rn n)) (θ : Rn n) : Set (Rn n) :=
  {x | x ∈ frontier D ∧ ⟪outwardNormal D x, θ⟫ < 0}

/-- Eq. (3.21), p. 8: the Kirchhoff approximation of the far field of a convex sound-soft or
sound-hard obstacle,
`γ_D ∫_{∂D₋(θ)} ∂_ν e^{i k θ · y} e^{-i k x̂ · y} ds(y)`, with the normal derivative written out:
`∂_ν e^{i k θ · y} = i k (ν(y) · θ) e^{i k θ · y}`. -/
def kirchhoffFarField {n : ℕ} (soft : Bool) (D : Set (Rn n)) (xh θ : Rn n) (k : ℝ) : ℂ :=
  (gammaD soft : ℂ) * ∫ y in illuminated D θ,
    (Complex.I * (k : ℂ) * (⟪outwardNormal D y, θ⟫ : ℂ)) *
      Complex.exp (Complex.I * (k : ℂ) * (⟪θ, y⟫ : ℂ)) *
        Complex.exp (-(Complex.I * (k : ℂ) * (⟪xh, y⟫ : ℂ))) ∂(surfMeas n)

/-- Eq. (4.25), p. 10: the single-pair indicator
`I₁(z, x̂, θ) = |∫_{k₋}^{k⁺} u^∞(x̂, θ, k) e^{-i k z · (θ - x̂)} dk|` for far field data
`u^∞ = u (x̂) (θ) (k)`. -/
def indicatorI1 {n : ℕ} (u : Rn n → Rn n → ℝ → ℂ) (km kp : ℝ) (xh θ z : Rn n) : ℝ :=
  ‖∫ k in km..kp, u xh θ k * Complex.exp (-(Complex.I * (k : ℂ) * (⟪z, θ - xh⟫ : ℂ)))‖

/-- Eq. (4.26), p. 10: the single-pair indicator
`I₂(z, x̂, θ) = |∫_{k₋}^{k⁺} (u^∞(x̂, θ, k) + conj u^∞(-x̂, -θ, k)) e^{-i k z · (θ - x̂)} dk|`. -/
def indicatorI2 {n : ℕ} (u : Rn n → Rn n → ℝ → ℂ) (km kp : ℝ) (xh θ z : Rn n) : ℝ :=
  ‖∫ k in km..kp, (u xh θ k + starRingEnd ℂ (u (-xh) (-θ) k)) *
      Complex.exp (-(Complex.I * (k : ℂ) * (⟪z, θ - xh⟫ : ℂ)))‖

end Arxiv1906_02008


