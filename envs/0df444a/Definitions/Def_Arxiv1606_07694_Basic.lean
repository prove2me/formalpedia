-- Prove2me | Definitions.Def_Arxiv1606_07694_Basic
-- name    : Arxiv1606_07694_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T23:18:18.994911+00:00
-- url     : https://prove2.me/theorems/d92609a1-6dd3-4d34-8f9d-87d198837644
-- title:
--   Perturbative kernels, Taylor forms and resummed scattering amplitude for a gently curved surface
-- statement:
--   Objects of Bimonte, *Wave-scattering from a gently curved surface* (arXiv:1606.07694v1), Sections "Perturbative expansion of the SA", "Resummation of the perturbative series" and "Comparison with Voronovich's small-slope approximation".
--
--   1. **Plane and momenta.** In-plane positions $\mathbf x$ and momenta $\mathbf k$ lie in $\mathbb R^2$, with components $\mathbf k^\mu$, $\mu\in\{1,2\}$. The incident and scattered waves have in-plane wave vectors $\mathbf k_0$, $\mathbf k$ and vertical wavenumbers $q_0=q(\mathbf k_0)$, $q=q(\mathbf k)$, where $q(\cdot)$ is an arbitrary complex-valued function.
--   2. **Reduced kernels (eqs. 6, 8).** A kernel family assigns to each order $n\ge0$ and each $\mathbf k,\mathbf k_0$ a complex function $\tilde G^{(n)}(\mathbf k_1,\dots,\mathbf k_n;\mathbf k,\mathbf k_0)$. It is symmetric if it is invariant under every permutation of $\mathbf k_1,\dots,\mathbf k_n$. The hyperplane is $\mathcal P^{(n)}=\{\mathbf k_1+\dots+\mathbf k_n+\mathbf k_0-\mathbf k=0\}$. Polarization indices are suppressed.
--   3. **Shift factor (eqs. 14, 15).** $c(\mathbf k,\mathbf k_0)=i(q_0+q)$.
--   4. **Taylor forms (eqs. 16, 19).** With $\kappa=(\mathbf k_1,\dots,\mathbf k_n)$ and $\|\kappa\|=\max_i|\mathbf k_i|$, a function $g$ has the second-order expansion (16) with coefficients $A,B_\mu,C_{\mu\nu},D_{\mu\nu}\in\mathbb C$ if
--   $$g(\kappa)=A+B_\mu\textstyle\sum_i\mathbf k_i^\mu+C_{\mu\nu}\sum_i\mathbf k_i^\mu\mathbf k_i^\nu-D_{\mu\nu}\sum_{i<j}\mathbf k_i^\mu\mathbf k_j^\nu+o(\|\kappa\|^2)\quad(\kappa\to0),$$
--   and the reduced expansion (19) if $g(\kappa)=A-D_{\mu\nu}\sum_{i<j}\mathbf k_i^\mu\mathbf k_j^\nu+o(\|\kappa\|^2)$. The truncated kernel of order $n$ built from coefficient families $A^{(n)}(\mathbf k,\mathbf k_0)$, $D^{(n)}(\mathbf k,\mathbf k_0)$ is $A^{(n)}-D^{(n)}_{\mu\nu}\sum_{i<j}\mathbf k_i^\mu\mathbf k_j^\nu$.
--   5. **Added term (eqs. 17, 18).** $f^{(n)}=(\mathbf k_1+\dots+\mathbf k_n+\mathbf k_0-\mathbf k)^\mu\big(\hat A_\mu+\hat B_{\mu\nu}(\mathbf k_1+\dots+\mathbf k_n)^\nu\big)$, which vanishes on $\mathcal P^{(n)}$.
--   6. **Height profile.** $h:\mathbb R^2\to\mathbb R$ is a Schwartz function. Its Fourier transform is $\tilde h(\mathbf k)=\int d^2\mathbf x\,h(\mathbf x)e^{-i\mathbf k\cdot\mathbf x}$, so that $h(\mathbf x)=\int\frac{d^2\mathbf k}{(2\pi)^2}\tilde h(\mathbf k)e^{i\mathbf k\cdot\mathbf x}$. In Voronovich's normalization it is $\tilde h_V=(2\pi)^{-2}\tilde h$. $\partial_\mu h$ is the partial derivative.
--   7. **Series terms (eq. 8).** For a kernel $T$ of order $n\ge1$, the $n$-th term is
--   $$\frac1{n!}\int\prod_{i=1}^n\frac{d^2\mathbf k_i}{(2\pi)^2}\,\tilde h(\mathbf k_1)\cdots\tilde h(\mathbf k_n)\,(2\pi)^2\delta^{(2)}(\mathbf k_1+\dots+\mathbf k_n+\mathbf k_0-\mathbf k)\,T(\mathbf k_1,\dots,\mathbf k_n),$$
--   with the delta function integrated out through $\mathbf k_n=\mathbf k-\mathbf k_0-\mathbf k_1-\dots-\mathbf k_{n-1}$. The result is a Lebesgue integral over $(\mathbb R^2)^{n-1}$ with prefactor $(2\pi)^{-2(n-1)}/n!$.
--   8. **Resummed amplitude (eq. 25).** The part of (25) that is a function of $\mathbf k$ is
--   $$\int d^2\mathbf x\,e^{i(\mathbf k_0-\mathbf k)\cdot\mathbf x}\Big[\frac{A^{(1)}}{c}\big(e^{c\,h(\mathbf x)}-1\big)+\tfrac12D^{(2)}_{\mu\nu}\partial_\mu h\,\partial_\nu h\,e^{c\,h(\mathbf x)}\Big],\qquad c=i(q_0+q).$$
--   The curvature term is $\int d^2\mathbf x\,e^{i[(\mathbf k_0-\mathbf k)\cdot\mathbf x+(q+q_0)h]}\tfrac12D_{\mu\nu}\partial_\mu h\,\partial_\nu h$.
--   9. **Voronovich's ansatz (eqs. 26 to 29).** Here $\sqrt{qq_0}$ is the principal square root, $B^{11}=A^{(1)}/(2i\sqrt{qq_0})$ and $B_2^{11}(\mathbf k,\mathbf k_0;\mathbf k_1)=\tilde G^{(2)}(\mathbf k-\mathbf k_1,\mathbf k_1-\mathbf k_0)/(2\sqrt{qq_0})$, with $\tilde G^{(2)}$ truncated at second order. Then $M^{11}(\mathbf k_1)=B_2^{11}(\mathbf k-\mathbf k_1)+B_2^{11}(\mathbf k_0+\mathbf k_1)+2(q+q_0)B^{11}$. The second term of (26) is
--   $$\frac{2\sqrt{qq_0}}{q+q_0}\int d^2\mathbf x\,e^{i[(\mathbf k_0-\mathbf k)\cdot\mathbf x+(q+q_0)h]}\Big(-\frac i4\Big)\int d^2\mathbf k_1\,M^{11}(\mathbf k_1)\tilde h_V(\mathbf k_1)e^{i\mathbf k_1\cdot\mathbf x}.$$
--
--   **Formalization Note** The paper defines the reduced kernels only on $\mathcal P^{(n)}$. In Lean they are total functions on $(\mathbb R^2)^n$, and every statement says explicitly where an identity is assumed to hold. The paper does not state its Fourier normalization. The one used here is the normalization under which eqs. (8) and (20) agree, and Voronovich's normalization is used in eq. (26), which is the one under which the paper's eq. (32) holds. The scattering amplitude contains the distribution $(2\pi)^2\delta^{(2)}(\mathbf k-\mathbf k_0)$, so its regular part and the coefficient of the delta function are stated separately.
-- source:
--   G. Bimonte, Wave-scattering from a gently curved surface, arXiv:1606.07694v1 (2016), Section "Perturbative expansion of the SA" (eqs. (6)-(8), (14)-(15)), Section "Resummation of the perturbative series" (eqs. (16)-(20), (25)), Section "Comparison with Voronovich's small-slope approximation" (eqs. (26)-(29)), PDF pp. 2-4

import Mathlib

/-!
G. Bimonte, *Wave-scattering from a gently curved surface*, arXiv:1606.07694v1 (2016): the reduced
perturbative kernels of the scattering amplitude and their momentum hyperplanes (eqs. (6), (8)), the
vertical-shift factor of eqs. (14)-(15), the second-order Taylor forms (16) and (19) with the added
terms (17)-(18), the Fourier transform of the height profile, the terms of the perturbative series
with truncated kernels (eq. (20)), the resummed amplitude (eq. (25)), and Voronovich's small-slope
ansatz with the kernel dictionary (eqs. (26)-(29)).
-/

open MeasureTheory Complex

noncomputable section

namespace Arxiv1606_07694

/-- Section "Perturbative expansion of the SA": the reference plane of in-plane positions
`x = (x, y)` and in-plane momenta `k`. For `κ : Vec2`, `κ μ` is the component `κ^μ`; the indices
`μ = 0, 1` stand for the paper's `μ = 1, 2`. -/
abbrev Vec2 : Type := EuclideanSpace ℝ (Fin 2)

/-- Eqs. (6), (8): a family of reduced perturbative kernels `G~^(n)(k_1, …, k_n; k, k_0)`, written
`G n k k0 κ` with `κ = (k_1, …, k_n)`; polarization indices are suppressed, as after eq. (16). The
paper defines `G~^(n)` only on the hyperplane `P^(n)`; values off `P^(n)` are an extension. -/
abbrev KernelFamily : Type := (n : ℕ) → Vec2 → Vec2 → (Fin n → Vec2) → ℂ

/-- Eq. (6): the reduced kernels are symmetric functions of the momenta `k_1, …, k_n`. -/
def IsSymmetricKernel (G : KernelFamily) : Prop :=
  ∀ (n : ℕ) (k k0 : Vec2) (κ : Fin n → Vec2) (σ : Equiv.Perm (Fin n)),
    G n k k0 (κ ∘ σ) = G n k k0 κ

/-- Eq. (6): `κ = (k_1, …, k_n)` lies on the hyperplane `P^(n) = {k_1 + … + k_n + k_0 - k = 0}`. -/
def OnHyperplane (k k0 : Vec2) {n : ℕ} (κ : Fin n → Vec2) : Prop :=
  ∑ i, κ i + k0 - k = 0

/-- Eqs. (14)-(15): the factor `i (q_0 + q)`, where `q_0 = qv k0` and `q = qv k` are the vertical
wavenumbers of the incident wave (in-plane wave vector `k_0`) and of the scattered wave (in-plane
wave vector `k`). -/
def shiftFactor (qv : Vec2 → ℂ) (k k0 : Vec2) : ℂ := I * (qv k0 + qv k)

/-- Eqs. (16), (19): the bilinear sum `∑_{i<j} D_{μν} k_i^μ k_j^ν` (summed over `μ, ν`). -/
def crossSum (Dm : Matrix (Fin 2) (Fin 2) ℂ) {n : ℕ} (κ : Fin n → Vec2) : ℂ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, ∑ μ, ∑ ν, Dm μ ν * (κ i μ : ℂ) * (κ j ν : ℂ)

/-- Eq. (19) without its remainder: the polynomial `A - D_{μν} ∑_{i<j} k_i^μ k_j^ν`. -/
def truncPoly (a : ℂ) (Dm : Matrix (Fin 2) (Fin 2) ℂ) {n : ℕ} (κ : Fin n → Vec2) : ℂ :=
  a - crossSum Dm κ

/-- Eq. (20): the kernel `G~^(n)` replaced by its second-order form (19),
`A^(n)(k, k_0) - D^(n)_{μν}(k, k_0) ∑_{i<j} k_i^μ k_j^ν`, for coefficient families `A`, `D`. -/
def truncKernel (A : ℕ → Vec2 → Vec2 → ℂ) (D : ℕ → Vec2 → Vec2 → Matrix (Fin 2) (Fin 2) ℂ)
    (n : ℕ) (k k0 : Vec2) (κ : Fin n → Vec2) : ℂ :=
  truncPoly (A n k k0) (D n k k0) κ

/-- Eq. (16): `g(k_1, …, k_n) = A + B_μ (∑_i k_i)^μ + C_{μν} ∑_i k_i^μ k_i^ν
- D_{μν} ∑_{i<j} k_i^μ k_j^ν + o(k²)` as `(k_1, …, k_n) → 0`. -/
def HasSecondOrderExpansion {n : ℕ} (g : (Fin n → Vec2) → ℂ) (a : ℂ) (b : Fin 2 → ℂ)
    (C Dm : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Asymptotics.IsLittleO (nhds 0)
    (fun κ : Fin n → Vec2 => g κ - (a + ∑ μ, b μ * ∑ i, (κ i μ : ℂ) +
      ∑ μ, ∑ ν, C μ ν * ∑ i, (κ i μ : ℂ) * (κ i ν : ℂ) - crossSum Dm κ))
    (fun κ : Fin n → Vec2 => ‖κ‖ ^ 2)

/-- Eq. (19): `g(k_1, …, k_n) = A - D_{μν} ∑_{i<j} k_i^μ k_j^ν + o(k²)` as `(k_1, …, k_n) → 0`. -/
def HasReducedExpansion {n : ℕ} (g : (Fin n → Vec2) → ℂ) (a : ℂ)
    (Dm : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Asymptotics.IsLittleO (nhds 0) (fun κ : Fin n → Vec2 => g κ - truncPoly a Dm κ)
    (fun κ : Fin n → Vec2 => ‖κ‖ ^ 2)

/-- Eqs. (17)-(18): the function `f^(n) = (k_1 + … + k_n + k_0 - k)^μ g^(n)_μ` with
`g^(n)_μ = Â_μ + B̂_{μν} (k_1 + … + k_n)^ν`, which vanishes on `P^(n)`. -/
def gaugeTerm (k k0 : Vec2) (Ahat : Fin 2 → ℂ) (Bhat : Matrix (Fin 2) (Fin 2) ℂ) {n : ℕ}
    (κ : Fin n → Vec2) : ℂ :=
  ∑ μ, ((∑ i, κ i + k0 - k) μ : ℂ) * (Ahat μ + ∑ ν, Bhat μ ν * ((∑ i, κ i) ν : ℂ))

/-- Eqs. (5), (8), (20): the Fourier transform `h~(k) = ∫ d²x h(x) e^{-i k·x}` of the height profile,
the normalization under which `h(x) = ∫ d²k/(2π)² h~(k) e^{i k·x}` (the paper does not state it). -/
def heightFT (h : SchwartzMap Vec2 ℝ) (k : Vec2) : ℂ :=
  ∫ x : Vec2, Complex.exp (-(I * (inner ℝ k x : ℂ))) * (h x : ℂ)

/-- Eqs. (20), (25): the partial derivative `∂_μ h(x)` of the height profile. -/
def heightPartial (h : SchwartzMap Vec2 ℝ) (μ : Fin 2) (x : Vec2) : ℝ :=
  fderiv ℝ (h : Vec2 → ℝ) x (EuclideanSpace.single μ 1)

/-- Eq. (8): the term of order `n = m + 1` of the perturbative series with kernel `T`,
`(1/n!) ∫ ∏_i d²k_i/(2π)² h~(k_1)…h~(k_n) (2π)² δ²(k_1 + … + k_n + k_0 - k) T(k_1, …, k_n)`,
with the delta function integrated out by `k_n = k - k_0 - k_1 - … - k_{n-1}`. -/
def seriesTerm (h : SchwartzMap Vec2 ℝ) (k k0 : Vec2) (m : ℕ)
    (T : (Fin (m + 1) → Vec2) → ℂ) : ℂ :=
  (((m + 1).factorial : ℂ))⁻¹ * (((2 * Real.pi : ℝ) : ℂ) ^ (2 * m))⁻¹ *
    ∫ κ : Fin m → Vec2, (∏ i, heightFT h (κ i)) * heightFT h (k - k0 - ∑ i, κ i) *
      T (Fin.snoc (α := fun _ => Vec2) κ (k - k0 - ∑ i, κ i))

/-- Eq. (25), part without the delta function: `∫ d²x e^{i(k_0-k)·x} [ (A^(1)/(i(q_0+q)))
(e^{i(q+q_0)h(x)} - 1) + (1/2) D^(2)_{μν} ∂_μh ∂_νh e^{i(q+q_0)h(x)} ]`. The remaining part of
eq. (25), `(A^(1)/(i(q_0+q))) ∫ d²x e^{i(k_0-k)·x} = (2π)² δ²(k_0 - k) A^(1)(k_0,k_0)/(2 i q_0)`, is a
delta function. -/
def resummedRegular (A : ℕ → Vec2 → Vec2 → ℂ) (D : ℕ → Vec2 → Vec2 → Matrix (Fin 2) (Fin 2) ℂ)
    (qv : Vec2 → ℂ) (h : SchwartzMap Vec2 ℝ) (k k0 : Vec2) : ℂ :=
  ∫ x : Vec2, Complex.exp (I * (inner ℝ (k0 - k) x : ℂ)) *
    (A 1 k k0 / shiftFactor qv k k0 * (Complex.exp (shiftFactor qv k k0 * (h x : ℂ)) - 1) +
      (1 / 2) * (∑ μ, ∑ ν, D 2 k k0 μ ν * (heightPartial h μ x : ℂ) * (heightPartial h ν x : ℂ)) *
        Complex.exp (shiftFactor qv k k0 * (h x : ℂ)))

/-- Eq. (25), second term: `∫ d²x e^{i[(k_0-k)·x + (q+q_0)h(x)]} (1/2) D_{μν} ∂_μh(x) ∂_νh(x)`. -/
def curvatureTerm (Dm : Matrix (Fin 2) (Fin 2) ℂ) (qv : Vec2 → ℂ) (h : SchwartzMap Vec2 ℝ)
    (k k0 : Vec2) : ℂ :=
  ∫ x : Vec2, Complex.exp (I * (inner ℝ (k0 - k) x : ℂ)) *
    Complex.exp (shiftFactor qv k k0 * (h x : ℂ)) *
      ((1 / 2) * ∑ μ, ∑ ν, Dm μ ν * (heightPartial h μ x : ℂ) * (heightPartial h ν x : ℂ))

/-- Eqs. (26), (28), (29): `√(q q_0)`, taken as the principal complex square root. -/
def sqrtqq0 (qv : Vec2 → ℂ) (k k0 : Vec2) : ℂ := (qv k * qv k0) ^ (1 / 2 : ℂ)

/-- Eq. (28): Voronovich's first-order kernel, `B^11(k, k_0) = A^(1)(k, k_0) / (2 i √(q q_0))`. -/
def voronovichB11 (A : ℕ → Vec2 → Vec2 → ℂ) (qv : Vec2 → ℂ) (k k0 : Vec2) : ℂ :=
  A 1 k k0 / (2 * I * sqrtqq0 qv k k0)

/-- Eq. (29) with `n = 1`: Voronovich's second-order kernel,
`B_2^11(k, k_0; k_1) = G~^(2)(k - k_1, k_1 - k_0; k, k_0) / (2! √(q q_0))`, with `G~^(2)` in its
second-order form (19). -/
def voronovichB2 (A : ℕ → Vec2 → Vec2 → ℂ) (D : ℕ → Vec2 → Vec2 → Matrix (Fin 2) (Fin 2) ℂ)
    (qv : Vec2 → ℂ) (k k0 k1 : Vec2) : ℂ :=
  truncKernel A D 2 k k0 ![k - k1, k1 - k0] / (2 * sqrtqq0 qv k k0)

/-- Eq. (27): `M^11(k, k_0; k_1) = B_2^11(k, k_0; k - k_1) + B_2^11(k, k_0; k_0 + k_1)
+ 2 (q + q_0) B^11(k, k_0)`. -/
def voronovichM (A : ℕ → Vec2 → Vec2 → ℂ) (D : ℕ → Vec2 → Vec2 → Matrix (Fin 2) (Fin 2) ℂ)
    (qv : Vec2 → ℂ) (k k0 k1 : Vec2) : ℂ :=
  voronovichB2 A D qv k k0 (k - k1) + voronovichB2 A D qv k k0 (k0 + k1) +
    2 * (qv k + qv k0) * voronovichB11 A qv k k0

/-- Eqs. (26), (32): the Fourier transform in Voronovich's normalization,
`h~(k) = (2π)^{-2} ∫ d²x h(x) e^{-i k·x}`, under which `h(x) = ∫ d²k h~(k) e^{i k·x}`. -/
def heightFTV (h : SchwartzMap Vec2 ℝ) (k : Vec2) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) ^ 2)⁻¹ * heightFT h k

/-- Eq. (26), second term: `(2√(q q_0)/(q+q_0)) ∫ d²x e^{i[(k_0-k)·x + (q+q_0)h(x)]}
(-(i/4)) ∫ d²k_1 M^11(k, k_0; k_1) h~(k_1) e^{i k_1·x}`. -/
def ssaSecondTerm (A : ℕ → Vec2 → Vec2 → ℂ) (D : ℕ → Vec2 → Vec2 → Matrix (Fin 2) (Fin 2) ℂ)
    (qv : Vec2 → ℂ) (h : SchwartzMap Vec2 ℝ) (k k0 : Vec2) : ℂ :=
  2 * sqrtqq0 qv k k0 / (qv k + qv k0) *
    ∫ x : Vec2, Complex.exp (I * (inner ℝ (k0 - k) x : ℂ)) *
      Complex.exp (shiftFactor qv k k0 * (h x : ℂ)) *
        (-(I / 4) * ∫ k1 : Vec2, voronovichM A D qv k k0 k1 * heightFTV h k1 *
          Complex.exp (I * (inner ℝ k1 x : ℂ)))

end Arxiv1606_07694


