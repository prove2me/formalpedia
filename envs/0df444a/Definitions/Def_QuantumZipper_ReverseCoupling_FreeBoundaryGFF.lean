-- Prove2me | Definitions.Def_QuantumZipper_ReverseCoupling_FreeBoundaryGFF
-- name    : QuantumZipper_ReverseCoupling_FreeBoundaryGFF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:15:57.557132+00:00
-- url     : https://prove2.me/theorems/b82db045-2ac0-4771-a15a-101e15c87539
-- title:
--   §3.1–3.3, (3.6), pp. 37–42 — test functions on ℍ, the free boundary Green's function G^{ℍ_F}, the energy E(ρ₁,ρ₂), and the free boundary GFF as a random modulo-constant distribution
-- statement:
--   Let $\mathbb H=\{z\in\mathbb C:\operatorname{Im} z>0\}$ be the open upper half-plane and let $H_s(\mathbb H)$ be the space of smooth, compactly supported real functions whose support lies in $\mathbb H$. A test function $\rho\in H_s(\mathbb H)$ has **mean zero** if $\int_{\mathbb H}\rho(z)\,dz=0$ (Lebesgue measure on $\mathbb C$). For a function $F$ on $\mathbb H$ write $(F,\rho)=\int_{\mathbb H}F(z)\rho(z)\,dz$.
--
--   **Green's function.** The free boundary Green's function of $\mathbb H$ is
--   $$G(y,z)=G^{\mathbb H_F}(y,z)=-\log|y-\bar z|-\log|y-z|,\qquad y,z\in\mathbb H .$$
--   There is no factor $1/(2\pi)$: the Dirichlet inner product is $(f_1,f_2)_\nabla=(2\pi)^{-1}\int\nabla f_1\cdot\nabla f_2$, and with this normalization the covariance of the field is exactly the double integral below.
--
--   **Energy.** For test functions $\rho_1,\rho_2$,
--   $$E(\rho_1,\rho_2)=\int_{\mathbb H}\int_{\mathbb H}\rho_1(y)\,G(y,z)\,\rho_2(z)\,dy\,dz ,$$
--   the covariance (3.6) of the free boundary Gaussian free field.
--
--   **Free boundary GFF.** A random modulo-additive-constant distribution $\tilde h$ on a probability space $(\Omega,\mathcal F,P)$, given by its pairings $\omega\mapsto(\tilde h,\rho)(\omega)$, is a **free boundary GFF on $\mathbb H$** if every mean-zero pairing is measurable and, for every $n$ and every family $\rho_1,\dots,\rho_n$ of mean-zero test functions, the vector $\big((\tilde h,\rho_1),\dots,(\tilde h,\rho_n)\big)$ is a centred Gaussian vector with covariance matrix $\big(E(\rho_i,\rho_j)\big)_{i,j=1}^n$. Nothing is said about test functions of nonzero mean: the field is defined only modulo additive constants.
--
--   These are the objects in which Theorem 1.2 is stated; Proposition 3.1 says that the one-dimensional laws already determine this field.
--
--   **Formalization Note** $H_s(\mathbb H)$ is Mathlib's `𝓓(ℍ, ℝ)` with $\mathbb C$ viewed as a real normed space. The field is a map `Ω → 𝓓(ℍ, ℝ) → ℝ`; samples are not required to be continuous or linear, only the finite-dimensional laws of mean-zero pairings are fixed (as `multivariateGaussian 0 (E(ρ_i,ρ_j))`). The energy is a Bochner integral over $\mathbb C\times\mathbb C$; for test functions supported in $\mathbb H$ the integrand is integrable (the logarithmic singularity is locally integrable in the plane), so it is a genuine integral. On the diagonal $y=z$ the Lean value of $G$ uses $\log 0=0$, a null set. Existence of the field is classical ([She07]).
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §3.1.1–3.1.2 (p. 37), §3.2 (pp. 39–41, (3.6)), §3.3 (pp. 41–42)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped Distributions ComplexConjugate

namespace QuantumZipper.ReverseCoupling

/-- The open upper half-plane `ℍ = {z : ℂ | 0 < Im z}`, as an open subset of `ℂ` (viewed as a real
normed space). Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §3.1.1, p. 37. -/
def Hplane : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | 0 < z.im}, isOpen_lt continuous_const Complex.continuous_im⟩

/-- `H_s(ℍ)`: smooth, compactly supported real test functions whose support lies in `ℍ`
(arXiv:1012.4797v2, §3.1.1–3.1.2, p. 37). This is Mathlib's `𝓓(ℍ, ℝ)`. -/
abbrev TestFn : Type := 𝓓(Hplane, ℝ)

/-- A test function `ρ` has mean zero: `∫_ℍ ρ(z) dz = 0` (Lebesgue measure on `ℂ`). Pairings of a
modulo-additive-constant distribution are only taken against such `ρ` (§3.1.2, p. 37). -/
def MeanZero (ρ : TestFn) : Prop :=
  ∫ z : ℂ, ρ z = 0

/-- The pairing `(F, ρ) = ∫_ℍ F(z) ρ(z) dz` of a function `F : ℂ → ℝ` with a test function
(§3.1.1, p. 37: "`(f₁, f₂) = ∫_D f₁(x) f₂(x) dx`"). -/
noncomputable def pairing (F : ℂ → ℝ) (ρ : TestFn) : ℝ :=
  ∫ z : ℂ, F z * ρ z

/-- The free boundary Green's function of `ℍ`,
`G^{ℍ_F}(y, z) = −log |y − z̄| − log |y − z|` ((3.6), p. 41; the reverse column of the table on p. 47
writes it as `−log |y − z| − log |y − z̄|`).

**Formalization Note** There is no factor `1/(2π)`: the Dirichlet inner product carries the factor
`(2π)⁻¹` (p. 6, p. 37), and with that normalization `Cov((h, ρ₁), (h, ρ₂)) = ∫∫ ρ₁ G ρ₂` exactly,
as in (3.6). On the diagonal `y = z` Lean's `Real.log 0 = 0` gives a junk value; the diagonal is a
Lebesgue-null subset of `ℂ × ℂ` and never enters an integral. -/
noncomputable def greenFree (y z : ℂ) : ℝ :=
  -Real.log ‖y - z‖ - Real.log ‖y - conj z‖

/-- The free boundary energy (covariance form) of (3.6), p. 41:
`E(ρ₁, ρ₂) = ∫_{ℍ×ℍ} ρ₁(y) G^{ℍ_F}(y, z) ρ₂(z) dy dz`.

**Formalization Note** The integral is a Bochner integral over `ℂ × ℂ` with the product Lebesgue
measure; for test functions supported in `ℍ` this is the integral over `ℍ × ℍ`. For compactly
supported bounded `ρ₁, ρ₂` with support in `ℍ` the integrand is integrable (the logarithmic
singularity on the diagonal is locally integrable in two dimensions, and `y − z̄ ≠ 0` on `ℍ × ℍ`), so
this is a genuine integral, not a junk `0`. -/
noncomputable def energy (ρ₁ ρ₂ : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, ρ₁ p.1 * greenFree p.1 p.2 * ρ₂ p.2

/-- The vector `((h, ρ_j))_j ∈ ℝⁿ` of pairings, as an element of `EuclideanSpace ℝ (Fin n)`. -/
def pairVec {n : ℕ} (v : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 v

/-- **Free boundary GFF on `ℍ`**, as a random modulo-additive-constant distribution
(arXiv:1012.4797v2, §3.2–3.3, pp. 39–42, covariance (3.6)).

A map `h : Ω → H_s(ℍ) → ℝ` (the value `h ω ρ` is the pairing `(h, ρ)` of the sample `ω`) is a free
boundary GFF under `P` if every mean-zero pairing is measurable and, for every finite family `ρ₁, …, ρₙ` of
mean-zero test functions, the random vector `((h, ρ₁), …, (h, ρₙ))` is a centred Gaussian vector with
covariance matrix `(E(ρ_i, ρ_j))_{i,j}` of (3.6).

**Formalization Note** Nothing is asserted about test functions with nonzero mean: that is what
"modulo additive constants" means (p. 37, p. 40). The sample `h ω` is not required to be continuous
or linear in `ρ`; only the finite-dimensional laws of the mean-zero pairings are fixed, which is the
data that Proposition 3.1 (p. 42) says determines the field. Existence: [She07] (or the Kolmogorov
extension theorem, since `(E(ρ_i, ρ_j))` is a covariance matrix on mean-zero test functions). -/
structure IsFreeBoundaryGFF {Ω : Type*} [MeasurableSpace Ω] (h : Ω → TestFn → ℝ)
    (P : Measure Ω) : Prop where
  measurable : ∀ ρ : TestFn, MeanZero ρ → Measurable fun ω => h ω ρ
  law : ∀ (n : ℕ) (ρ : Fin n → TestFn), (∀ j, MeanZero (ρ j)) →
    P.map (fun ω => pairVec fun j => h ω (ρ j)) =
      multivariateGaussian 0 (Matrix.of fun i j => energy (ρ i) (ρ j))

end QuantumZipper.ReverseCoupling


