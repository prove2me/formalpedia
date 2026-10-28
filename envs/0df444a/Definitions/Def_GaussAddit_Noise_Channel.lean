-- Prove2me | Definitions.Def_GaussAddit_Noise_Channel
-- name    : GaussAddit_Noise_Channel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:54.97598+00:00
-- url     : https://prove2.me/theorems/83936a1f-b69b-4020-b55c-7de6f332f7f3
-- title:
--   m-mode displacement kernel, circular Gaussian noise P_n (Dirac at n = 0), the m-use channel N_n^{⊗m} of (14), Schatten z-norm, ν_z of (2), and the replica form Θ of (21) (pp. 1–3)
-- statement:
--   This file sets up the classical-noise (random displacement) bosonic channel of Giovannetti and Lloyd and every object its maximal output norms are stated with.
--
--   **Fock space of $m$ uses.** The $m$ uses of the channel are $m$ bosonic modes. Their Hilbert space $\mathcal H^{\otimes m}$ is identified with $\ell^2(\mathbb N^m)$: the basis vector $|u\rangle$, $u=(u_1,\dots,u_m)\in\mathbb N^m$, is the Fock state with $u_r$ photons in mode $r$. An operator is described by its coefficient array $X_{uv}=\langle u|X|v\rangle$. Density operators are the positive trace-class operators of trace one (from the referenced definition module).
--
--   **Displacements.** For $\mu\in\mathbb C$ the single-mode displacement is $D(\mu)=\exp(\mu a^\dagger-\mu^*a)$ with Fock coefficients $\langle p|D(\mu)|q\rangle$; for $\vec\mu=(\mu_1,\dots,\mu_m)\in\mathbb C^m$ the multi-mode displacement $D(\vec\mu)=\exp(\vec\mu\cdot\vec a^\dagger-\vec a\cdot\vec\mu^\dagger)=D_1(\mu_1)\cdots D_m(\mu_m)$ has coefficients
--   $$\langle u|D(\vec\mu)|v\rangle=\prod_{r=1}^m\langle u_r|D(\mu_r)|v_r\rangle .$$
--
--   **Noise law.** For $n>0$, $P_n(\mu)\,d^2\mu$ with $P_n(\mu)=e^{-|\mu|^2/n}/(\pi n)$ and $d^2\mu=d\,\mathrm{Re}\,\mu\;d\,\mathrm{Im}\,\mu$ is the law of a complex number whose real and imaginary parts are independent centred Gaussians of variance $n/2$ (eq. (7)). At $n=0$ it is the point mass at $0$. The law $P_n(\vec\mu)\,d^2\vec\mu$ of (15) is the product of $m$ copies.
--
--   **The channel** (eqs. (13)–(14)). For every coefficient array $X$ (entangled inputs included),
--   $$\langle u|\mathcal N_n^{\otimes m}(X)|v\rangle=\int d^2\vec\mu\,P_n(\vec\mu)\sum_{u',v'}\langle u|D(\vec\mu)|u'\rangle\,X_{u'v'}\,\langle v|D(\vec\mu)|v'\rangle^* .$$
--
--   **Norms** (eqs. (2)–(3)). For $z\ge1$ and an operator $A$, $\operatorname{Tr}|A|^z=\sum_u\langle u|(A^\dagger A)^{z/2}|u\rangle\in[0,\infty]$ and $\|A\|_z=(\operatorname{Tr}|A|^z)^{1/z}$. The maximal output $z$-norm of $m$ uses is
--   $$\nu_z(\mathcal N_n^{\otimes m})=\sup_{\rho}\|\mathcal N_n^{\otimes m}(\rho)\|_z ,$$
--   the supremum over **all** density operators $\rho$ of the $m$ modes.
--
--   **Coherent products, overlaps and $\Theta$.** $|\alpha_1\rangle_1\otimes\cdots\otimes|\alpha_m\rangle_m$ has coefficients $\prod_r e^{-|\alpha_r|^2/2}\alpha_r^{u_r}/\sqrt{u_r!}$. For a vector $\psi$, $\langle\psi|D^\dagger(\vec\mu)D(\vec\nu)|\psi\rangle$ is computed as $\sum_w\overline{\langle w|D(\vec\mu)|\psi\rangle}\,\langle w|D(\vec\nu)|\psi\rangle$. On the $k$-copy space $(\mathcal H^{\otimes m})^{\otimes k}=\ell^2((\mathbb N^m)^k)$ the operator $\Theta$ of (21) is represented by its quadratic form
--   $$\langle\phi|\Theta|\phi\rangle=\int d^2\vec\mu_1\cdots d^2\vec\mu_k\,P_n(\vec\mu_1)\cdots P_n(\vec\mu_k)\,\langle\phi|D_1^\dagger(\vec\mu_1)D_1(\vec\mu_2)\otimes\cdots\otimes D_k^\dagger(\vec\mu_k)D_k(\vec\mu_1)|\phi\rangle ,$$
--   with the copy index $s+1$ taken cyclically.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Fock coordinates are `Fin m → ℕ` and operators are `Matrix (Fin m → ℕ) (Fin m → ℕ) ℂ` (row = bra); the Hilbert space is `lp (fun _ => ℂ) 2`. The noise law is `gaussianReal 0 (n/2)` in each of Re μ and Im μ, mapped to ℂ; since `gaussianReal 0 0` is the Dirac mass, n = 0 is the identity channel (for n < 0, which no statement uses, the law is also the Dirac mass). An array is turned into the unique bounded operator with these Fock coefficients (the zero operator if there is none, which never happens for channel outputs of states), and $(A^\dagger A)^{z/2}$ is the continuous functional calculus `CFC.rpow`. All norms and suprema take values in $[0,\infty]$, so no supremum or trace has a junk real value.
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, pp. 1–3, eqs. (2), (3), (6), (7), (13)–(15), (17), (21); footnote [19]

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

namespace GaussAddit.Noise

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix coherentCoefficient)

/-- Occupation strings of `m` bosonic modes (one per channel use): the Fock basis of
`H^{⊗m}`, with `ℓ²(ℕ)^{⊗m} = ℓ²(ℕ^m)`. -/
abbrev Occ (m : ℕ) := Fin m → ℕ

/-- Coefficient arrays of operators on `m` modes: `X u v = ⟨u|X|v⟩` (row = bra, column = ket). -/
abbrev Arr (m : ℕ) := Matrix (Occ m) (Occ m) ℂ

/-- The Fock basis vector `|u⟩` of the `m`-mode space. -/
def basisVec {m : ℕ} (u : Occ m) : Hilbert (Occ m) := lp.single 2 u 1

/-- Fock coefficients `⟨u|D(μ⃗)|v⟩ = ∏_r ⟨u_r|D(μ_r)|v_r⟩` of the multi-mode displacement
`D(μ⃗) = exp(μ⃗·a⃗† − a⃗·μ⃗†)` of p. 3 (product of the single-mode `D(μ) = exp(μa† − μ*a)`). -/
def dispKernel {m : ℕ} (μ : Fin m → ℂ) : Arr m :=
  fun u v => ∏ r, displacementMatrix (μ r) (u r) (v r)

/-- The circularly symmetric law `P_n(μ) d²μ` of (7): `Re μ` and `Im μ` independent centred
Gaussians of variance `n/2`. At `n = 0` it is the Dirac mass at `0`. -/
def circGauss (n : ℝ) : Measure ℂ :=
  ((gaussianReal 0 (Real.toNNReal (n / 2))).prod (gaussianReal 0 (Real.toNNReal (n / 2)))).map
    Complex.measurableEquivRealProd.symm

/-- The law `P_n(μ⃗) d²μ⃗` of (15) on `ℂ^m`: `m` independent copies of `circGauss n`. -/
def noiseLaw (n : ℝ) (m : ℕ) : Measure (Fin m → ℂ) :=
  Measure.pi (fun _ => circGauss n)

/-- The `m`-use channel `N_n^{⊗m}` of (13)–(14) acting on an arbitrary coefficient array
(entangled inputs included):
`⟨u|N_n^{⊗m}(X)|v⟩ = ∫ P_n(μ⃗) Σ_{u',v'} ⟨u|D(μ⃗)|u'⟩ X_{u'v'} ⟨v|D(μ⃗)|v'⟩^* d²μ⃗`. -/
def channel (n : ℝ) (m : ℕ) (X : Arr m) : Arr m := fun u v =>
  ∫ μ, ∑' u', ∑' v', dispKernel μ u u' * X u' v' * star (dispKernel μ v v') ∂(noiseLaw n m)

open Classical in
/-- The bounded operator whose Fock coefficients are `X` (unique, since the `|u⟩` form a
Hilbert basis); the zero operator when no bounded operator has these coefficients. -/
def realize {m : ℕ} (X : Arr m) : Hilbert (Occ m) →L[ℂ] Hilbert (Occ m) :=
  if h : ∃ T : Hilbert (Occ m) →L[ℂ] Hilbert (Occ m),
      ∀ u v, ⟪basisVec u, T (basisVec v)⟫_ℂ = X u v then Classical.choose h else 0

/-- `|A|^z = (A†A)^{z/2}` by the continuous functional calculus, for the operator `A`
realizing `X`. -/
def absPow {m : ℕ} (z : ℝ) (X : Arr m) : Hilbert (Occ m) →L[ℂ] Hilbert (Occ m) := by
  letI : ContinuousFunctionalCalculus ℂ (Hilbert (Occ m) →L[ℂ] Hilbert (Occ m)) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (Hilbert (Occ m) →L[ℂ] Hilbert (Occ m)) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  exact CFC.rpow (star (realize X) * realize X) (z / 2)

/-- `Tr |A|^z = Σ_u ⟨u||A|^z|u⟩ ∈ [0, ∞]` (trace of a positive operator; `∞` when `A` is not
in the Schatten class). -/
def tracePow {m : ℕ} (z : ℝ) (X : Arr m) : ℝ≥0∞ :=
  ∑' u, ENNReal.ofReal (⟪basisVec u, absPow z X (basisVec u)⟫_ℂ).re

/-- The `z`-norm (3): `‖A‖_z = (Tr |A|^z)^{1/z}`, valued in `[0, ∞]`. -/
def zNorm {m : ℕ} (z : ℝ) (X : Arr m) : ℝ≥0∞ := tracePow z X ^ (1 / z)

/-- The maximal output `z`-norm (2) of `N_n^{⊗m}`: supremum over all density operators of the
`m` uses, entangled ones included. -/
def nu (z n : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ⨆ ρ : State (Occ m), zNorm z (channel n m ρ.coefficients)

/-- The coefficients of the coherent product state `|α_1⟩_1 ⊗ ⋯ ⊗ |α_m⟩_m⟨⋯|`. -/
def coherentArr {m : ℕ} (α : Fin m → ℂ) : Arr m := fun u v =>
  (∏ r, coherentCoefficient (α r) (u r)) * star (∏ r, coherentCoefficient (α r) (v r))

/-- `⟨ψ|D†(μ⃗)D(ν⃗)|ψ⟩ = Σ_w (⟨w|D(μ⃗)|ψ⟩)^* ⟨w|D(ν⃗)|ψ⟩`. -/
def overlap {m : ℕ} (ψ : Hilbert (Occ m)) (μ ν : Fin m → ℂ) : ℂ :=
  ∑' w, star (∑' u, dispKernel μ w u * ψ u) * ∑' v, dispKernel ν w v * ψ v

/-- The integrand of `⟨φ|Θ|φ⟩` for the operator `Θ` of (21) on the `k`-copy space
`(H^{⊗m})^{⊗k} = ℓ²((ℕ^m)^k)`, at the noise values `μ⃗_1, …, μ⃗_k`:
`Σ_{U,V} φ_U^* ∏_s ⟨U_s|D_s†(μ⃗_s) D_s(μ⃗_{s+1})|V_s⟩ φ_V`, with `s + 1` cyclic. -/
def thetaIntegrand {m k : ℕ} (φ : Hilbert (Fin k → Occ m)) (μ : Fin k → Fin m → ℂ) : ℂ :=
  ∑' U, star (φ U) * ∑' V,
    (∏ s, ∑' w, star (dispKernel (μ s) w (U s)) * dispKernel (μ (finRotate k s)) w (V s)) * φ V

/-- The quadratic form `⟨φ|Θ|φ⟩` of the operator `Θ` of (21):
`∫ P_n(μ⃗_1)⋯P_n(μ⃗_k) ⟨φ|D_1†(μ⃗_1)D_1(μ⃗_2) ⊗ ⋯ ⊗ D_k†(μ⃗_k)D_k(μ⃗_1)|φ⟩`. -/
def thetaForm (n : ℝ) (m k : ℕ) (φ : Hilbert (Fin k → Occ m)) : ℂ :=
  ∫ μ, thetaIntegrand φ μ ∂(Measure.pi fun _ : Fin k => noiseLaw n m)

end

end GaussAddit.Noise


