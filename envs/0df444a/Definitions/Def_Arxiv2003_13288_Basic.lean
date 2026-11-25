-- Prove2me | Definitions.Def_Arxiv2003_13288_Basic
-- name    : Arxiv2003_13288_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T08:40:37.731094+00:00
-- url     : https://prove2.me/theorems/7667bdcc-9f64-4573-9596-0f5a30a6e98b
-- title:
--   Dipolar self-energies, Green's-function components and scattering vertices in disordered media
-- statement:
--   Objects of Sections 2.3, 3.2, 3.4.2 and 4.2 of Wang and Zhao (2020), for electromagnetic waves of background wavenumber $k>0$ in a random medium of particles with number density $n_0>0$.
--
--   1. **Scattering mean free path.** For monodisperse randomly placed scatterers with scattering cross section $C_s$, $l_s=1/(n_0C_s)$.
--   2. **Effective permittivity and wavenumber (Sec. 3.2.1).** A self-energy $\Sigma$ determines $\varepsilon_{\mathrm{eff}}=1-\Sigma/k^2$ (eq. 35). The effective transverse wavenumber is $K^\perp=\sqrt{\varepsilon^\perp}\,k$, with the principal complex square root.
--   3. **Dipoles.** A point electric dipole of polarizability $\alpha$ has T-operator $t_0=-k^2\alpha$ (eq. 39). The Lorenz-Lorentz self-energy is $\Sigma_{\mathrm{LLR}}=n_0t_0/(1+n_0t_0/(3k^2))$ (eq. 65). A sphere of radius $a$ and permittivity $\varepsilon_p$ has electrostatic polarizability $\alpha_{\mathrm{ES}}=4\pi a^3(\varepsilon_p-1)/(\varepsilon_p+2)$ and volume fraction $f_v=\tfrac43\pi a^3n_0$.
--   4. **Green's function (eqs. 73-74).** $G_0^\perp(r)=-\big(\tfrac{i}{kr}-\tfrac{1}{(kr)^2}+1\big)\tfrac{e^{ikr}}{4\pi r}$ and $G_0^\parallel(r)=2\big(\tfrac{i}{kr}-\tfrac{1}{(kr)^2}\big)\tfrac{e^{ikr}}{4\pi r}$. The regular part of the dyadic Green's function is $\mathrm{PV}\,\mathbf G_0(\mathbf r)=G_0^\perp(r)(\mathbf I-\hat{\mathbf r}\hat{\mathbf r})+G_0^\parallel(r)\hat{\mathbf r}\hat{\mathbf r}$ for $\mathbf r\ne0$. The spherical Bessel functions are $j_0(x)=\sin x/x$ and $j_1(x)=\sin x/x^2-\cos x/x$.
--   5. **Pair correlations.** $h_2=g_2-1$ is the pair correlation function of a statistically homogeneous and isotropic medium, a function of the distance $r$. Its three-dimensional Fourier transform is $H_2(\mathbf q)=\int d^3\mathbf r\,h_2(r)e^{-i\mathbf q\cdot\mathbf r}$ (eq. 78). The correlation integral is $\int_0^\infty dr\,r\,e^{ikr}h_2(r)$.
--   6. **Principal-value integrals.** $\int d^3\mathbf r\,\mathrm{PV}\,\mathbf G_0(\mathbf r)h_2(r)$ (eq. 79) is the limit as $\epsilon\to0^+$ of the integral over $|\mathbf r|>\epsilon$, taken entry by entry. The Keller correlation integral of eq. (71) is $\int_{|\mathbf r|>\epsilon}d^3\mathbf r\,\mathbf e\cdot\mathrm{PV}\,\mathbf G_0(\mathbf r)\cdot\mathbf e\;h_2(r)\,e^{iK\hat{\mathbf u}\cdot\mathbf r}$, the transverse component along a unit vector $\mathbf e\perp\hat{\mathbf u}$ at momentum $\mathbf p=K\hat{\mathbf u}$.
--   7. **QCA self-energy (eq. 80).** $\Sigma_{\mathrm{QCA}}=n_0t_0\big/\big(1+\tfrac{n_0t_0}{3k^2}+\tfrac23n_0t_0\int_0^\infty dr\,r\,e^{ikr}[g_2(r)-1]\big)$.
--   8. **Differential scattering coefficient (eqs. 41-42).** For an on-shell irreducible vertex $\Gamma(K\hat{\mathbf p},K\hat{\mathbf p}')=\gamma(\hat{\mathbf p},\hat{\mathbf p}')\,\mathbf I\otimes\mathbf I$, the scattering direction at polar angle $\theta$ and azimuth $\varphi$ about $\hat{\mathbf p}'=\hat{\mathbf u}$ is $\hat{\mathbf p}=\cos\theta\,\hat{\mathbf u}+\sin\theta(\cos\varphi\,\mathbf e_1+\sin\varphi\,\mathbf e_2)$ in an orthonormal frame $(\hat{\mathbf u},\mathbf e_1,\mathbf e_2)$, and
--   $$\frac{d\kappa_s}{d\theta_s}=\int_0^{2\pi}\frac{1}{(2\pi)^2}\,\gamma(\hat{\mathbf p},\hat{\mathbf p}')\,\tfrac12\operatorname{tr}\big[(\mathbf I-\hat{\mathbf p}\hat{\mathbf p})(\mathbf I-\hat{\mathbf p}'\hat{\mathbf p}')\big]\,d\varphi.$$
--   The ISA vertex of point dipoles has $\gamma=n_0|t_0|^2$ (eq. 44), and the on-shell QCA vertex has $\gamma=n_0|C|^2+n_0^2|C|^2H_2(K\hat{\mathbf p}-K\hat{\mathbf p}')$ (eq. 83).
--   9. **Ohm's law (eqs. 58-59).** A nonabsorbing diffusive slab of thickness $L$ has total transmittance $T=(l_{\mathrm{tr}}+z_e)/(L+2z_e)$ with extrapolation length $z_e=\tfrac23\bar R\,l_{\mathrm{tr}}$.
--
--   **Formalization Note** The scalar $\tfrac12\operatorname{tr}[(\mathbf I-\hat{\mathbf p}\hat{\mathbf p})(\mathbf I-\hat{\mathbf p}'\hat{\mathbf p}')]$ is the transverse part of $\mathbf I\otimes\mathbf I$ (eq. 41) for unpolarized light: the average over the two incident polarizations of the sum over the scattered ones. The paper does not write this contraction out; it is the reading under which eq. (45) follows from eq. (42). The Green's-function components are those printed in eqs. (73)-(74). They are the negatives of the components of the real-space Green's function printed in eq. (53).
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), Secs. 2.3, 3.2.1, 3.2.2, 3.4.2, 4.2.2-4.2.4 (eqs. 35, 39, 41-44, 58-59, 65-68, 71-74, 78-80, 83)

import Mathlib

/-!
B. X. Wang and C. Y. Zhao, *The dependent scattering effect on radiative properties of
micro/nanoscale discrete disordered media*, arXiv:2003.13288v1 (2020): the scattering mean free
path and order-of-magnitude criteria of Sections 2.3 and 3, the effective permittivity and
wavenumber of Section 3.2.1, the transverse irreducible vertex of Section 3.2.2, and the dipolar
self-energies, Green's-function components, pair-correlation integrals and vertices of
Sections 4.2.2-4.2.4, and Ohm's law of Section 3.4.2.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2003_13288

/-- Real three-dimensional space, used for positions `r` and momentum directions `p̂`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Sec. 2.3, footnote 5 (PDF p. 14): the scattering mean free path `l_s = 1/(n₀ C_s)` of
monodisperse, randomly distributed scatterers with number density `n₀` and scattering cross
section `C_s`. -/
def scatMeanFreePath (n0 Cs : ℝ) : ℝ := 1 / (n0 * Cs)

/-- Eq. (35) (Sec. 3.2.1, PDF p. 27): the effective permittivity `ε_eff = 1 - Σ/k²` determined
by a (scalar, or transverse) self-energy `Σ` at background wavenumber `k`. -/
def effPermittivity (k : ℝ) (Sig : ℂ) : ℂ := 1 - Sig / (k : ℂ) ^ 2

/-- Sec. 3.2.1, after eq. (36) (PDF p. 27): the effective transverse wavenumber
`K^⊥ = √(ε^⊥) k`, with the principal complex square root. -/
def effWavenumber (k : ℝ) (eps : ℂ) : ℂ := eps ^ (1 / 2 : ℂ) * (k : ℂ)

/-- Eq. (39) (Sec. 3.2.1, PDF p. 28): the T-operator `t₀ = -k² α` of a single electric dipole of
polarizability `α`. -/
def dipoleT (k : ℝ) (alpha : ℂ) : ℂ := -(k : ℂ) ^ 2 * alpha

/-- Eq. (65) (Sec. 4.2.2, PDF p. 50): the Lorenz-Lorentz self-energy
`Σ_LLR = n₀ t₀ / (1 + n₀ t₀/(3k²))`. -/
def llrSelfEnergy (n0 k : ℝ) (t0 : ℂ) : ℂ := n0 * t0 / (1 + n0 * t0 / (3 * (k : ℂ) ^ 2))

/-- Sec. 4.2.2, before eq. (68) (PDF p. 51): the electrostatic polarizability
`α_ES = 4π a³ (ε_p - 1)/(ε_p + 2)` of a sphere of radius `a` and permittivity `ε_p`. -/
def alphaES (a : ℝ) (epsP : ℂ) : ℂ := 4 * Real.pi * a ^ 3 * (epsP - 1) / (epsP + 2)

/-- Eq. (68) (Sec. 4.2.2, PDF p. 51): the volume fraction `f_v = n₀ (4/3) π a³`. -/
def volFraction (n0 a : ℝ) : ℝ := n0 * (4 / 3) * Real.pi * a ^ 3

/-- Eq. (72) (Sec. 4.2.3, PDF p. 52): the spherical Bessel function `j₀(x) = sin x / x`. -/
def sphJ0 (x : ℝ) : ℝ := Real.sin x / x

/-- Eq. (72) (Sec. 4.2.3, PDF p. 52): the spherical Bessel function
`j₁(x) = sin x / x² - cos x / x`. -/
def sphJ1 (x : ℝ) : ℝ := Real.sin x / x ^ 2 - Real.cos x / x

/-- Eq. (73) (Sec. 4.2.3, PDF p. 52): the transverse component of the Green's function,
`G₀^⊥(r) = -(i/(kr) - 1/(kr)² + 1) e^{ikr}/(4π r)`. -/
def greenPerp (k r : ℝ) : ℂ :=
  -(Complex.I / ((k * r : ℝ) : ℂ) - 1 / ((k * r : ℝ) : ℂ) ^ 2 + 1) *
    Complex.exp (Complex.I * ((k * r : ℝ) : ℂ)) / (4 * Real.pi * r)

/-- Eq. (74) (Sec. 4.2.3, PDF p. 52): the longitudinal component of the Green's function,
`G₀^∥(r) = 2 (i/(kr) - 1/(kr)²) e^{ikr}/(4π r)`. -/
def greenPar (k r : ℝ) : ℂ :=
  2 * (Complex.I / ((k * r : ℝ) : ℂ) - 1 / ((k * r : ℝ) : ℂ) ^ 2) *
    Complex.exp (Complex.I * ((k * r : ℝ) : ℂ)) / (4 * Real.pi * r)

/-- The dyad `v vᵀ` of a vector `v ∈ ℝ³`, as a complex `3 × 3` matrix (`r̂ r̂`, `p̂ p̂` in the
paper). -/
def dyad (v : E3) : Matrix (Fin 3) (Fin 3) ℂ := fun i j => ((v i * v j : ℝ) : ℂ)

/-- Eqs. (73)-(74) (Sec. 4.2.3, PDF p. 52): the regular (principal-value) part of the dyadic
Green's function, `PV G₀(r) = G₀^⊥(r) (I - r̂ r̂) + G₀^∥(r) r̂ r̂` for `r ≠ 0`. -/
def greenReg (k : ℝ) (r : E3) : Matrix (Fin 3) (Fin 3) ℂ :=
  greenPerp k ‖r‖ • (1 - dyad (‖r‖⁻¹ • r)) + greenPar k ‖r‖ • dyad (‖r‖⁻¹ • r)

/-- The component `e · M · e` of a `3 × 3` matrix along a unit vector `e`; for `e ⊥ p̂` this is
the transverse component of a tensor `M = M^⊥ (I - p̂ p̂) + M^∥ p̂ p̂`. -/
def quadForm (M : Matrix (Fin 3) (Fin 3) ℂ) (e : E3) : ℂ :=
  ∑ i, ∑ j, (e i : ℂ) * M i j * (e j : ℂ)

/-- Eqs. (71)-(72) (Sec. 4.2.3, PDF p. 52): the transverse component, along `e ⊥ p̂ = u`, of the
correlation integral `∫ d³r G₀(r) h₂(r) e^{i p·r}` at `p = K u`, with the regular part of `G₀`
and the ball `|r| ≤ ε` removed. -/
def kellerTrunc (k K : ℝ) (h2 : ℝ → ℝ) (u e : E3) (ε : ℝ) : ℂ :=
  ∫ r in {r : E3 | ε < ‖r‖},
    quadForm (greenReg k r) e * (h2 ‖r‖ : ℂ) * Complex.exp (Complex.I * ((K * inner ℝ u r : ℝ) : ℂ))

/-- Eq. (79) (Sec. 4.2.4, PDF p. 54): the integral `∫ d³r PV G₀(r) h₂(r)` with the ball
`|r| ≤ ε` removed, entry by entry. -/
def pvTrunc (k : ℝ) (h2 : ℝ → ℝ) (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ∫ r in {r : E3 | ε < ‖r‖}, greenReg k r i j * (h2 ‖r‖ : ℂ)

/-- Eq. (79) (Sec. 4.2.4, PDF p. 54): the principal-value integral `∫ d³r PV G₀(r) h₂(r)`, the
limit of `pvTrunc k h2 ε` as `ε → 0⁺`. -/
def pvGreenIntegral (k : ℝ) (h2 : ℝ → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) (pvTrunc k h2)

/-- Eq. (80) (Sec. 4.2.4, PDF p. 55): the pair-correlation integral
`∫₀^∞ dr r e^{ikr} [g₂(r) - 1]`, written with `h₂ = g₂ - 1`. -/
def corrIntegral (k : ℝ) (h2 : ℝ → ℝ) : ℂ :=
  ∫ r in Set.Ioi (0 : ℝ), (r : ℂ) * Complex.exp (Complex.I * ((k * r : ℝ) : ℂ)) * (h2 r : ℂ)

/-- Eq. (80) (Sec. 4.2.4, PDF p. 55): the QCA self-energy of electric dipoles,
`Σ = n₀ t₀ / (1 + n₀ t₀/(3k²) + 2 n₀ t₀ ∫₀^∞ dr r e^{ikr} [g₂(r) - 1] / 3)`. -/
def qcaSelfEnergy (n0 k : ℝ) (t0 : ℂ) (h2 : ℝ → ℝ) : ℂ :=
  n0 * t0 / (1 + n0 * t0 / (3 * (k : ℂ) ^ 2) + 2 * n0 * t0 * corrIntegral k h2 / 3)

/-- Eq. (78) (Sec. 4.2.4, PDF p. 54): the Fourier transform of the pair correlation function,
`H₂(q) = ∫ d³r h₂(r) e^{-i q·r}`. -/
def pairCorrFT (h2 : ℝ → ℝ) (q : E3) : ℂ :=
  ∫ r : E3, (h2 ‖r‖ : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ q r : ℝ) : ℂ)))

/-- Sec. 3.2.2 (PDF p. 29): the scattering direction `p̂` at polar angle `θ` and azimuth `φ`
about the incident direction `p̂' = u`, in an orthonormal frame `(u, e₁, e₂)`. -/
def scatDir (u e1 e2 : E3) (θ φ : ℝ) : E3 :=
  Real.cos θ • u + Real.sin θ • (Real.cos φ • e1 + Real.sin φ • e2)

/-- Eq. (41) (Sec. 3.2.2, PDF p. 29): the transverse projector `I - p̂ p̂`. -/
def transProj (v : E3) : Matrix (Fin 3) (Fin 3) ℂ := 1 - dyad v

/-- Eq. (41) (Sec. 3.2.2, PDF p. 29): the transverse part `(I - p̂p̂) (I ⊗ I) (I - p̂'p̂')` of the
tensor `I ⊗ I`, contracted for unpolarized light, i.e. averaged over the two incident
polarizations and summed over the scattered ones: `½ tr[(I - p̂p̂)(I - p̂'p̂')]`. -/
def unpolTransverse (v w : E3) : ℂ := (1 / 2) * Matrix.trace (transProj v * transProj w)

/-- Eq. (42) and the sentence before eq. (45) (Sec. 3.2.2, PDF pp. 29-30): the differential
scattering coefficient with respect to the polar angle, `dκ_s/dθ_s`, of an irreducible vertex
`Γ(Kp̂, Kp̂') = γ(p̂, p̂') I ⊗ I`: the transverse unpolarized part of `Γ/(2π)²`, integrated over
the azimuth `φ_s ∈ [0, 2π]` with the incident direction `p̂' = u` fixed. -/
def diffScatPolar (γ : E3 → E3 → ℂ) (u e1 e2 : E3) (θ : ℝ) : ℂ :=
  ∫ φ in (0 : ℝ)..(2 * Real.pi),
    ((2 * Real.pi : ℂ) ^ 2)⁻¹ * γ (scatDir u e1 e2 θ φ) u * unpolTransverse (scatDir u e1 e2 θ φ) u

/-- Eq. (44) (Sec. 3.2.2, PDF p. 29): the scalar coefficient `n₀ |t₀|²` of the ISA irreducible
vertex `Γ = n₀ |t₀|² I ⊗ I` of point dipoles. -/
def isaDipoleVertex (n0 : ℝ) (t0 : ℂ) (_v _w : E3) : ℂ := ((n0 * ‖t0‖ ^ 2 : ℝ) : ℂ)

/-- Eq. (83) (Sec. 4.2.4, PDF p. 55): the scalar coefficient
`n₀ |C|² + n₀² |C|² H₂(K p̂ - K p̂')` of the on-shell QCA irreducible vertex. -/
def qcaVertex (n0 K : ℝ) (C : ℂ) (h2 : ℝ → ℝ) (v w : E3) : ℂ :=
  ((n0 * ‖C‖ ^ 2 : ℝ) : ℂ) + ((n0 ^ 2 * ‖C‖ ^ 2 : ℝ) : ℂ) * pairCorrFT h2 (K • v - K • w)

/-- Eq. (58) (Sec. 3.4.2, PDF p. 40): Ohm's law for the total transmittance of a nonabsorbing
diffusive slab of thickness `L`, `T = (l_tr + z_e)/(L + 2 z_e)`. -/
def ohmTransmittance (ltr ze L : ℝ) : ℝ := (ltr + ze) / (L + 2 * ze)

/-- Eq. (59) (Sec. 3.4.2, PDF p. 40): the extrapolation length `z_e = (2/3) R̄ l_tr`. -/
def extrapLength (Rbar ltr : ℝ) : ℝ := 2 / 3 * Rbar * ltr

end Arxiv2003_13288


