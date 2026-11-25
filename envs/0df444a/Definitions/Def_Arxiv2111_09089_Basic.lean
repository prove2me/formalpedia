-- Prove2me | Definitions.Def_Arxiv2111_09089_Basic
-- name    : Arxiv2111_09089_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T10:23:04.387121+00:00
-- url     : https://prove2.me/theorems/bd546bab-9f2c-5a0d-8803-ab25bb74e198
-- title:
--   Cayley spectral variable, Padé-Fourier approximant and parallel-plate spectral Green's function
-- statement:
--   Objects of Sections II and III-A-1 of Hadad (2021). Time dependence $e^{j\omega t}$; $j$ is the imaginary unit.
--
--   1. **Padé example (Section II-A).** The Taylor polynomial of $e^{-x^2}$ about $0$ is $f_T(x)=1-x^2+x^4/2-x^6/6$. The two Padé approximations are $f_{P1}(x)=\dfrac{1-x^2/3}{1+2x^2/3+x^4/6}$ and $f_{P2}(x)=\dfrac{1}{1+x^2+x^4/2}$.
--   2. **Tilted path (eq. 2).** For $\alpha>0$, the normalised transverse wavenumber on the tilted path is $\xi=(1+j\alpha)\mu$. The map is defined for complex $\mu$, so that it can be evaluated at $\mu=\pm j$.
--   3. **Cayley variable (eq. 3).** $\mu=-j\,\dfrac{1+\eta}{1-\eta}$.
--   4. **Annulus and Laurent coefficients (eq. 5).** $A_\delta=\{\eta:1-\delta<|\eta|<1+\delta\}$. The Laurent coefficients of $g$ on the unit circle are its Fourier coefficients there, $c_n=\dfrac1{2\pi}\displaystyle\int_0^{2\pi}g(e^{j\phi})e^{-jn\phi}\,d\phi$.
--   5. **Padé-Fourier rational function (eq. 6).** $P_L(\eta)=\sum_{l=-L}^{L}a_l\eta^l$, $Q_M(\eta)=\sum_{m=-M}^{M}b_m\eta^m$ and the approximant $P_L/Q_M$.
--   6. **Parallel-plate waveguide (eq. 9).** Two PEC plates are a distance $d$ apart, filled with relative permittivity $\epsilon_{r1}$; $k_0$ is the vacuum wavenumber and $Z_0=120\pi\,\Omega$. With $k_z=k_0\sqrt{\epsilon_{r1}-\xi^2}$ and $Z_{TM}=Z_0\sqrt{\epsilon_{r1}-\xi^2}/\epsilon_{r1}$,
--   $$g(\xi;z,z')=-\frac{Z_{TM}/2}{1-e^{-2jk_zd}}\big(e^{-jk_zz_1}-e^{-jk_zz_2}-e^{-jk_zz_3}+e^{-jk_zz_4}\big),$$
--   where $z_1=|z-z'|$, $z_2=z+z'$, $z_3=2d-(z+z')$ and $z_4=2d-|z-z'|$.
--
--   **Formalization Note** The paper does not define $k_z$, and it writes $\epsilon$ in $Z_{TM}$. Here $k_z=k_0\sqrt{\epsilon_{r1}-\xi^2}$, consistent with eq. (1) ($\xi=k_t/k_0$) and with the formula for $Z_{TM}$, and $\epsilon=\epsilon_{r1}$. The square root is the principal branch $w^{1/2}$. $g$ is an even function of $k_z$, so the choice of branch does not change it. A quotient whose denominator vanishes takes the value $0$ in Lean; no statement depends on that value.
-- source:
--   Y. Hadad, On the use of the Padé-Fourier approximation in fast evaluation of the Green's function of layered media, arXiv:2111.09089v1 (2021), Sections II-A, II-B (eq. (2)), II-C (eqs. (3), (5), (6)) and III-A-1 (eq. (9))

import Mathlib

/-!
Y. Hadad, *On the use of the Padé-Fourier approximation in fast evaluation of the Green's
function of layered media*, arXiv:2111.09089v1 (2021): the Padé example of Section II-A, the
tilted integration path of Section II-B (eq. (2)), the Cayley spectral variable, the Laurent
coefficients and the Padé-Fourier rational function of Section II-C (eqs. (3), (5), (6)), and the
spectral Green's function of the lossy parallel-plate waveguide of Section III-A-1 (eq. (9)).
-/

open Complex

noncomputable section

namespace Arxiv2111_09089

/-- Section II-A, p. 2: the Taylor polynomial `f_T(x) = 1 - x² + x⁴/2 - x⁶/6` of `e^{-x²}`
about `x₀ = 0`. -/
def gaussTaylor (x : ℝ) : ℝ := 1 - x ^ 2 + x ^ 4 / 2 - x ^ 6 / 6

/-- Section II-A, p. 2: the first Padé approximation of `e^{-x²}`,
`f_P1(x) = (1 - x²/3) / (1 + 2x²/3 + x⁴/6)`. -/
def padeP1 (x : ℝ) : ℝ := (1 - x ^ 2 / 3) / (1 + 2 * x ^ 2 / 3 + x ^ 4 / 6)

/-- Section II-A, p. 2: the second Padé approximation of `e^{-x²}`,
`f_P2(x) = 1 / (1 + x² + x⁴/2)`. -/
def padeP2 (x : ℝ) : ℝ := 1 / (1 + x ^ 2 + x ^ 4 / 2)

/-- Section II-B, eq. (2), p. 3: the tilted integration path `ξ = (1 + jα) μ`. The variable `μ`
is complex so that the map can be evaluated at the points `μ = ± j` of Section II-C. -/
def xiOfMu (α : ℝ) (μ : ℂ) : ℂ := (1 + α * I) * μ

/-- Section II-C, eq. (3), p. 3: the Cayley transform `μ = -j (1 + η) / (1 - η)`. -/
def cayley (η : ℂ) : ℂ := -I * (1 + η) / (1 - η)

/-- Section II-C, eq. (5), p. 3: the annulus `1 - δ < |η| < 1 + δ` around the unit circle. -/
def annulus (δ : ℝ) : Set ℂ := {η | 1 - δ < ‖η‖ ∧ ‖η‖ < 1 + δ}

/-- Section II-C, eq. (5) and the text after it, p. 3: the `n`-th Laurent coefficient `c_n` of
`g` on the unit circle, i.e. the `n`-th Fourier coefficient of `φ ↦ g(e^{jφ})` on `[0, 2π]`,
`c_n = (1/2π) ∫₀^{2π} g(e^{jφ}) e^{-jnφ} dφ`. -/
def laurentCoeff (g : ℂ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos (fun φ : ℝ => g (exp (φ * I))) n

/-- Section II-C, eq. (6), p. 3: the Laurent polynomial `∑_{l=-L}^{L} a_l η^l`. -/
def laurentPoly (a : ℤ → ℂ) (L : ℕ) (η : ℂ) : ℂ :=
  ∑ l ∈ Finset.Icc (-(L : ℤ)) L, a l * η ^ l

/-- Section II-C, eq. (6), p. 3: the Padé-Fourier rational function
`P_L(η) / Q_M(η) = (∑_{l=-L}^{L} a_l η^l) / (∑_{m=-M}^{M} b_m η^m)`. -/
def padeFourier (a b : ℤ → ℂ) (L M : ℕ) (η : ℂ) : ℂ :=
  laurentPoly a L η / laurentPoly b M η

/-- Section III-A-1, p. 4: the free-space impedance `Z₀ = 120π Ω`. -/
def freeSpaceImpedance : ℝ := 120 * Real.pi

/-- Section III-A-1, eq. (9), p. 4: the longitudinal wavenumber `k_z = k₀ √(ε_{r1} - ξ²)` in the
filling of relative permittivity `ε_{r1}`, with `ξ` normalised by the vacuum wavenumber `k₀`
(eq. (1)). The paper uses `k_z` without defining it. -/
def ppwKz (k0 : ℝ) (ε ξ : ℂ) : ℂ := k0 * (ε - ξ ^ 2) ^ (1 / 2 : ℂ)

/-- Section III-A-1, p. 4: the TM wave impedance `Z_TM = Z₀ √(ε_{r1} - ξ²) / ε_{r1}` (the paper
writes `ε` in the denominator; it is the filling's `ε_{r1}`). -/
def ppwZTM (ε ξ : ℂ) : ℂ := freeSpaceImpedance * (ε - ξ ^ 2) ^ (1 / 2 : ℂ) / ε

/-- Section III-A-1, eq. (9), p. 4: the 1D spectral Green's function of the `x`-component of the
TM field of an `x`-polarised dipole in a parallel-plate waveguide of PEC plates at distance `d`
filled with relative permittivity `ε_{r1}`, source at `z'`, observer at `z`:
`g = -(Z_TM/2) / (1 - e^{-2j k_z d}) (e^{-j k_z z₁} - e^{-j k_z z₂} - e^{-j k_z z₃} + e^{-j k_z z₄})`,
with `z₁ = |z - z'|`, `z₂ = z + z'`, `z₃ = 2d - (z + z')`, `z₄ = 2d - |z - z'|`. -/
def ppwGreen (k0 d : ℝ) (ε : ℂ) (z z' : ℝ) (ξ : ℂ) : ℂ :=
  let kz := ppwKz k0 ε ξ;
  -(ppwZTM ε ξ / 2) / (1 - exp (-2 * I * kz * d)) *
    (exp (-I * kz * abs (z - z')) - exp (-I * kz * (z + z')) -
      exp (-I * kz * (2 * d - (z + z'))) + exp (-I * kz * (2 * d - abs (z - z'))))

end Arxiv2111_09089


