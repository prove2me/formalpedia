-- Prove2me | Definitions.Def_Arxiv2507_18491_Basic
-- name    : Arxiv2507_18491_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-26T12:58:28.896361+00:00
-- url     : https://prove2.me/theorems/6c7d89cf-bfac-422b-b068-5b024daa5e6c
-- title:
--   Layered media, reaction field components and M2L integrals of the Maxwell FMM in layered media
-- statement:
--   Objects of Sections 3.1-3.4 and Appendices A-B of Yuan, Wang, Zhang and Cai (2025).
--
--   1. **Layered medium (Section 3.1).** There are $L+1$ horizontal layers $0,\dots,L$ from top to bottom. The interface between layer $\ell$ and layer $\ell+1$ is the plane $z=d_\ell$, $0\le\ell\le L-1$, with $d_0>\dots>d_{L-1}$. Layer $\ell$ has permittivity $\varepsilon_\ell>0$, permeability $\mu_\ell>0$ and wave number $k_\ell=\omega\sqrt{\varepsilon_\ell\mu_\ell}$ (eq. 3.1). A height $z$ lies in layer $\ell$ if $d_\ell<z<d_{\ell-1}$; layer $0$ is unbounded above and layer $L$ is unbounded below. The vertical wave number is $k_{\ell z}=\sqrt{k_\ell^2-k_\rho^2}$ with $\operatorname{Im}k_{\ell z}\ge0$. For real $k_\rho$ this is $\sqrt{k_\ell^2-k_\rho^2}\ge0$ when $k_\rho\le k_\ell$, and $\mathrm i\sqrt{k_\rho^2-k_\ell^2}$ otherwise.
--   2. **Spectral Green's function (eq. 3.3).** For coefficient functions $\phi,\psi,\tilde\psi$ of $(z,z')$ in the target layer $\ell$,
--   $$\widehat{\boldsymbol G}_E=-\frac{\mathrm i\omega}{k_\ell^2}\Big(k_\ell^2\phi J_1+\mu_\ell k_\rho^2\psi J_2+\mu_\ell\partial_z\psi J_3+\mu_\ell\tilde\psi J_4+\frac{k_\ell^2\phi+\mu_\ell\partial_z\tilde\psi}{k_\rho^2}J_5\Big),$$
--   without the term $\boldsymbol\delta$, which is supported on $z=z'$. Here $J_1,\dots,J_5$ are the $3\times3$ matrices (3.5), and $(k_\rho,\alpha)$ are the polar coordinates of $(k_x,k_y)$.
--   3. **Reaction field exponentials (eqs. 3.9-3.11, 3.21-3.24).** $\tau_\ell(z)=2d_\ell-z$. For a component $(\ast,\star)\in\{\uparrow,\downarrow\}^2$ ($\ast$ is the direction of the wave arriving at the target, $\star$ the direction of the wave leaving the source), $Z^{\ast\star}_{\ell\ell'}(k_\rho,z,z')$ is the exponential (3.9) and $s^{\ast\star}_{\ell\ell'}=\pm1$ is the sign (3.11). The effective location $\hat\tau^{\ast\star}_{\ell\ell'}(\boldsymbol r)$ of a target and the equivalent polarization coordinate $\breve\tau^{\star}_{\ell\ell'}(\boldsymbol r')$ of a source (3.21)-(3.22) replace the height by its mirror image in an adjacent interface, or keep it. The vertical transmission distance is $|\hat z-\breve z|$, the vertical part of (3.24). A component is *defined* when every interface index that occurs in its case of (3.9) lies in $\{0,\dots,L-1\}$.
--   4. **Reaction parts (eq. 3.8).** For density functions $\phi^{\ast\star}_{\ell\ell'}(k_\rho)$ and $\psi^{\ast\star}_{\ell\ell'}(k_\rho)$, the reaction parts of $\phi_\ell$ and $\psi_\ell$ are $-\frac{1}{2\omega k_{\ell'z}}\sum_{\ast,\star}\phi^{\ast\star}_{\ell\ell'}Z^{\ast\star}_{\ell\ell'}$ and $-\frac{1}{2\omega\mu_{\ell'}k_{\ell'z}}\sum_{\ast,\star}\psi^{\ast\star}_{\ell\ell'}Z^{\ast\star}_{\ell\ell'}$.
--   5. **Reaction components (eqs. 3.13-3.14, 3.16-3.19).** $\Theta^{\ast\star}_{\ell\ell'}$ is the matrix (3.14), and $\widehat{\boldsymbol G}^{\ast\star}_{\ell\ell'}=\mathrm iZ^{\ast\star}_{\ell\ell'}\Theta^{\ast\star}_{\ell\ell'}/(2k_{\ell'z})$. $\boldsymbol G^{\ast\star}_{\ell\ell'}(\boldsymbol r,\boldsymbol r')$ is its inverse Fourier transform (3.18), computed entry by entry. $M_1,\dots,M_6$ are the constant matrices displayed after (3.15), and $\gamma_{\ell\ell'}=\mu_\ell/(\mu_{\ell'}k_\ell^2)$. $\sigma_1,\sigma_2,\sigma_4,\sigma_5$ are the densities (3.16)-(3.17). Both $\sigma_3$ as printed in (3.16) and the density $\sigma_3^{c}$ that (3.14) actually produces are defined: $\sigma_3^{c}=\phi/k_{\ell'z}+\gamma_{\ell\ell'}k_{\ell z}\psi$ for $\uparrow\downarrow,\downarrow\uparrow$ and $\phi/k_{\ell'z}-\gamma_{\ell\ell'}k_{\ell z}\psi$ for $\uparrow\uparrow,\downarrow\downarrow$. The operator (3.19) is
--   $$\mathcal L^{\ast\star}_{\ell\ell'\kappa}[\sigma](\boldsymbol r,\boldsymbol r')=\frac{\mathrm i}{8\pi^2}\iint_{\mathbb R^2}\mathcal E^{\ast\star}_{\ell\ell'}\big(\hat\tau(\boldsymbol r),\breve\tau(\boldsymbol r')\big)e^{\mathrm i\kappa\alpha}\sigma(k_\rho)\,dk_xdk_y,$$
--   where $\mathcal E(\boldsymbol r,\boldsymbol r')=e^{\mathrm ik_x(x-x')+\mathrm ik_y(y-y')}e^{s(\mathrm ik_{\ell z}z-\mathrm ik_{\ell'z}z')}$ (3.20).
--   6. **Integrals of Sections 3.3-3.4 (eqs. 3.28, 3.44-3.45).** These are
--   $$\mathcal I^{\nu\mu}_{nm\kappa}=\frac{c^{\nu\mu}_{nm}}{2\pi}\iint\mathcal E\,e^{\mathrm i(m-\mu+\kappa)\alpha}\widehat P_n^m(k_z/k)\widehat P_\nu^\mu(k'_z/k')\sigma(k_\rho)\,dk_xdk_y,\qquad c^{\nu\mu}_{nm}=s^{n+\nu+m+\mu}\mathrm i^{n+\nu+1},$$
--   and the Sommerfeld-type integral $\widehat{\mathcal I}^{\nu\mu}_{nm\kappa}=\int_0^\infty k_\rho J_{m-\mu+\kappa}(k_\rho\rho)\mathcal Z\,\widehat P_n^m\widehat P_\nu^\mu\sigma\,dk_\rho$. $J_n$ is the Bessel function, given by its integral representation $J_n(x)=\frac1{2\pi\mathrm i^n}\int_0^{2\pi}e^{\mathrm ix\cos\theta+\mathrm in\theta}d\theta$.
--   7. **Chebyshev expansions (Appendices A-B, eq. 3.49).** $T_n$ is the Chebyshev polynomial of the first kind. $C^{ab}_{js}$ are the coefficients given by the recurrence (A.2), with the initial value $C^{ab}_{11}=a$, which (A.2) uses but does not list. $\mathrm{sgn}(x)=(-1)^{\min(0,x)}$. $\tau_{nm}(\theta)$ and $K_n$ are the prefactor and number of terms of (B.1).
--   8. **FMM boxes (Section 3.4.1).** A box is a closed axis-parallel cube, given by its centre and side length.
--
--   **Formalization Note** The density functions $\phi^{\ast\star}_{\ell\ell'}$ and $\psi^{\ast\star}_{\ell\ell'}$ are arbitrary functions of $k_\rho$: the paper says only that they are computed from the layer structure by recurrences in other references. Likewise the normalized associated Legendre function $\widehat P_n^m$ is an arbitrary family `P n m`: the paper uses it in (3.28) without giving its normalization, and statements that need its symmetry $\widehat P_n^{-m}=(-1)^m\widehat P_n^m$ take that symmetry as a hypothesis. Points of $\mathbb R^3$ are triples $(x,y,z)$, and the factor $e^{\mathrm i\alpha}$ is $(k_x+\mathrm ik_y)/k_\rho$, which is set to $0$ on the null set $k_\rho=0$.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), Sections 3.1-3.4 (eqs. (3.1)-(3.24), (3.28), (3.44)-(3.45), (3.49)), Appendix A (eqs. (A.1)-(A.2)) and Appendix B (eq. (B.1))

import Mathlib

/-!
H. Yuan, B. Wang, W. Zhang and W. Cai, *Fast multipole method for Maxwell's equations in layered
media*, arXiv:2507.18491v1 (2025): the layered medium and vertical wave numbers (Section 3.1,
eqs. (3.1), (3.3)-(3.5)), the reaction-field decomposition and its exponentials, signs, equivalent
polarization coordinates and effective locations (eqs. (3.8)-(3.24)), the matrix basis and
densities of the reaction field components (eqs. (3.13)-(3.19)), the integrals of Sections 3.3-3.4
(eqs. (3.28), (3.44)-(3.45)), the Chebyshev coefficients of Appendix A (eqs. (A.1)-(A.2)) and the
factors of the Chebyshev expansion of the associated Legendre functions of Appendix B (eq. (B.1)).
-/

open MeasureTheory

noncomputable section

namespace Arxiv2507_18491

/-- Section 3.1: the vertical propagation directions `↑` (upward, `true`) and `↓` (downward,
`false`). A reaction field component is labelled by a pair `(∗, ⋆)`: `∗` is the direction of the
wave arriving at the target, `⋆` the direction of the wave leaving the source. -/
abbrev Dir := Bool

/-- Eq. (3.1): the wave number `k_ℓ = ω √(ε_ℓ μ_ℓ)` of layer `ℓ`. -/
def waveNum (omega : ℝ) (epsL muL : ℕ → ℝ) (l : ℕ) : ℝ := omega * Real.sqrt (epsL l * muL l)

/-- Section 3.1 (after eq. (3.7)): the vertical wave number `k_{ℓz} = √(k_ℓ² - k_ρ²)` with the
branch `Im k_{ℓz} ≥ 0`, for a real wave number `k = k_ℓ` and a real spectral variable `k_ρ`:
the nonnegative square root when `k_ρ² ≤ k²` and `i √(k_ρ² - k²)` otherwise. -/
def vkz (k krho : ℝ) : ℂ :=
  if krho ^ 2 ≤ k ^ 2 then ((Real.sqrt (k ^ 2 - krho ^ 2) : ℝ) : ℂ)
  else Complex.I * ((Real.sqrt (krho ^ 2 - k ^ 2) : ℝ) : ℂ)

/-- Section 3.1: the interfaces `z = d_ℓ`, `0 ≤ ℓ ≤ L - 1`, between layer `ℓ` and layer `ℓ + 1`
satisfy `d_0 > ⋯ > d_{L-1}` (only the values `d 0, …, d (L - 1)` are interfaces). -/
def IsInterfaces (L : ℕ) (d : ℕ → ℝ) : Prop := ∀ i j : ℕ, i < j → j < L → d j < d i

/-- Section 3.1 (eq. (3.3)): the height `z` lies strictly inside layer `ℓ ∈ {0, …, L}`, i.e.
`d_ℓ < z < d_{ℓ-1}`, where layer `0` is unbounded above and layer `L` is unbounded below. -/
def InLayer (L : ℕ) (d : ℕ → ℝ) (l : ℕ) (z : ℝ) : Prop :=
  l ≤ L ∧ (l = 0 ∨ z < d (l - 1)) ∧ (l = L ∨ d l < z)

/-- Eq. (3.10): the reflection `τ_ℓ(z) = 2 d_ℓ - z` in the interface `z = d_ℓ`. -/
def refl (d : ℕ → ℝ) (l : ℕ) (z : ℝ) : ℝ := 2 * d l - z

/-- Eq. (3.11): the sign `s^{∗⋆}_{ℓℓ'}`; it depends only on `⋆ = b`:
`s^{∗↓}_{ℓℓ'} = 1` for `ℓ ≤ ℓ'` and `-1` for `ℓ > ℓ'`; `s^{∗↑}_{ℓℓ'} = 1` for `ℓ < ℓ'` and `-1`
for `ℓ ≥ ℓ'`. -/
def sgnS (l l' : ℕ) (b : Dir) : ℝ :=
  if b then (if l < l' then 1 else -1) else (if l ≤ l' then 1 else -1)

/-- Eq. (3.9): the reaction field component `(∗, ⋆) = (a, b)` for target layer `ℓ` and source
layer `ℓ'` (both in `{0, …, L}`) is defined: every interface index occurring in its case of
(3.9) lies in `{0, …, L - 1}` (the reflections `τ_{ℓ-1}` and `τ_ℓ` need an interface above,
respectively below, the layer). -/
def CompDefined (L l l' : ℕ) (a b : Dir) : Prop :=
  match a, b with
  | true, true => l < l' ∨ (1 ≤ l' ∧ l + 1 ≤ L)
  | true, false => (l ≤ l' ∧ l' + 1 ≤ L) ∨ (l' < l ∧ l + 1 ≤ L)
  | false, true => (l < l' ∧ 1 ≤ l) ∨ (l' ≤ l ∧ 1 ≤ l')
  | false, false => (l ≤ l' ∧ 1 ≤ l ∧ l' + 1 ≤ L) ∨ l' < l

/-- Eq. (3.9): the exponentials `Z^{∗⋆}_{ℓℓ'}(k_ρ, z, z')` of the reaction field components,
`(∗, ⋆) = (a, b)`, for target height `z` in layer `ℓ` and source height `z'` in layer `ℓ'`;
`k j` is the wave number of layer `j`, and `k_{ℓz}`, `k_{ℓ'z}` are the vertical wave numbers. -/
def Zfun (k : ℕ → ℝ) (d : ℕ → ℝ) (l l' : ℕ) (a b : Dir) (krho z z' : ℝ) : ℂ :=
  let kz : ℂ := vkz (k l) krho
  let kz' : ℂ := vkz (k l') krho
  match a, b with
  | true, true =>
    if l < l' then Complex.exp (Complex.I * (kz * z - kz' * z'))
    else Complex.exp (Complex.I * (kz' * refl d (l' - 1) z' - kz * refl d l z))
  | true, false =>
    if l ≤ l' then Complex.exp (Complex.I * (kz * z - kz' * refl d l' z'))
    else Complex.exp (Complex.I * (kz' * z' - kz * refl d l z))
  | false, true =>
    if l < l' then Complex.exp (Complex.I * (kz * refl d (l - 1) z - kz' * z'))
    else Complex.exp (Complex.I * (kz' * refl d (l' - 1) z' - kz * z))
  | false, false =>
    if l ≤ l' then Complex.exp (Complex.I * (kz * refl d (l - 1) z - kz' * refl d l' z'))
    else Complex.exp (Complex.I * (kz' * z' - kz * z))

/-- Eq. (3.22): the height of the effective location `τ̂^{∗⋆}_{ℓℓ'}(r)` of a target at height
`z` (by eq. (3.23), `τ_ℓ(r) = (x, y, τ_ℓ(z))` changes only the height). -/
def effZ (d : ℕ → ℝ) (l l' : ℕ) (a b : Dir) (z : ℝ) : ℝ :=
  match a, b with
  | true, true => if l < l' then z else refl d l z
  | true, false => if l ≤ l' then z else refl d l z
  | false, true => if l < l' then refl d (l - 1) z else z
  | false, false => if l ≤ l' then refl d (l - 1) z else z

/-- Eq. (3.21): the height of the equivalent polarization coordinate `τ̆^⋆_{ℓℓ'}(r')` of a source
at height `z'`. -/
def polZ (d : ℕ → ℝ) (l l' : ℕ) (b : Dir) (z' : ℝ) : ℝ :=
  if b then (if l < l' then z' else refl d (l' - 1) z')
  else (if l ≤ l' then refl d l' z' else z')

/-- Eqs. (3.22)-(3.23): the effective location `τ̂^{∗⋆}_{ℓℓ'}(r)` of a target `r = (x, y, z)`. -/
def effLoc (d : ℕ → ℝ) (l l' : ℕ) (a b : Dir) (r : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (r.1, r.2.1, effZ d l l' a b r.2.2)

/-- Eqs. (3.21), (3.23): the equivalent polarization coordinate `τ̆^⋆_{ℓℓ'}(r')` of a source
`r' = (x', y', z')`. -/
def polLoc (d : ℕ → ℝ) (l l' : ℕ) (b : Dir) (r' : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (r'.1, r'.2.1, polZ d l l' b r'.2.2)

/-- Section 3.2 and eq. (3.24): the vertical transmission distance of the component `(∗, ⋆)`, the
vertical part `|ẑ - z̆|` of the field transmission distance `|τ̂^{∗⋆}_{ℓℓ'}(r) - τ̆^⋆_{ℓℓ'}(r')|`. -/
def vertDist (d : ℕ → ℝ) (l l' : ℕ) (a b : Dir) (z z' : ℝ) : ℝ :=
  |effZ d l l' a b z - polZ d l l' b z'|

/-- Eq. (3.5): `J_1 = diag(1, 1, 0)`. -/
def J1 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]

/-- Eq. (3.5): `J_2 = diag(0, 0, 1)`. -/
def J2 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, 0; 0, 0, 1]

/-- Eq. (3.5): `J_3`, with entries `i k_x`, `i k_y` in the third column. -/
def J3 (kx ky : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, Complex.I * (kx : ℂ); 0, 0, Complex.I * (ky : ℂ); 0, 0, 0]

/-- Eq. (3.5): `J_4`, with entries `i k_x`, `i k_y` in the third row. -/
def J4 (kx ky : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, 0; Complex.I * (kx : ℂ), Complex.I * (ky : ℂ), 0]

/-- Eq. (3.5): `J_5 = -[[k_x², k_x k_y, 0], [k_x k_y, k_y², 0], [0, 0, 0]]`. -/
def J5 (kx ky : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-((kx : ℂ) ^ 2), -((kx : ℂ) * ky), 0; -((kx : ℂ) * ky), -((ky : ℂ) ^ 2), 0; 0, 0, 0]

/-- Section 3.1, matrix `M_1` (display after eq. (3.15)). -/
def M1 : Matrix (Fin 3) (Fin 3) ℂ := !![1 / 2, 0, 0; 0, 1 / 2, 0; 0, 0, 0]

/-- Section 3.1, matrix `M_2` (display after eq. (3.15)). -/
def M2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1 / 4, Complex.I / 4, 0; Complex.I / 4, 1 / 4, 0; 0, 0, 0]

/-- Section 3.1, matrix `M_3` (display after eq. (3.15)). -/
def M3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1 / 4, -Complex.I / 4, 0; -Complex.I / 4, 1 / 4, 0; 0, 0, 0]

/-- Section 3.1, matrix `M_4` (display after eq. (3.15)). -/
def M4 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1 / 2; 0, 0, -Complex.I / 2; 0, 0, 0]

/-- Section 3.1, matrix `M_5` (display after eq. (3.15)). -/
def M5 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1 / 2; 0, 0, Complex.I / 2; 0, 0, 0]

/-- Section 3.1, matrix `M_6` (display after eq. (3.15)). -/
def M6 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, 0; 0, 0, 1]

/-- `k_ρ = √(k_x² + k_y²)`, the radial polar coordinate of `(k_x, k_y)` (eq. (3.4)). -/
def krhoOf (kx ky : ℝ) : ℝ := Real.sqrt (kx ^ 2 + ky ^ 2)

/-- Eq. (3.4): `e^{iα}` for the polar angle `α` of `(k_x, k_y)`, i.e. `(k_x + i k_y) / k_ρ`
(equal to `0` at the origin, a null set). -/
def eia (kx ky : ℝ) : ℂ := ((kx : ℂ) + (ky : ℂ) * Complex.I) / (krhoOf kx ky : ℂ)

/-- Eq. (3.3) without the term `δ`, which is supported on `z = z'` and carries the factor
`δ_{ℓℓ'}`: the spectral electric dyadic Green's function
`-(iω/k_ℓ²)(k_ℓ² φ J_1 + μ_ℓ k_ρ² ψ J_2 + μ_ℓ ∂_z ψ J_3 + μ_ℓ ψ̃ J_4 + (k_ℓ² φ + μ_ℓ ∂_z ψ̃)/k_ρ² J_5)`
built from coefficient functions `φ(z, z')`, `ψ(z, z')`, `ψ̃(z, z')` of the target layer `ℓ`, with
`kl = k_ℓ` and `mul = μ_ℓ`. -/
def specGE (omega kl mul kx ky : ℝ) (phi psi psiT : ℝ → ℝ → ℂ) (z z' : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  let kr2 : ℂ := ((kx ^ 2 + ky ^ 2 : ℝ) : ℂ)
  (-(Complex.I * (omega : ℂ)) / (kl : ℂ) ^ 2) •
    (((kl : ℂ) ^ 2 * phi z z') • J1 + ((mul : ℂ) * kr2 * psi z z') • J2
      + ((mul : ℂ) * deriv (fun w => psi w z') z) • J3 kx ky
      + ((mul : ℂ) * psiT z z') • J4 kx ky
      + (((kl : ℂ) ^ 2 * phi z z' + (mul : ℂ) * deriv (fun w => psiT w z') z) / kr2) • J5 kx ky)

/-- Eq. (3.8), first line without the free-space part: the reaction part
`-(1/(2ω k_{ℓ'z})) Σ_{∗,⋆} φ^{∗⋆}_{ℓℓ'}(k_ρ) Z^{∗⋆}_{ℓℓ'}(k_ρ, z, z')` of `φ_ℓ`, for density
functions `phiD ∗ ⋆` of `k_ρ`. -/
def phiReac (omega : ℝ) (k : ℕ → ℝ) (d : ℕ → ℝ) (l l' : ℕ) (phiD : Dir → Dir → ℝ → ℂ)
    (krho z z' : ℝ) : ℂ :=
  -(2 * (omega : ℂ) * vkz (k l') krho)⁻¹ *
    ∑ a : Dir, ∑ b : Dir, phiD a b krho * Zfun k d l l' a b krho z z'

/-- Eq. (3.8), second line without the free-space part: the reaction part
`-(1/(2ω μ_{ℓ'} k_{ℓ'z})) Σ_{∗,⋆} ψ^{∗⋆}_{ℓℓ'}(k_ρ) Z^{∗⋆}_{ℓℓ'}(k_ρ, z, z')` of `ψ_ℓ`. -/
def psiReac (omega : ℝ) (k muL : ℕ → ℝ) (d : ℕ → ℝ) (l l' : ℕ) (psiD : Dir → Dir → ℝ → ℂ)
    (krho z z' : ℝ) : ℂ :=
  -(2 * (omega : ℂ) * (muL l' : ℂ) * vkz (k l') krho)⁻¹ *
    ∑ a : Dir, ∑ b : Dir, psiD a b krho * Zfun k d l l' a b krho z z'

/-- Section 3.1 (before eq. (3.16)): `γ_{ℓℓ'} = μ_ℓ / (μ_{ℓ'} k_ℓ²)`, with `kl = k_ℓ`,
`mul = μ_ℓ`, `mul' = μ_{ℓ'}`. -/
def gam (kl mul mul' : ℝ) : ℂ := (mul : ℂ) / ((mul' : ℂ) * (kl : ℂ) ^ 2)

/-- Eq. (3.14): the matrix `Θ^{∗⋆}_{ℓℓ'}(k_x, k_y)` of the component `(∗, ⋆) = (a, b)`,
`φ (J_1 + J_5/k_ρ²) + (μ_ℓ ψ/(μ_{ℓ'} k_ℓ²)) (k_ρ² J_2 + c₃ i k_{ℓz} J_3 + c₄ i k_{ℓ'z} J_4
+ c₅ (k_{ℓz} k_{ℓ'z}/k_ρ²) J_5)` with the signs `(c₃, c₄, c₅)` printed in (3.14):
`(+,-,+)` for `↑↓`, `(+,+,-)` for `↑↑`, `(-,-,-)` for `↓↓`, `(-,+,+)` for `↓↑`; here `phi`, `psi`
are the values `φ^{∗⋆}_{ℓℓ'}(k_ρ)`, `ψ^{∗⋆}_{ℓℓ'}(k_ρ)`. -/
def Theta (kl kl' mul mul' : ℝ) (a b : Dir) (phi psi : ℂ) (kx ky : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  let kr2 : ℂ := ((kx ^ 2 + ky ^ 2 : ℝ) : ℂ)
  let kz : ℂ := vkz kl (krhoOf kx ky)
  let kz' : ℂ := vkz kl' (krhoOf kx ky)
  let c : ℂ × ℂ × ℂ :=
    match a, b with
    | true, false => (1, -1, 1)
    | true, true => (1, 1, -1)
    | false, false => (-1, -1, -1)
    | false, true => (-1, 1, 1)
  phi • (J1 + kr2⁻¹ • J5 kx ky)
    + (gam kl mul mul' * psi) • (kr2 • J2 + (c.1 * Complex.I * kz) • J3 kx ky
      + (c.2.1 * Complex.I * kz') • J4 kx ky + (c.2.2 * kz * kz' / kr2) • J5 kx ky)

/-- Eq. (3.13): the spectral reaction field component
`Ĝ^{∗⋆}_{ℓℓ'}(k_x, k_y, z, z') = i Z^{∗⋆}_{ℓℓ'}(k_ρ, z, z') / (2 k_{ℓ'z}) Θ^{∗⋆}_{ℓℓ'}(k_x, k_y)`,
for the densities `phiD`, `psiD` (functions of `k_ρ`) of the component `(a, b)`. -/
def GhatReac (k muL : ℕ → ℝ) (d : ℕ → ℝ) (l l' : ℕ) (a b : Dir) (phiD psiD : ℝ → ℂ)
    (kx ky z z' : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (Complex.I * Zfun k d l l' a b (krhoOf kx ky) z z' / (2 * vkz (k l') (krhoOf kx ky))) •
    Theta (k l) (k l') (muL l) (muL l') a b (phiD (krhoOf kx ky)) (psiD (krhoOf kx ky)) kx ky

/-- Eq. (3.18), first line: the `(i, j)` entry of the physical-space reaction field component
`G^{∗⋆}_{ℓℓ'}(r, r') = (1/4π²) ∬ Ĝ^{∗⋆}_{ℓℓ'} e^{i k_x (x - x') + i k_y (y - y')} dk_x dk_y`
(inverse Fourier transform (3.2)). -/
def GReac (k muL : ℕ → ℝ) (d : ℕ → ℝ) (l l' : ℕ) (a b : Dir) (phiD psiD : ℝ → ℂ)
    (r r' : ℝ × ℝ × ℝ) (i j : Fin 3) : ℂ :=
  (4 * (Real.pi : ℂ) ^ 2)⁻¹ * ∫ p : ℝ × ℝ,
    GhatReac k muL d l l' a b phiD psiD p.1 p.2 r.2.2 r'.2.2 i j *
      Complex.exp (Complex.I * ((p.1 : ℂ) * (r.1 - r'.1) + (p.2 : ℂ) * (r.2.1 - r'.2.1)))

/-- Eq. (3.16): `σ^{∗⋆}_{ℓℓ'1} = φ^{∗⋆}_{ℓℓ'}/k_{ℓ'z} ∓ γ_{ℓℓ'} k_{ℓz} ψ^{∗⋆}_{ℓℓ'}`, with `-` for
`↑↓`, `↓↑` and `+` for `↑↑`, `↓↓`; `kl = k_ℓ`, `kl' = k_{ℓ'}`, `mul = μ_ℓ`, `mul' = μ_{ℓ'}`. -/
def sig1 (kl kl' mul mul' : ℝ) (a b : Dir) (phiD psiD : ℝ → ℂ) (krho : ℝ) : ℂ :=
  phiD krho / vkz kl' krho + (if a = b then 1 else -1) * gam kl mul mul' * vkz kl krho * psiD krho

/-- Eq. (3.16) as printed: `σ^{∗↓}_{ℓℓ'3} = φ/k_{ℓ'z} + γ_{ℓℓ'} k_{ℓz} ψ` and
`σ^{∗↑}_{ℓℓ'3} = φ/k_{ℓ'z} - γ_{ℓℓ'} k_{ℓz} ψ`. (Not used by the statements: substituting into
(3.14) gives `sig3c`, which differs from it for `↓↑` and `↓↓`.) -/
def sig3 (kl kl' mul mul' : ℝ) (b : Dir) (phiD psiD : ℝ → ℂ) (krho : ℝ) : ℂ :=
  phiD krho / vkz kl' krho + (if b then -1 else 1) * gam kl mul mul' * vkz kl krho * psiD krho

/-- The density multiplying `e^{±2iα} M_2`, `M_3` that the substitution of the identities after
(3.15) into (3.14) produces (Section 3.1, display after (3.17)):
`φ/k_{ℓ'z} + γ_{ℓℓ'} k_{ℓz} ψ` for `↑↓`, `↓↑` and `φ/k_{ℓ'z} - γ_{ℓℓ'} k_{ℓz} ψ` for `↑↑`, `↓↓`.
It agrees with the printed `σ_{ℓℓ'3}` of (3.16) for `↑↓`, `↑↑`. -/
def sig3c (kl kl' mul mul' : ℝ) (a b : Dir) (phiD psiD : ℝ → ℂ) (krho : ℝ) : ℂ :=
  phiD krho / vkz kl' krho + (if a = b then -1 else 1) * gam kl mul mul' * vkz kl krho * psiD krho

/-- Eq. (3.17): `σ^{↑⋆}_{ℓℓ'2} = -γ_{ℓℓ'} k_ρ k_{ℓz}/k_{ℓ'z} ψ^{↑⋆}_{ℓℓ'}` and
`σ^{↓⋆}_{ℓℓ'2} = γ_{ℓℓ'} k_ρ k_{ℓz}/k_{ℓ'z} ψ^{↓⋆}_{ℓℓ'}`. -/
def sig2 (kl kl' mul mul' : ℝ) (a : Dir) (psiD : ℝ → ℂ) (krho : ℝ) : ℂ :=
  (if a then -1 else 1) * gam kl mul mul' * krho * vkz kl krho / vkz kl' krho * psiD krho

/-- Eq. (3.17): `σ^{∗↓}_{ℓℓ'4} = γ_{ℓℓ'} k_ρ ψ^{∗↓}_{ℓℓ'}` and
`σ^{∗↑}_{ℓℓ'4} = -γ_{ℓℓ'} k_ρ ψ^{∗↑}_{ℓℓ'}`. -/
def sig4 (kl mul mul' : ℝ) (b : Dir) (psiD : ℝ → ℂ) (krho : ℝ) : ℂ :=
  (if b then -1 else 1) * gam kl mul mul' * krho * psiD krho

/-- Eq. (3.17): `σ^{∗⋆}_{ℓℓ'5} = γ_{ℓℓ'} k_ρ²/k_{ℓ'z} ψ^{∗⋆}_{ℓℓ'}`. -/
def sig5 (kl kl' mul mul' : ℝ) (psiD : ℝ → ℂ) (krho : ℝ) : ℂ :=
  gam kl mul mul' * (krho : ℂ) ^ 2 / vkz kl' krho * psiD krho

/-- Section 3.3 (display before eq. (3.28)): `𝒵(k_ρ, z, z') = e^{s (i k_z z - i k'_z z')}` with
`k = k_ℓ`, `k' = k_{ℓ'}`, `k_z = k_{ℓz}`, `k'_z = k_{ℓ'z}` and `s = s^{∗⋆}_{ℓℓ'}`. -/
def calZ (s k k' krho z z' : ℝ) : ℂ :=
  Complex.exp ((s : ℂ) * (Complex.I * vkz k krho * z - Complex.I * vkz k' krho * z'))

/-- Eq. (3.20) (and Section 3.3): `ℰ(r, r') = e^{i k_x (x - x') + i k_y (y - y')} 𝒵(k_ρ, z, z')`,
as a function of `(k_x, k_y)`. -/
def calE (s k k' kx ky : ℝ) (r r' : ℝ × ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * ((kx : ℂ) * (r.1 - r'.1) + (ky : ℂ) * (r.2.1 - r'.2.1))) *
    calZ s k k' (krhoOf kx ky) r.2.2 r'.2.2

/-- Integrand of eq. (3.19): `ℰ^{∗⋆}_{ℓℓ'}(τ̂^{∗⋆}_{ℓℓ'}(r), τ̆^⋆_{ℓℓ'}(r')) e^{iκα} σ(k_ρ)` as a
function of `p = (k_x, k_y)`. -/
def opLIntegrand (k : ℕ → ℝ) (d : ℕ → ℝ) (l l' : ℕ) (a b : Dir) (kappa : ℤ) (sigma : ℝ → ℂ)
    (r r' : ℝ × ℝ × ℝ) (p : ℝ × ℝ) : ℂ :=
  calE (sgnS l l' b) (k l) (k l') p.1 p.2 (effLoc d l l' a b r) (polLoc d l l' b r') *
    eia p.1 p.2 ^ kappa * sigma (krhoOf p.1 p.2)

/-- Eq. (3.19): `L^{∗⋆}_{ℓℓ'κ}[σ](r, r') = (i/8π²) ∬_{ℝ²} ℰ^{∗⋆}_{ℓℓ'}(τ̂(r), τ̆(r')) e^{iκα} σ(k_ρ)
dk_x dk_y`. -/
def opL (k : ℕ → ℝ) (d : ℕ → ℝ) (l l' : ℕ) (a b : Dir) (kappa : ℤ) (sigma : ℝ → ℂ)
    (r r' : ℝ × ℝ × ℝ) : ℂ :=
  Complex.I / (8 * (Real.pi : ℂ) ^ 2) * ∫ p : ℝ × ℝ, opLIntegrand k d l l' a b kappa sigma r r' p

/-- Eq. (3.28): `c^{νμ}_{nm} = (s^{∗⋆}_{ℓℓ'})^{n+ν+m+μ} i^{n+ν+1}`. -/
def cCoef (s : ℝ) (n : ℕ) (m : ℤ) (nu : ℕ) (mu : ℤ) : ℂ :=
  (s : ℂ) ^ ((n : ℤ) + (nu : ℤ) + m + mu) * Complex.I ^ (n + nu + 1)

/-- Integrand of eq. (3.28): `ℰ(r, r') e^{i(m-μ+κ)α} P̂_n^m(k_z/k) P̂_ν^μ(k'_z/k') σ(k_ρ)` as a
function of `p = (k_x, k_y)`; `P n m` stands for the analytically extended normalized associated
Legendre function `P̂_n^m`, whose normalization the paper does not state. -/
def intIIntegrand (P : ℕ → ℤ → ℂ → ℂ) (sigma : ℝ → ℂ) (s k k' : ℝ) (n : ℕ) (m kappa : ℤ)
    (nu : ℕ) (mu : ℤ) (r r' : ℝ × ℝ × ℝ) (p : ℝ × ℝ) : ℂ :=
  calE s k k' p.1 p.2 r r' * eia p.1 p.2 ^ (m - mu + kappa) *
    P n m (vkz k (krhoOf p.1 p.2) / k) * P nu mu (vkz k' (krhoOf p.1 p.2) / k') *
      sigma (krhoOf p.1 p.2)

/-- Eq. (3.28): `I^{νμ}_{nmκ}(r, r', σ) = (c^{νμ}_{nm}/2π) ∬_{ℝ²} ℰ(r, r') e^{i(m-μ+κ)α}
P̂_n^m(k_z/k) P̂_ν^μ(k'_z/k') σ(k_ρ) dk_x dk_y`. -/
def intI (P : ℕ → ℤ → ℂ → ℂ) (sigma : ℝ → ℂ) (s k k' : ℝ) (n : ℕ) (m kappa : ℤ) (nu : ℕ)
    (mu : ℤ) (r r' : ℝ × ℝ × ℝ) : ℂ :=
  cCoef s n m nu mu / (2 * (Real.pi : ℂ)) *
    ∫ p : ℝ × ℝ, intIIntegrand P sigma s k k' n m kappa nu mu r r' p

/-- Section 3.4.2: the Bessel function `J_n` of integer order `n`, through the integral
representation `J_n(x) = (2π iⁿ)⁻¹ ∫_0^{2π} e^{i x cos θ + i n θ} dθ` quoted there. -/
def besselJ (n : ℤ) (x : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I ^ n)⁻¹ *
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (Complex.I * (x : ℂ) * (Real.cos θ : ℂ) + Complex.I * (n : ℂ) * (θ : ℂ))

/-- Eq. (3.45): the Sommerfeld-type integral
`Î^{νμ}_{nmκ}(ρ, z, z'; σ) = ∫_0^∞ k_ρ J_{m-μ+κ}(k_ρ ρ) 𝒵(k_ρ, z, z') P̂_n^m(k_z/k)
P̂_ν^μ(k'_z/k') σ(k_ρ) dk_ρ`. -/
def intIhat (P : ℕ → ℤ → ℂ → ℂ) (sigma : ℝ → ℂ) (s k k' : ℝ) (n : ℕ) (m kappa : ℤ) (nu : ℕ)
    (mu : ℤ) (rho z z' : ℝ) : ℂ :=
  ∫ krho in Set.Ioi (0 : ℝ),
    (krho : ℂ) * besselJ (m - mu + kappa) (krho * rho) * calZ s k k' krho z z' *
      P n m (vkz k krho / k) * P nu mu (vkz k' krho / k') * sigma krho

/-- The Chebyshev polynomial of the first kind `T_n`, evaluated at a complex number. -/
def chebT (n : ℕ) (x : ℂ) : ℂ := (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval x

/-- Eq. (A.2): the coefficients `C^{ab}_{js}` of `T_j(a x + b) = Σ_{s=0}^j C^{ab}_{js} T_s(x)` by the
printed recurrence: `C_{00} = 1`, `C_{10} = b`, `C_{21} = 4ab`, `C_{n+1,n+1} = a C_{nn}` (`n ≥ 1`),
`C_{n+1,n} = a C_{n,n-1} + 2b C_{nn}` (`n ≥ 2`),
`C_{n+1,s} = a (C_{n,s-1} + C_{n,s+1}) + 2b C_{ns} - C_{n-1,s}` (`2 ≤ s ≤ n-1`, `n ≥ 3`),
`C_{n+1,1} = 2a C_{n0} + a C_{n2} + 2b C_{n1} - C_{n-1,1}` (`n ≥ 2`),
`C_{n+1,0} = a C_{n1} + 2b C_{n0} - C_{n-1,0}` (`n ≥ 1`), together with the initial value
`C_{11} = a`, which (A.2) uses but does not list, and `C_{js} = 0` for `s > j`. -/
def chebShiftCoeff (a b : ℂ) : ℕ → ℕ → ℂ
  | 0, s => if s = 0 then 1 else 0
  | 1, s => if s = 0 then b else if s = 1 then a else 0
  | n + 2, s =>
    if s = 0 then
      a * chebShiftCoeff a b (n + 1) 1 + 2 * b * chebShiftCoeff a b (n + 1) 0
        - chebShiftCoeff a b n 0
    else if s = 1 then
      (if n = 0 then 4 * a * b
       else 2 * a * chebShiftCoeff a b (n + 1) 0 + a * chebShiftCoeff a b (n + 1) 2
        + 2 * b * chebShiftCoeff a b (n + 1) 1 - chebShiftCoeff a b n 1)
    else if s = n + 2 then a * chebShiftCoeff a b (n + 1) (n + 1)
    else if s = n + 1 then
      a * chebShiftCoeff a b (n + 1) n + 2 * b * chebShiftCoeff a b (n + 1) (n + 1)
    else if s ≤ n then
      a * (chebShiftCoeff a b (n + 1) (s - 1) + chebShiftCoeff a b (n + 1) (s + 1))
        + 2 * b * chebShiftCoeff a b (n + 1) s - chebShiftCoeff a b n s
    else 0

/-- Eq. (3.49): `sgn(x) = (-1)^{min(0, x)}`. -/
def sgnPow (m : ℤ) : ℂ := (-1 : ℂ) ^ (min 0 m)

/-- Eq. (B.1): the prefactor `τ_{nm}(θ)` of the Chebyshev expansion of `P̂_n^m(cos θ)`, `m ≥ 0`:
`1` (`n`, `m` even), `sec θ` (`n` odd, `m` even), `sin θ` (`n`, `m` odd), `tan θ` (`n` even,
`m` odd). -/
def tauLeg (n m : ℕ) (θ : ℂ) : ℂ :=
  if n % 2 = 0 ∧ m % 2 = 0 then 1
  else if m % 2 = 0 then (Complex.cos θ)⁻¹
  else if n % 2 = 1 then Complex.sin θ
  else Complex.tan θ

/-- Eq. (B.1): the number of terms `K_n` of the Chebyshev expansion of `P̂_n^m`, `m ≥ 0`:
`n/2` (`n` even), `(n+1)/2` (`n` odd, `m` even), `(n-1)/2` (`n` odd, `m` odd). -/
def Kn (n m : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else if m % 2 = 0 then (n + 1) / 2 else (n - 1) / 2

/-- Section 3.4.1: the closed axis-parallel box of the FMM tree with centre `c` and side length
`h`. -/
def box (c : ℝ × ℝ × ℝ) (h : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | |p.1 - c.1| ≤ h / 2 ∧ |p.2.1 - c.2.1| ≤ h / 2 ∧ |p.2.2 - c.2.2| ≤ h / 2}

end Arxiv2507_18491


