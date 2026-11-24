-- Prove2me | Definitions.Def_Arxiv1310_4241_Basic
-- name    : Arxiv1310_4241_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T11:00:05.171149+00:00
-- url     : https://prove2.me/theorems/a9370308-1b54-40a3-b25e-025c104bf40b
-- title:
--   Time-harmonic Maxwell fields, Sommerfeld kernels, and planar Mie and generalized Debye representations
-- statement:
--   Objects of Sections I, II, IV and V of O'Neil (2013).
--
--   1. **Space and differential operators.** Points of $\mathbb R^3$ are $\mathbf x=(x,y,z)$; $z>0$ is the upper half-space. Fields are complex: a scalar field is $f:\mathbb R^3\to\mathbb C$, a vector field $\mathbf F:\mathbb R^3\to\mathbb C^3$. $\partial_i$, $\nabla$, $\nabla\cdot$, $\nabla\times$ and $\triangle$ are the usual real partial derivatives, gradient, divergence, curl and Laplacian. The transverse Laplacian is $\partial_x^2+\partial_y^2$, and the tangential divergence of $\mathbf F$ is $\partial_xF_x+\partial_yF_y$, the divergence of its tangential projection $-\mathbf n\times\mathbf n\times\mathbf F$ (eq. (38)). The normal is $\mathbf n=\hat{\mathbf z}$, so $\mathbf n\times(a,b,c)=(-b,a,0)$.
--   2. **Maxwell fields (Section I).** The wavenumber is $k=\omega\sqrt{\varepsilon\mu}$ (principal root) with $\omega\in\mathbb R$ and $\varepsilon,\mu\in\mathbb C$, and the standing assumption is $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$. A source-free time-harmonic Maxwell field on an open set $U$ is a pair $(\mathbf E,\mathbf H)$ of fields differentiable on $U$ with $\nabla\times\mathbf E=i\omega\mu\mathbf H$, $\nabla\times\mathbf H=-i\omega\varepsilon\mathbf E$, $\nabla\cdot\mathbf E=\nabla\cdot\mathbf H=0$ on $U$ (eq. (1) with $\mathbf J=0$, $\rho=0$). The radiation condition is eq. (3) exactly as printed, $\lim_{|\mathbf x|\to\infty,\ \mathbf x\in U}\big(\mathbf H(\mathbf x)\times\hat{\mathbf r}-\tfrac{\mu}{\varepsilon}\mathbf E(\mathbf x)\big)=0$ with $\hat{\mathbf r}=\mathbf x/|\mathbf x|$.
--   3. **Planar Mie fields (eq. (22)).** For scalar $u,v$: $\mathbf E=\nabla\times\nabla\times(u\hat{\mathbf z})+i\omega\mu\nabla\times(v\hat{\mathbf z})$, $\mathbf H=\nabla\times\nabla\times(v\hat{\mathbf z})-i\omega\varepsilon\nabla\times(u\hat{\mathbf z})$. $u$ solves the Helmholtz equation on $U$ if $\triangle u+k^2u=0$ there.
--   4. **Green's function and Sommerfeld kernel (eqs. (9)-(10)).** $g_k(\mathbf x)=e^{ik|\mathbf x|}/(4\pi|\mathbf x|)$. With $\beta=\sqrt{\xi^2+\eta^2-k^2}$, $\widehat g_k(\xi,\eta,z)=e^{-\beta|z|}/(8\pi^2\beta)$. The branch of $\beta$ is the principal root, except on the negative real axis (only for real $k$ and $\xi^2+\eta^2<k^2$), where $\beta=-i\sqrt{k^2-\xi^2-\eta^2}$; this is the branch with $\operatorname{Re}\beta\ge0$ for which eq. (9) represents the outgoing $g_k$. The kernels $e^{-\beta z}/(8\pi^2\beta)$ and $e^{\beta z}/(8\pi^2\beta)$ of eqs. (46) and (47) are used above and below an interface.
--   5. **Lorenz-gauge fields of a current (eq. (6)).** For a current $\mathbf J$: $\mathbf A=\int g_k(\mathbf x-\mathbf x')\mathbf J(\mathbf x')\,dV'$, $\mathbf H=\nabla\times\mathbf A$, and $\mathbf E=i\omega\mu\mathbf A-\frac1{i\omega\varepsilon}\nabla\int g_k(\mathbf x-\mathbf x')\,\nabla\cdot\mathbf J(\mathbf x')\,dV'$.
--   6. **Debye potentials (eq. (24)).** For a spectral density $\widehat\sigma$ on $\mathbb R^2$, $u(x,y,z)=\int_{\mathbb R^2}\widehat g_k(\xi,\eta,z)\widehat\sigma(\xi,\eta)e^{i(\xi x+\eta y)}\,d\xi\,d\eta$.
--   7. **Generalized Debye sources on one Fourier mode (Section V).** Fix $(\xi,\eta)$ and write $e=e^{i(\xi x+\eta y)}$. A planar density $c\,e$ has single-layer potential $\mathcal S_k[c\,e]=\widehat g_k(\xi,\eta,z)\,c\,e$ (eq. (40), with $e^{-\beta z}$ above and $e^{\beta z}$ below the plane), and $\nabla\triangle^{-1}[c\,e]$ has coefficient vector $(i\xi,i\eta,0)\cdot(-c/(\xi^2+\eta^2))$ (eq. (41)). On the plane, $\mathcal S_0$ multiplies a function of frequency $(\xi,\eta)$ by $\widehat g_0(\xi,\eta,0)$. The generalized Debye fields are $\mathbf E=\sqrt\mu\,(ik\mathcal S_k[\mathbf j]-\nabla\mathcal S_k[r]-\nabla\times\mathcal S_k[\mathbf m])$ and $\mathbf H=\sqrt\varepsilon\,(ik\mathcal S_k[\mathbf m]-\nabla\mathcal S_k[q]+\nabla\times\mathcal S_k[\mathbf j])$ (eqs. (32)-(34), (45)).
--   8. **Perfect conductor (eq. (35)).** $\mathbf j=ik(\nabla\triangle^{-1}r-\mathbf n\times\nabla\triangle^{-1}q)$, $\mathbf m=\mathbf n\times\mathbf j$, fields in $z\ge0$.
--   9. **Two layers (eqs. (45)-(48), (51), (53)).** Real constants $\varepsilon_0,\mu_0$ in $z>0$ and $\varepsilon_1,\mu_1$ in $z\le0$, $k_j=\omega\sqrt{\varepsilon_j\mu_j}$; currents $\mathbf j_0=i\omega(\sqrt{\mu_0\varepsilon_0}\nabla\triangle^{-1}r_0-\varepsilon_1\sqrt{\mu_1/\varepsilon_0}\,\mathbf n\times\nabla\triangle^{-1}r_1)$, $\mathbf j_1=\mathbf n\times\sqrt{\varepsilon_0/\varepsilon_1}\,\mathbf j_0$, and $\mathbf m_0,\mathbf m_1$ likewise with $q_j$ and $\varepsilon\leftrightarrow\mu$. The jumps $[f]=f_0-f_1$ of $\mathcal S_0\nabla\cdot\mathbf E$, $\mathbf n\cdot\varepsilon\mathbf E$, $\mathcal S_0\nabla\cdot\mathbf H$, $\mathbf n\cdot\mu\mathbf H$ across $z=0$ define a linear map of $(\widehat r_0,\widehat r_1,\widehat q_0,\widehat q_1)$, whose $4\times4$ matrix is the system matrix of eq. (53).
--
--   **Formalization Note** The paper does not name the branch of $\sqrt{\xi^2+\eta^2-k^2}$; the branch chosen is the one that makes eq. (9) true. Section V is formalised on one Fourier mode, on which the paper states every operator acts by multiplication (eqs. (39)-(41)); its eq. (40) is used as the definition of $\mathcal S_k$ on a mode. Section V.B uses positive real material constants, for which the square roots of ratios in eq. (48) are unambiguous. A matrix entry of eq. (53) is the Fourier coefficient of a jump, read off as its value at the origin, where $e=1$.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), Sections I-II (eqs. (1)-(10)), Section IV (eqs. (22)-(24)), Section V (eqs. (32)-(41), (45)-(53)), https://arxiv.org/abs/1310.4241

import Mathlib

/-!
M. O'Neil, *A generalized Debye source approach to electromagnetic scattering in layered media*,
arXiv:1310.4241v1 (2013): time-harmonic Maxwell fields and the Helmholtz Green's function with its
Sommerfeld (spectral) representation (Sections I-II, eqs. (1)-(10)), the Lorenz-gauge fields of a
current (eq. (6)), the planar Lorenz-Debye-Mie representation (Section IV, eqs. (22)-(24)), and the
generalized Debye source representation on a perfectly conducting half-space and on a two-layer
medium, evaluated on one Fourier mode (Section V, eqs. (32)-(41) and (45)-(53)).
-/

open MeasureTheory

noncomputable section

namespace Arxiv1310_4241

/-- Physical space `ℝ³` (Section I); the point `p` has coordinates `(x, y, z) = (p 0, p 1, p 2)`. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The point `(x, y, z)` of space. -/
def pt (x y z : ℝ) : Space := !₂[x, y, z]

/-- Section II: the upper half-space `z > 0`, the homogeneous region where the scattered fields
are represented. -/
def upperHalfSpace : Set Space := {p | 0 < p 2}

/-- The partial derivative `∂f/∂x_i` at `p` (derivative along the `i`-th coordinate direction). -/
def pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (i : Fin 3) (f : Space → F)
    (p : Space) : F :=
  fderiv ℝ f p (EuclideanSpace.single i 1)

/-- Gradient `∇f` of a complex scalar field. -/
def grad (f : Space → ℂ) (p : Space) : Fin 3 → ℂ := ![pd 0 f p, pd 1 f p, pd 2 f p]

/-- Divergence `∇ · F` of a complex vector field. -/
def divergence (F : Space → Fin 3 → ℂ) (p : Space) : ℂ :=
  pd 0 (fun q => F q 0) p + pd 1 (fun q => F q 1) p + pd 2 (fun q => F q 2) p

/-- Curl `∇ × F` of a complex vector field. -/
def curl (F : Space → Fin 3 → ℂ) (p : Space) : Fin 3 → ℂ :=
  ![pd 1 (fun q => F q 2) p - pd 2 (fun q => F q 1) p,
    pd 2 (fun q => F q 0) p - pd 0 (fun q => F q 2) p,
    pd 0 (fun q => F q 1) p - pd 1 (fun q => F q 0) p]

/-- Laplacian `△f = ∂²f/∂x² + ∂²f/∂y² + ∂²f/∂z²`. -/
def laplacian (f : Space → ℂ) (p : Space) : ℂ :=
  pd 0 (pd 0 f) p + pd 1 (pd 1 f) p + pd 2 (pd 2 f) p

/-- Eq. (23): the transverse Laplacian `∂²f/∂x² + ∂²f/∂y²`. -/
def transverseLaplacian (f : Space → ℂ) (p : Space) : ℂ :=
  pd 0 (pd 0 f) p + pd 1 (pd 1 f) p

/-- Section V: the divergence along the plane `z = const` of the tangential projection
`-n × n × F = (F_x, F_y, 0)` of a vector field (eq. (38)), `∂F_x/∂x + ∂F_y/∂y`. -/
def tangentialDivergence (F : Space → Fin 3 → ℂ) (p : Space) : ℂ :=
  pd 0 (fun q => F q 0) p + pd 1 (fun q => F q 1) p

/-- The vector field `u ẑ` (eq. (22)). -/
def zhatField (u : Space → ℂ) : Space → Fin 3 → ℂ := fun p => ![0, 0, u p]

/-- `n × v` with `n = ẑ` (Sections II and V: `n = ẑ` always). -/
def nCross (v : Fin 3 → ℂ) : Fin 3 → ℂ := ![-v 1, v 0, 0]

/-- Section I: the wavenumber `k = ω √(εμ)` (principal square root). -/
def wavenumber (ω : ℝ) (ε μ : ℂ) : ℂ := ω * (ε * μ) ^ (1 / 2 : ℂ)

/-- Section I: the standing causality assumption on the wavenumber, `Re k > 0` and `Im k ≥ 0`. -/
def IsCausalWavenumber (k : ℂ) : Prop := 0 < k.re ∧ 0 ≤ k.im

/-- Principal square root of a complex number (used for `√ε`, `√μ` of Section V). -/
def csqrt (z : ℂ) : ℂ := z ^ (1 / 2 : ℂ)

/-- Eq. (1) on an open region `U` free of sources (`J = 0`, `ρ = 0` there): the fields are
differentiable and `∇ × E = iωμH`, `∇ × H = -iωεE`, `∇ · E = 0`, `∇ · H = 0` on `U`. -/
def IsSourceFreeMaxwellOn (ω : ℝ) (ε μ : ℂ) (U : Set Space) (E H : Space → Fin 3 → ℂ) : Prop :=
  ∀ p ∈ U, DifferentiableAt ℝ E p ∧ DifferentiableAt ℝ H p ∧
    curl E p = (Complex.I * ω * μ) • H p ∧ curl H p = (-(Complex.I * ω * ε)) • E p ∧
    divergence E p = 0 ∧ divergence H p = 0

/-- The radial unit vector `r̂ = x / |x|`. -/
def radialUnit (p : Space) : Fin 3 → ℂ := fun i => ((p i / ‖p‖ : ℝ) : ℂ)

/-- Eq. (3), as printed: `lim_{|x| → ∞} (H(x) × r̂ - (μ/ε) E(x)) = 0`, the limit taken over
points of the region `U`. -/
def SilverMullerAsPrinted (ε μ : ℂ) (U : Set Space) (E H : Space → Fin 3 → ℂ) : Prop :=
  Filter.Tendsto (fun p => crossProduct (H p) (radialUnit p) - (μ / ε) • E p)
    (Bornology.cobounded Space ⊓ Filter.principal U) (nhds 0)

/-- `u` solves the homogeneous Helmholtz equation `△u + k²u = 0` on `U` (Section IV). -/
def IsHelmholtzOn (k : ℂ) (U : Set Space) (u : Space → ℂ) : Prop :=
  ∀ p ∈ U, laplacian u p + k ^ 2 * u p = 0

/-- Eq. (22): the planar Lorenz-Debye-Mie electric field
`E = ∇ × ∇ × (u ẑ) + iωμ ∇ × (v ẑ)`. -/
def mieE (ω : ℝ) (μ : ℂ) (u v : Space → ℂ) : Space → Fin 3 → ℂ :=
  fun p => curl (curl (zhatField u)) p + (Complex.I * ω * μ) • curl (zhatField v) p

/-- Eq. (22): the planar Lorenz-Debye-Mie magnetic field
`H = ∇ × ∇ × (v ẑ) - iωε ∇ × (u ẑ)`. -/
def mieH (ω : ℝ) (ε : ℂ) (u v : Space → ℂ) : Space → Fin 3 → ℂ :=
  fun p => curl (curl (zhatField v)) p - (Complex.I * ω * ε) • curl (zhatField u) p

/-- Eq. (9): the Helmholtz Green's function `g_k(x) = e^{ik|x|} / (4π|x|)`. -/
def greenFn (k : ℂ) (p : Space) : ℂ :=
  Complex.exp (Complex.I * k * ‖p‖) / (4 * Real.pi * ‖p‖)

/-- Eqs. (9)-(10): `β = √(ξ² + η² - k²)`. The paper does not name the branch; this is the root
with `Re β ≥ 0` for which the Sommerfeld formula (9) represents `e^{ik|x|}/(4π|x|)`: the principal
root, except on the negative real axis (reached only for real `k` and `ξ² + η² < k²`), where
`β = -i √(k² - ξ² - η²)`, the limit of the principal root from `Im k > 0`. -/
def sommerfeldRoot (k : ℂ) (ξ η : ℝ) : ℂ :=
  if ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).im = 0 ∧ ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).re < 0 then
    -Complex.I * (Real.sqrt (-((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2).re) : ℂ)
  else ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2) ^ (1 / 2 : ℂ)

/-- Eq. (10): `ĝ_k(ξ, η, z) = e^{-β|z|} / (8π² β)`. -/
def ghat (k : ℂ) (ξ η z : ℝ) : ℂ :=
  Complex.exp (-(sommerfeldRoot k ξ η) * |z|) / (8 * Real.pi ^ 2 * sommerfeldRoot k ξ η)

/-- Eq. (46): the kernel used above an interface, `e^{-βz} / (8π² β)` (equal to `ĝ_k` for
`z ≥ 0`, continued as the same exponential). -/
def ghatUp (k : ℂ) (ξ η z : ℝ) : ℂ :=
  Complex.exp (-(sommerfeldRoot k ξ η) * z) / (8 * Real.pi ^ 2 * sommerfeldRoot k ξ η)

/-- Eq. (47): the kernel used below an interface, `e^{βz} / (8π² β)` (equal to `ĝ_k` for
`z ≤ 0`, continued as the same exponential). -/
def ghatDown (k : ℂ) (ξ η z : ℝ) : ℂ :=
  Complex.exp (sommerfeldRoot k ξ η * z) / (8 * Real.pi ^ 2 * sommerfeldRoot k ξ η)

/-- The plane wave `e^{i(ξx + ηy)}` (eqs. (24), (37)). -/
def planeWave (ξ η x y : ℝ) : ℂ := Complex.exp (Complex.I * (ξ * x + η * y))

/-- Eq. (6): the volume potential `∫ g_k(x - x') f(x') dV'`. -/
def volumePotential (k : ℂ) (f : Space → ℂ) (p : Space) : ℂ :=
  ∫ q, greenFn k (p - q) * f q

/-- Eq. (6): the vector potential `∫ g_k(x - x') J(x') dV'` of a current `J`, componentwise. -/
def vectorPotential (k : ℂ) (J : Space → Fin 3 → ℂ) : Space → Fin 3 → ℂ :=
  fun p i => volumePotential k (fun q => J q i) p

/-- Eq. (6): the Lorenz-gauge magnetic field `H = ∇ × ∫ g_k J dV'`. -/
def lorenzH (k : ℂ) (J : Space → Fin 3 → ℂ) : Space → Fin 3 → ℂ :=
  curl (vectorPotential k J)

/-- Eq. (6): the Lorenz-gauge electric field
`E = iωμ ∫ g_k J dV' - (1/(iωε)) ∇ ∫ g_k (∇ · J) dV'`, with `k = ω √(εμ)`. -/
def lorenzE (ω : ℝ) (ε μ : ℂ) (J : Space → Fin 3 → ℂ) : Space → Fin 3 → ℂ :=
  fun p => (Complex.I * ω * μ) • vectorPotential (wavenumber ω ε μ) J p -
    (1 / (Complex.I * ω * ε)) • grad (volumePotential (wavenumber ω ε μ) (divergence J)) p

/-- Eq. (24): the Debye potential `u(x, y, z) = ∫ ĝ_k(ξ, η, z) σ̂(ξ, η) e^{i(ξx + ηy)} dξ dη`
with spectral density `σ̂`. -/
def debyePotential (k : ℂ) (σh : ℝ × ℝ → ℂ) (p : Space) : ℂ :=
  ∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 (p 2) * σh ζ * planeWave ζ.1 ζ.2 (p 0) (p 1)

/-! ### Section V on one Fourier mode

The paper evaluates every operator of the generalized Debye representation on Fourier modes
`e^{i(ξx+ηy)}`, where it acts by multiplication (Section V.A, eqs. (39)-(41)). The definitions
below are the densities, currents, layer potentials and fields generated by one mode. -/

/-- The planar mode `e^{i(ξx + ηy)}` as a function on space (independent of `z`). -/
def mode (ξ η : ℝ) (p : Space) : ℂ := planeWave ξ η (p 0) (p 1)

/-- A planar vector density with constant coefficient vector `v` on the mode `(ξ, η)`. -/
def modeField (v : Fin 3 → ℂ) (ξ η : ℝ) : Space → Fin 3 → ℂ := fun p i => v i * mode ξ η p

/-- Eqs. (40), (46): the Helmholtz single layer `S_k` of the planar density `c e^{i(ξx+ηy)}` on
`z = 0`, on and above the plane: `ĝ_k(ξ, η, z) c e^{i(ξx+ηy)}` with `e^{-βz}`. -/
def slpUp (k : ℂ) (ξ η : ℝ) (c : ℂ) : Space → ℂ :=
  fun p => ghatUp k ξ η (p 2) * c * mode ξ η p

/-- Eqs. (40), (47): the single layer `S_k` of `c e^{i(ξx+ηy)}` on and below the plane, with
`e^{βz}`. -/
def slpDown (k : ℂ) (ξ η : ℝ) (c : ℂ) : Space → ℂ :=
  fun p => ghatDown k ξ η (p 2) * c * mode ξ η p

/-- Eqs. (39)-(41): the coefficient vector of `∇△⁻¹ f` for the planar density
`f = c e^{i(ξx+ηy)}`: `△⁻¹` multiplies by `-1/(ξ² + η²)` and `∇` by `(iξ, iη, 0)`. -/
def gradInvLap (ξ η : ℝ) (c : ℂ) : Fin 3 → ℂ :=
  ![Complex.I * ξ * (-c / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)),
    Complex.I * η * (-c / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)), 0]

/-- Eq. (40) with `k = 0`: the Laplace single layer `S_0` on the plane `z = 0` applied to a
function of frequency `(ξ, η)` on that plane, which multiplies it by `ĝ_0(ξ, η, 0)`. -/
def laplaceSingleLayerOnMode (ξ η : ℝ) (f : Space → ℂ) : Space → ℂ :=
  fun p => ghat 0 ξ η 0 * f p

/-- Eqs. (32)-(34), (45): the generalized Debye electric field
`E = √μ (ik S[j] - ∇ S[r] - ∇ × S[m])`, where `S c` is the layer potential of the mode with
coefficient `c`, and `j`, `m`, `r` are the coefficients of the currents and of the source `r`. -/
def debyeE (sqrtμ k : ℂ) (S : ℂ → Space → ℂ) (j m : Fin 3 → ℂ) (r : ℂ) :
    Space → Fin 3 → ℂ :=
  fun p => sqrtμ • ((Complex.I * k) • (fun i => S (j i) p) - grad (S r) p -
    curl (fun p' i => S (m i) p') p)

/-- Eqs. (32)-(34), (45): the generalized Debye magnetic field
`H = √ε (ik S[m] - ∇ S[q] + ∇ × S[j])`. -/
def debyeH (sqrtε k : ℂ) (S : ℂ → Space → ℂ) (j m : Fin 3 → ℂ) (q : ℂ) :
    Space → Fin 3 → ℂ :=
  fun p => sqrtε • ((Complex.I * k) • (fun i => S (m i) p) - grad (S q) p +
    curl (fun p' i => S (j i) p') p)

/-- Eq. (35) on a mode: `j = ik(∇△⁻¹ r - n × ∇△⁻¹ q)` for the perfect conductor. -/
def pecJ (k : ℂ) (ξ η : ℝ) (r q : ℂ) : Fin 3 → ℂ :=
  (Complex.I * k) • (gradInvLap ξ η r - nCross (gradInvLap ξ η q))

/-- Section V.A: the scattered electric field in `z ≥ 0` above the perfect conductor `z ≤ 0`
generated by the sources `r e^{i(ξx+ηy)}`, `q e^{i(ξx+ηy)}` (eqs. (32)-(35), `m = n × j`). -/
def pecE (ω : ℝ) (ε μ : ℂ) (ξ η : ℝ) (r q : ℂ) : Space → Fin 3 → ℂ :=
  debyeE (csqrt μ) (wavenumber ω ε μ) (slpUp (wavenumber ω ε μ) ξ η)
    (pecJ (wavenumber ω ε μ) ξ η r q) (nCross (pecJ (wavenumber ω ε μ) ξ η r q)) r

/-- Section V.A: the scattered magnetic field above the perfect conductor for the same sources. -/
def pecH (ω : ℝ) (ε μ : ℂ) (ξ η : ℝ) (r q : ℂ) : Space → Fin 3 → ℂ :=
  debyeH (csqrt ε) (wavenumber ω ε μ) (slpUp (wavenumber ω ε μ) ξ η)
    (pecJ (wavenumber ω ε μ) ξ η r q) (nCross (pecJ (wavenumber ω ε μ) ξ η r q)) q

/-- Eq. (48) on a mode: `j_0 = iω(√(μ₀ε₀) ∇△⁻¹ r_0 - ε₁ √(μ₁/ε₀) n × ∇△⁻¹ r_1)` (real material
constants `ε₀, μ₀` in `z > 0` and `ε₁, μ₁` in `z ≤ 0`). -/
def twoLayerJ0 (ω ε0 μ0 ε1 μ1 ξ η : ℝ) (r0 r1 : ℂ) : Fin 3 → ℂ :=
  (Complex.I * ω) • (((Real.sqrt (μ0 * ε0) : ℝ) : ℂ) • gradInvLap ξ η r0 -
    ((ε1 * Real.sqrt (μ1 / ε0) : ℝ) : ℂ) • nCross (gradInvLap ξ η r1))

/-- Eq. (48): `j_1 = n × √(ε₀/ε₁) j_0`. -/
def twoLayerJ1 (ω ε0 μ0 ε1 μ1 ξ η : ℝ) (r0 r1 : ℂ) : Fin 3 → ℂ :=
  nCross (((Real.sqrt (ε0 / ε1) : ℝ) : ℂ) • twoLayerJ0 ω ε0 μ0 ε1 μ1 ξ η r0 r1)

/-- Eq. (48): `m_0 = iω(√(μ₀ε₀) ∇△⁻¹ q_0 - μ₁ √(ε₁/μ₀) n × ∇△⁻¹ q_1)`. -/
def twoLayerM0 (ω ε0 μ0 ε1 μ1 ξ η : ℝ) (q0 q1 : ℂ) : Fin 3 → ℂ :=
  (Complex.I * ω) • (((Real.sqrt (μ0 * ε0) : ℝ) : ℂ) • gradInvLap ξ η q0 -
    ((μ1 * Real.sqrt (ε1 / μ0) : ℝ) : ℂ) • nCross (gradInvLap ξ η q1))

/-- Eq. (48): `m_1 = n × √(μ₀/μ₁) m_0`. -/
def twoLayerM1 (ω ε0 μ0 ε1 μ1 ξ η : ℝ) (q0 q1 : ℂ) : Fin 3 → ℂ :=
  nCross (((Real.sqrt (μ0 / μ1) : ℝ) : ℂ) • twoLayerM0 ω ε0 μ0 ε1 μ1 ξ η q0 q1)

/-- Eq. (45), layer 0 (`z ≥ 0`): `E_0 = √μ₀ (ik₀ S_{k₀}[j_0] - ∇ S_{k₀}[r_0] - ∇ × S_{k₀}[m_0])`,
`k₀ = ω √(ε₀μ₀)`, for the sources `r_j e^{i(ξx+ηy)}`, `q_j e^{i(ξx+ηy)}`. -/
def twoLayerE0 (ω ε0 μ0 ε1 μ1 ξ η : ℝ) (r0 r1 q0 q1 : ℂ) : Space → Fin 3 → ℂ :=
  debyeE (Real.sqrt μ0 : ℂ) (wavenumber ω ε0 μ0) (slpUp (wavenumber ω ε0 μ0) ξ η)
    (twoLayerJ0 ω ε0 μ0 ε1 μ1 ξ η r0 r1) (twoLayerM0 ω ε0 μ0 ε1 μ1 ξ η q0 q1) r0

/-- Eq. (45), layer 0: `H_0 = √ε₀ (ik₀ S_{k₀}[m_0] - ∇ S_{k₀}[q_0] + ∇ × S_{k₀}[j_0])`. -/
def twoLayerH0 (ω ε0 μ0 ε1 μ1 ξ η : ℝ) (r0 r1 q0 q1 : ℂ) : Space → Fin 3 → ℂ :=
  debyeH (Real.sqrt ε0 : ℂ) (wavenumber ω ε0 μ0) (slpUp (wavenumber ω ε0 μ0) ξ η)
    (twoLayerJ0 ω ε0 μ0 ε1 μ1 ξ η r0 r1) (twoLayerM0 ω ε0 μ0 ε1 μ1 ξ η q0 q1) q0

/-- Eq. (45), layer 1 (`z ≤ 0`): `E_1 = √μ₁ (ik₁ S_{k₁}[j_1] - ∇ S_{k₁}[r_1] - ∇ × S_{k₁}[m_1])`,
`k₁ = ω √(ε₁μ₁)`, with the kernel `e^{βz}` of eq. (47). -/
def twoLayerE1 (ω ε0 μ0 ε1 μ1 ξ η : ℝ) (r0 r1 q0 q1 : ℂ) : Space → Fin 3 → ℂ :=
  debyeE (Real.sqrt μ1 : ℂ) (wavenumber ω ε1 μ1) (slpDown (wavenumber ω ε1 μ1) ξ η)
    (twoLayerJ1 ω ε0 μ0 ε1 μ1 ξ η r0 r1) (twoLayerM1 ω ε0 μ0 ε1 μ1 ξ η q0 q1) r1

/-- Eq. (45), layer 1: `H_1 = √ε₁ (ik₁ S_{k₁}[m_1] - ∇ S_{k₁}[q_1] + ∇ × S_{k₁}[j_1])`. -/
def twoLayerH1 (ω ε0 μ0 ε1 μ1 ξ η : ℝ) (r0 r1 q0 q1 : ℂ) : Space → Fin 3 → ℂ :=
  debyeH (Real.sqrt ε1 : ℂ) (wavenumber ω ε1 μ1) (slpDown (wavenumber ω ε1 μ1) ξ η)
    (twoLayerJ1 ω ε0 μ0 ε1 μ1 ξ η r0 r1) (twoLayerM1 ω ε0 μ0 ε1 μ1 ξ η q0 q1) q1

/-- Eqs. (51), (53): the jumps `[f] = f_0 - f_1` (layer 0 minus layer 1) across `z = 0`, at the
point `p`, of the four interface quantities `S_0 ∇·E`, `n·εE`, `S_0 ∇·H`, `n·μH` of the scattered
field generated by the sources `s = (r_0, r_1, q_0, q_1)`, indexed as in eq. (53):
`inl 0, inl 1, inr 0, inr 1` for the rows and for `r_0, r_1, q_0, q_1`. -/
def twoLayerJumps (ω ε0 μ0 ε1 μ1 ξ η : ℝ) (s : Fin 2 ⊕ Fin 2 → ℂ) (p : Space) :
    Fin 2 ⊕ Fin 2 → ℂ :=
  Sum.elim
    ![laplaceSingleLayerOnMode ξ η (tangentialDivergence
          (twoLayerE0 ω ε0 μ0 ε1 μ1 ξ η (s (.inl 0)) (s (.inl 1)) (s (.inr 0)) (s (.inr 1)))) p -
        laplaceSingleLayerOnMode ξ η (tangentialDivergence
          (twoLayerE1 ω ε0 μ0 ε1 μ1 ξ η (s (.inl 0)) (s (.inl 1)) (s (.inr 0)) (s (.inr 1)))) p,
      (ε0 : ℂ) * twoLayerE0 ω ε0 μ0 ε1 μ1 ξ η (s (.inl 0)) (s (.inl 1)) (s (.inr 0)) (s (.inr 1)) p 2 -
        (ε1 : ℂ) * twoLayerE1 ω ε0 μ0 ε1 μ1 ξ η (s (.inl 0)) (s (.inl 1)) (s (.inr 0)) (s (.inr 1)) p 2]
    ![laplaceSingleLayerOnMode ξ η (tangentialDivergence
          (twoLayerH0 ω ε0 μ0 ε1 μ1 ξ η (s (.inl 0)) (s (.inl 1)) (s (.inr 0)) (s (.inr 1)))) p -
        laplaceSingleLayerOnMode ξ η (tangentialDivergence
          (twoLayerH1 ω ε0 μ0 ε1 μ1 ξ η (s (.inl 0)) (s (.inl 1)) (s (.inr 0)) (s (.inr 1)))) p,
      (μ0 : ℂ) * twoLayerH0 ω ε0 μ0 ε1 μ1 ξ η (s (.inl 0)) (s (.inl 1)) (s (.inr 0)) (s (.inr 1)) p 2 -
        (μ1 : ℂ) * twoLayerH1 ω ε0 μ0 ε1 μ1 ξ η (s (.inl 0)) (s (.inl 1)) (s (.inr 0)) (s (.inr 1)) p 2]

/-- Eq. (53): the matrix of the linear system for `(r̂_0, r̂_1, q̂_0, q̂_1)` at the mode `(ξ, η)`.
Its column for a source is the vector of Fourier coefficients of the four jumps generated by that
source with unit amplitude; the coefficient is the value at the origin, where
`e^{i(ξx+ηy)} = 1`. -/
def twoLayerSystem (ω ε0 μ0 ε1 μ1 ξ η : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  fun i j => twoLayerJumps ω ε0 μ0 ε1 μ1 ξ η (Pi.single j 1) (pt 0 0 0) i

end Arxiv1310_4241


