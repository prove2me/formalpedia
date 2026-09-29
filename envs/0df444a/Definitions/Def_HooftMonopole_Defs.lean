-- Prove2me | Definitions.Def_HooftMonopole_Defs
-- name    : HooftMonopole_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T19:50:58.665819+00:00
-- url     : https://prove2.me/theorems/7cb8796b-7a44-4285-9ee8-450aea374ea6
-- title:
--   't Hooft 1974: static Georgi–Glashow model, hedgehog ansatz and reduced energy
-- statement:
--   Definitions for the static SO(3) Georgi–Glashow model of 't Hooft (1974), Sects. 1–2.
--
--   Space and isospin space are both $\mathbb R^3$, indices $i,j,a,b,c \in \{1,2,3\}$ (in Lean $\{0,1,2\}$), repeated indices summed, $\varepsilon_{abc}$ the Levi-Civita symbol. A **Higgs field** is a map $Q : \mathbb R^3 \to \mathbb R^3$, $x \mapsto (Q_a(x))_a$, and a static **gauge field** in the gauge $W_4 = 0$ is a family $W_i : \mathbb R^3 \to \mathbb R^3$, $x \mapsto (W^a_i(x))_a$. For parameters $e, \lambda, F \in \mathbb R$:
--
--   1. **Covariant derivative and field strength** (2.2):
--   $$D_iQ_a = \partial_iQ_a + e\,\varepsilon_{abc}W^b_iQ_c,\qquad G^a_{ij} = \partial_iW^a_j - \partial_jW^a_i + e\,\varepsilon_{abc}W^b_iW^c_j .$$
--   2. **Energy density and energy** of a static configuration (minus the Lagrangian (2.1), with $\mu^2 = -\tfrac12\lambda F^2$ and the vacuum constant added as in (2.9)):
--   $$\mathcal E = \tfrac14G^a_{ij}G^a_{ij} + \tfrac12D_iQ_aD_iQ_a + \tfrac18\lambda(Q_aQ_a - F^2)^2,\qquad E = \int_{\mathbb R^3}\mathcal E\,d^3x .$$
--   3. **Static solution**: $Q$ and all $W_i$ are $C^\infty$, $\mathcal E$ is integrable, and $\frac{d}{dt}\big|_{t=0}E[Q + t\,\delta Q,\ W + t\,\delta W] = 0$ for all $C^\infty$ compactly supported $\delta Q$, $\delta W_i$.
--   4. **Electromagnetic tensor** (2.17) $F_{ij} = |Q|^{-1}Q_aG^a_{ij} - (e|Q|^3)^{-1}\varepsilon_{abc}Q_a(D_iQ_b)(D_jQ_c)$ and **magnetic field** $B_k = \tfrac12\varepsilon_{kij}F_{ij}$.
--   5. **Spherically symmetric ansatz** (2.8): $Q_a(x) = x_a\,Q(|x|)$, $W^a_i(x) = \varepsilon_{iab}x_b\,W(|x|)$ for profiles $Q, W : \mathbb R \to \mathbb R$.
--   6. **Radial energy integrand** (minus the bracket of (2.9)):
--   $$r^2W'^2 + 4rWW' + 6W^2 + 2er^2W^3 + \tfrac12e^2r^4W^4 + \tfrac12r^2Q'^2 + rQQ' + \tfrac32Q^2 + 2er^2WQ^2 + e^2r^4W^2Q^2 - \tfrac14\lambda F^2r^2Q^2 + \tfrac18\lambda r^4Q^4 + \tfrac18\lambda F^4 .$$
--   7. **Lagrange equation** (2.13) for $W$ at radius $r$:
--   $$\frac{d}{dr}\Big(2r^4\frac{dW}{dr} + 4r^3W\Big) = r^2\Big[4r\frac{dW}{dr} + 12W + 6er^2W^2 + 2e^2r^4W^3 + 2er^2Q^2 + 2e^2r^4WQ^2\Big].$$
--   8. The SU(2) matrix (1.4) $\Omega(\theta,\varphi) = \cos\tfrac\theta2\,\mathrm{diag}(e^{i\varphi}, e^{-i\varphi}) + \sin\tfrac\theta2\begin{pmatrix}0&i\\ i&0\end{pmatrix}$ and the Pauli matrices $\sigma_1,\sigma_2,\sigma_3$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** $\mathbb R^3$ is `EuclideanSpace ℝ (Fin 3)` with Lebesgue measure; $\varepsilon_{abc} = (a-b)(b-c)(c-a)/2$ on $\{0,1,2\}$; $\partial_i f(x)$ is the Fréchet derivative of $f$ at $x$ applied to the $i$-th basis vector (zero if $f$ is not differentiable at $x$). In $F_{ij}$, Lean's $1/0 = 0$ applies at zeros of $Q$. The integral is a Bochner integral ($0$ if the integrand is not integrable).
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, Sect. 1 eq. (1.4); Sect. 2 eqs. (2.1)-(2.3), (2.8), (2.9), (2.13), (2.17)

import Mathlib

/-!
# 't Hooft (1974), "Magnetic monopoles in unified gauge theories" — basic definitions

Static Georgi–Glashow (SO(3) Yang–Mills–Higgs) model of Sect. 2 of
G. 't Hooft, Nucl. Phys. B79 (1974) 276–284.

* Physical space and isospin space are both modelled by `EuclideanSpace ℝ (Fin 3)`.
* A Higgs field is a map `Q : Space → Space`, `Q x a = Q_a(x)`.
* A static gauge field in the temporal gauge (`W_4 = 0`) is `W : Fin 3 → Space → Space`,
  `W i x a = W^a_i(x)`.
-/

namespace HooftMonopole

open MeasureTheory

noncomputable section

/-- Physical space `ℝ³` (also used for isospin space). -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The Levi-Civita symbol `ε_{abc}` on `{0,1,2}`: `+1` on even permutations of `(0,1,2)`,
`-1` on odd permutations, `0` if two indices coincide. -/
def levi (a b c : Fin 3) : ℝ :=
  (((a : ℕ) : ℝ) - (b : ℕ)) * (((b : ℕ) : ℝ) - (c : ℕ)) * (((c : ℕ) : ℝ) - (a : ℕ)) / 2

/-- Partial derivative `∂_i f(x)` of a vector-valued map on space. -/
noncomputable def partialDeriv (f : Space → Space) (i : Fin 3) (x : Space) : Space :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- Covariant derivative of the Higgs triplet, eq. (2.2):
`D_i Q_a = ∂_i Q_a + e ε_{abc} W^b_i Q_c`. -/
noncomputable def covDeriv (e : ℝ) (Q : Space → Space) (W : Fin 3 → Space → Space)
    (i : Fin 3) (x : Space) (a : Fin 3) : ℝ :=
  partialDeriv Q i x a + e * ∑ b, ∑ c, levi a b c * W i x b * Q x c

/-- Non-abelian field strength, eq. (2.2):
`G^a_{ij} = ∂_i W^a_j − ∂_j W^a_i + e ε_{abc} W^b_i W^c_j`. -/
noncomputable def fieldStrength (e : ℝ) (W : Fin 3 → Space → Space)
    (i j : Fin 3) (x : Space) (a : Fin 3) : ℝ :=
  partialDeriv (W j) i x a - partialDeriv (W i) j x a
    + e * ∑ b, ∑ c, levi a b c * W i x b * W j x c

/-- `Q_a Q_a`, the squared length of the Higgs isovector at `x`. -/
def higgsNormSq (Q : Space → Space) (x : Space) : ℝ := ∑ a, (Q x a) ^ 2

/-- Static energy density of the Lagrangian (2.1) (i.e. minus the Lagrangian density of a
static configuration with `W_4 = 0`), with `μ² = -½ λ F²` as in (2.3) and with the constant
`⅛ λ F⁴` added so that the vacuum has zero energy (as in (2.9)):
`¼ G^a_{ij} G^a_{ij} + ½ D_i Q_a D_i Q_a + ⅛ λ (Q_a Q_a − F²)²`. -/
noncomputable def energyDensity (e lam F : ℝ) (Q : Space → Space)
    (W : Fin 3 → Space → Space) (x : Space) : ℝ :=
  (1 / 4) * ∑ i, ∑ j, ∑ a, (fieldStrength e W i j x a) ^ 2
    + (1 / 2) * ∑ i, ∑ a, (covDeriv e Q W i x a) ^ 2
    + (lam / 8) * (higgsNormSq Q x - F ^ 2) ^ 2

/-- Total static energy `E = ∫ energyDensity d³x` (Lebesgue measure on `ℝ³`). -/
noncomputable def energy (e lam F : ℝ) (Q : Space → Space) (W : Fin 3 → Space → Space) : ℝ :=
  ∫ x, energyDensity e lam F Q W x

/-- A regular, finite-energy, static solution of the field equations of (2.1) in the gauge
`W_4 = 0`: the fields are `C^∞`, the energy density is integrable, and the energy is
stationary under every smooth compactly supported variation of `Q` and of the spatial
components `W_i`. -/
def IsStaticSolution (e lam F : ℝ) (Q : Space → Space) (W : Fin 3 → Space → Space) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Q ∧ (∀ i, ContDiff ℝ (⊤ : ℕ∞) (W i)) ∧
    Integrable (energyDensity e lam F Q W) ∧
    ∀ (δQ : Space → Space) (δW : Fin 3 → Space → Space),
      ContDiff ℝ (⊤ : ℕ∞) δQ → HasCompactSupport δQ →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (δW i)) → (∀ i, HasCompactSupport (δW i)) →
      HasDerivAt
        (fun t : ℝ => energy e lam F (fun x => Q x + t • δQ x) (fun i x => W i x + t • δW i x))
        0 0

/-- 't Hooft's gauge-invariant electromagnetic field tensor, eq. (2.17):
`F_{ij} = |Q|⁻¹ Q_a G^a_{ij} − (e |Q|³)⁻¹ ε_{abc} Q_a (D_i Q_b)(D_j Q_c)`.
(Where `Q = 0` Lean's convention `1/0 = 0` applies; the quantity is only meaningful where
`Q ≠ 0`.) -/
noncomputable def emField (e : ℝ) (Q : Space → Space) (W : Fin 3 → Space → Space)
    (i j : Fin 3) (x : Space) : ℝ :=
  (1 / Real.sqrt (higgsNormSq Q x)) * ∑ a, Q x a * fieldStrength e W i j x a
    - (1 / (e * Real.sqrt (higgsNormSq Q x) ^ 3)) *
      ∑ a, ∑ b, ∑ c, levi a b c * Q x a * covDeriv e Q W i x b * covDeriv e Q W j x c

/-- Magnetic field `B_k = ½ ε_{kij} F_{ij}` of the electromagnetic tensor (2.17). -/
noncomputable def magneticField (e : ℝ) (Q : Space → Space) (W : Fin 3 → Space → Space)
    (x : Space) (k : Fin 3) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, levi k i j * emField e Q W i j x

/-- Spherically symmetric Higgs field of ansatz (2.8): `Q_a(x) = x_a Q(|x|)`. -/
noncomputable def hedgehogHiggs (q : ℝ → ℝ) : Space → Space :=
  fun x => q ‖x‖ • x

/-- Spherically symmetric gauge field of ansatz (2.8): `W^a_i(x) = ε_{iab} x_b W(|x|)`. -/
noncomputable def hedgehogGauge (w : ℝ → ℝ) : Fin 3 → Space → Space :=
  fun i x => w ‖x‖ • ∑ a, (∑ b, levi i a b * x b) • EuclideanSpace.single a (1 : ℝ)

/-- Minus the bracket of eq. (2.9): the radial energy integrand of the ansatz (2.8), so that
the energy is `4π ∫₀^∞ r² · radialEnergyIntegrand e λ F W Q r dr`. -/
noncomputable def radialEnergyIntegrand (e lam F : ℝ) (W Q : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ 2 * (deriv W r) ^ 2 + 4 * r * W r * deriv W r + 6 * W r ^ 2 + 2 * e * r ^ 2 * W r ^ 3
    + (1 / 2) * e ^ 2 * r ^ 4 * W r ^ 4 + (1 / 2) * r ^ 2 * (deriv Q r) ^ 2
    + r * Q r * deriv Q r + (3 / 2) * Q r ^ 2 + 2 * e * r ^ 2 * W r * Q r ^ 2
    + e ^ 2 * r ^ 4 * W r ^ 2 * Q r ^ 2 - (1 / 4) * lam * F ^ 2 * r ^ 2 * Q r ^ 2
    + (1 / 8) * lam * r ^ 4 * Q r ^ 4 + (1 / 8) * lam * F ^ 4

/-- The Lagrange equation (2.13) for the radial profile `W`, at radius `r`:
`d/dr (2r⁴ W' + 4r³ W) = r² [4r W' + 12 W + 6e r² W² + 2e² r⁴ W³ + 2e r² Q² + 2e² r⁴ W Q²]`. -/
def radialWEquation (e : ℝ) (W Q : ℝ → ℝ) (r : ℝ) : Prop :=
  deriv (fun s => 2 * s ^ 4 * deriv W s + 4 * s ^ 3 * W s) r =
    r ^ 2 * (4 * r * deriv W r + 12 * W r + 6 * e * r ^ 2 * W r ^ 2
      + 2 * e ^ 2 * r ^ 4 * W r ^ 3 + 2 * e * r ^ 2 * Q r ^ 2 + 2 * e ^ 2 * r ^ 4 * W r * Q r ^ 2)

/-- The SU(2) gauge transformation of eq. (1.4):
`Ω(θ,φ) = cos(θ/2) diag(e^{iφ}, e^{-iφ}) + sin(θ/2) [[0, i], [i, 0]]`. -/
noncomputable def omegaMatrix (θ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos (θ / 2) : ℂ) • !![Complex.exp (Complex.I * φ), 0; 0, Complex.exp (-(Complex.I * φ))]
    + (Real.sin (θ / 2) : ℂ) • !![0, Complex.I; Complex.I, 0]

/-- The Pauli matrices `σ₁, σ₂, σ₃` (indexed by `0, 1, 2`). -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

end

end HooftMonopole


