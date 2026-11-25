-- Prove2me | Definitions.Def_Arxiv2606_14486_Basic
-- name    : Arxiv2606_14486_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T19:08:03.658156+00:00
-- url     : https://prove2.me/theorems/7da85d81-4697-4dad-b14c-98b49939ebe5
-- title:
--   Array-factor model of an RIS and the electromagnetic reciprocity integral
-- statement:
--   Objects of Sections II and III of Khankhoje and Kundu (2026).
--
--   1. **Steering vector (eq. 1).** A linear array has $n$ elements spaced $d$ along $x$. For wavenumber $k$ and an angle $\theta$ measured clockwise from $+z$, $a(\theta)=\big[1,e^{jkd\sin\theta},\dots,e^{jk(n-1)d\sin\theta}\big]^T$.
--   2. **Reflected wavefronts (eqs. 2, 3, 5).** Element $i$ reflects with coefficient $R_ie^{j\psi_i}$, and $\Psi$ is the vector of these coefficients. The reflected wavefront is the element-wise product $a(\alpha)\cdot\Psi\cdot a(\beta)$. The forward wavefront is $y=a(\theta_2)\cdot\Psi\cdot a(-\theta_1)$ and the reverse wavefront is $z=a(-\theta_3)\cdot\Psi'\cdot a(\theta_2)$.
--   3. **In phase.** A wavefront $v$ is in phase (it interferes constructively in its direction) if there is a single $\varphi\in\mathbb{R}$ with $v_i=|v_i|e^{j\varphi}$ for every $i$.
--   4. **Phase profiles (eqs. 4, 6).** The forward phase step is $\Delta\psi=kd(\sin\theta_1-\sin\theta_2)$. A linear profile is $\psi_i=c+(i-1)\Delta$, and eq. (6) is $\psi'_i=(i-1)\Delta\psi'$.
--   5. **Array factor and discrete beamforming (eqs. 9-11).** For weights $w$, $G(\alpha,\beta)=\sum_{i=1}^n w_i\exp\big(j(i-1)kd[\sin\alpha+\sin\beta]\big)$, so $G(-\theta_1,\theta_2)$ and $G(\theta_2,-\theta_1)$ both carry the exponent $(i-1)kd[\sin\theta_2-\sin\theta_1]$, as in eqs. (9) and (11). The weights $\tilde w$ solve eq. (10) if every $\tilde w_i$ lies in the finite set $\mathcal{B}$ of diode-state reflection coefficients and $|G(\alpha,\beta)|$ at $\tilde w$ is maximal among all such weight vectors.
--   6. **Time-harmonic fields (Section III).** Phasor fields $E,H:\mathbb{R}^3\to\mathbb{C}^3$ use the time dependence $e^{j\omega t}$. The curl is computed from Fréchet partial derivatives. A medium is reciprocal on a region if its permittivity and permeability tensors $\varepsilon(x),\mu(x)\in\mathbb{C}^{3\times3}$ are symmetric there. The fields are source-free on the region if they are differentiable there and satisfy $\nabla\times E=-j\omega\mu H$ and $\nabla\times H=j\omega\varepsilon E$.
--   7. **Reciprocity integral (eq. 12).** For a box $[a,b]\subset\mathbb{R}^3$, $\Psi=\oint_S(E_1\times H_2-E_2\times H_1)\cdot d\vec s$ over its boundary $S$ with the outward normal. The integral is written as the sum over the six faces, and the products carry no complex conjugation.
--
--   **Formalization Note** Elements are indexed from $0$, so the paper's factor $(i-1)$ is the index itself. The flux through the box boundary uses the face parametrisation of Mathlib's divergence theorem.
-- source:
--   Khankhoje and Kundu, Implications of the Reciprocity Theorem for Reconfigurable Intelligent Surfaces, arXiv:2606.14486v1 (2026), https://arxiv.org/abs/2606.14486, Sec. II-A eqs. (1)-(6), Sec. II-B eqs. (9)-(11), Sec. III eq. (12), Appendix A (bounding boxes)

import Mathlib

/-!
Khankhoje and Kundu, *Implications of the Reciprocity Theorem for Reconfigurable Intelligent
Surfaces*, arXiv:2606.14486v1 (2026): the array-factor model of Section II (steering vector,
reflected wavefronts, linear reflection-phase profiles, array factor and discrete beamforming
problem, eqs. (1)-(11)) and, for Section III, time-harmonic fields in a linear medium with
symmetric permittivity and permeability tensors and the reciprocity surface integral `Ψ` of
eq. (12) over a rectangular box.

Element indices: element `i : Fin n` is the paper's element `i + 1`, so the paper's factor
`(i - 1)` is `(i : ℕ)` here.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2606_14486

/-- Section II, eq. (1): the array steering vector
`a(θ) = [1, e^{jkd sin θ}, …, e^{jk(n-1)d sin θ}]ᵀ` of `n` elements spaced `d` along `x`, for
wavenumber `k` and angle `θ` measured clockwise from `+z`. -/
def steering (n : ℕ) (k d θ : ℝ) : Fin n → ℂ :=
  fun i => Complex.exp ((((i : ℕ) : ℝ) * k * d * Real.sin θ : ℝ) * Complex.I)

/-- Section II, after eq. (2): the vector `Ψ` of element-wise reflection coefficients
`R_i e^{jψ_i}`, with magnitudes `R_i` and reflection phases `ψ_i`. -/
def reflCoeffs {n : ℕ} (R ψ : Fin n → ℝ) : Fin n → ℂ :=
  fun i => (R i : ℂ) * Complex.exp ((ψ i : ℂ) * Complex.I)

/-- Section II, eqs. (2) and (5): the reflected wavefront `a(α) · Ψ · a(β)` (element-wise
products). Eq. (2) is `y = a(θ₂) · Ψ · a(-θ₁)`, i.e. `wavefront n k d θ₂ (-θ₁) (reflCoeffs R ψ)`; eq. (5) is
`z = a(-θ₃) · Ψ' · a(θ₂)`, i.e. `wavefront n k d (-θ₃) θ₂ (reflCoeffs R' ψ')`. -/
def wavefront (n : ℕ) (k d α β : ℝ) (c : Fin n → ℂ) : Fin n → ℂ :=
  fun i => steering n k d α i * c i * steering n k d β i

/-- Section II-A, before eq. (4): the entries of a wavefront are all in phase (constructive
interference in the corresponding direction): there is one phase `φ` with
`v_i = |v_i| e^{jφ}` for every element `i`. -/
def InPhase {n : ℕ} (v : Fin n → ℂ) : Prop :=
  ∃ φ : ℝ, ∀ i, v i = (‖v i‖ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)

/-- Section II-A, eq. (4): the inter-element phase step `Δψ = kd (sin θ₁ - sin θ₂)` for
beamforming from incidence angle `θ₁` to reflection angle `θ₂`. -/
def phaseStep (k d θ₁ θ₂ : ℝ) : ℝ := k * d * (Real.sin θ₁ - Real.sin θ₂)

/-- Section II-A, eqs. (4) and (6): a reflection-phase profile linear in the element index,
`ψ_i = c + (i - 1) Δ` (eq. (4) "up to a constant" `c`; eq. (6) is `c = 0`, `Δ = Δψ'`). -/
def linearPhases (n : ℕ) (c Δ : ℝ) : Fin n → ℝ := fun i => c + ((i : ℕ) : ℝ) * Δ

/-- Section II-B, eqs. (9) and (11): the array factor of weights `w`,
`∑_i w_i exp(j (i-1) kd [sin α + sin β])`. Eq. (9) is `G(-θ₁, θ₂)` with the forward weights
and eq. (11) is `G(θ₂, -θ₁)` with the reverse weights `τ`; both have the exponent
`(i-1) kd [sin θ₂ - sin θ₁]`, as printed. -/
def arrayFactor (n : ℕ) (k d α β : ℝ) (w : Fin n → ℂ) : ℂ :=
  ∑ i, w i * Complex.exp ((((i : ℕ) : ℝ) * k * d * (Real.sin α + Real.sin β) : ℝ) * Complex.I)

/-- Section II-B, eq. (10): `w` solves the discrete beamforming problem
`max_w |G(α, β)| subject to w ∈ 𝓑`, where every element's weight (field reflection
coefficient) lies in the finite set `𝓑` of diode-state coefficients. -/
def IsOptimalWeights (B : Finset ℂ) (n : ℕ) (k d α β : ℝ) (w : Fin n → ℂ) : Prop :=
  (∀ i, w i ∈ B) ∧
    ∀ w' : Fin n → ℂ, (∀ i, w' i ∈ B) → ‖arrayFactor n k d α β w'‖ ≤ ‖arrayFactor n k d α β w‖

/-- Section III, eq. (12): the partial derivative `∂_j F` at `x` of a complex scalar field on
`ℝ³`, as the Fréchet derivative in the `j`-th coordinate direction. -/
def pderiv (F : (Fin 3 → ℝ) → ℂ) (j : Fin 3) (x : Fin 3 → ℝ) : ℂ :=
  fderiv ℝ F x (Pi.single j 1)

/-- The curl `∇ × F` of a complex (phasor) vector field on `ℝ³`, used in the time-harmonic
Maxwell equations underlying eq. (12) (Harrington, Eq. 3-34, cited in Section III). -/
def curl (F : (Fin 3 → ℝ) → Fin 3 → ℂ) (x : Fin 3 → ℝ) : Fin 3 → ℂ :=
  ![pderiv (fun y => F y 2) 1 x - pderiv (fun y => F y 1) 2 x,
    pderiv (fun y => F y 0) 2 x - pderiv (fun y => F y 2) 0 x,
    pderiv (fun y => F y 1) 0 x - pderiv (fun y => F y 0) 1 x]

/-- Section I (citing Chew, Ch. 30) and Section III: on the region `V` the medium is linear and
reciprocal, i.e. described by permittivity and permeability tensors `ε(x)`, `μ(x)` (complex,
so lossy media are allowed) that are symmetric matrices. -/
def IsReciprocalMedium (eps mu : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (V : Set (Fin 3 → ℝ)) : Prop :=
  ∀ x ∈ V, (eps x).transpose = eps x ∧ (mu x).transpose = mu x

/-- Section III, eq. (12): the phasor fields `(E, H)` (time dependence `e^{jωt}`, as in
Section II) satisfy the source-free time-harmonic Maxwell equations
`∇ × E = -jω μ H`, `∇ × H = jω ε E` at every point of `V`, where both fields are
differentiable ("a volume ... does not contain any impressed sources"). -/
def IsSourceFreeMaxwellOn (ω : ℝ) (eps mu : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (V : Set (Fin 3 → ℝ)) (E H : (Fin 3 → ℝ) → Fin 3 → ℂ) : Prop :=
  ∀ x ∈ V, DifferentiableAt ℝ E x ∧ DifferentiableAt ℝ H x ∧
    curl E x = (-(Complex.I * ω)) • (mu x).mulVec (H x) ∧
    curl H x = (Complex.I * ω) • (eps x).mulVec (E x)

/-- Section III and Appendix A: the open rectangular box `∏_i (a_i, b_i)`; the paper's
surface `S` enclosing the RIS is the boundary of such a bounding box. -/
def boxInterior (a b : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ fun i => Set.Ioo (a i) (b i)

/-- The outward flux `∮_S F · ds` of a complex vector field through the boundary `S` of the
box `[a, b] ⊂ ℝ³`: for each coordinate `i`, the integral of `F_i` over the face `x_i = b_i`
minus the integral over the face `x_i = a_i`, each face parametrised by the two remaining
coordinates (the face convention of Mathlib's divergence theorem). -/
def boxFlux (a b : Fin 3 → ℝ) (F : (Fin 3 → ℝ) → Fin 3 → ℂ) : ℂ :=
  ∑ i : Fin 3,
    ((∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i) -
      ∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i)

/-- Section III, eq. (12): the reciprocity integral
`Ψ = ∮_S (E₁ × H₂ - E₂ × H₁) · ds` over the boundary of the box `[a, b]`, where `(E₁, H₁)` are
the fields with the transmitter at `A` and `(E₂, H₂)` those with the transmitter at `B`
(products without complex conjugation). -/
def reciprocityIntegral (a b : Fin 3 → ℝ) (E₁ H₁ E₂ H₂ : (Fin 3 → ℝ) → Fin 3 → ℂ) : ℂ :=
  boxFlux a b fun x => crossProduct (E₁ x) (H₂ x) - crossProduct (E₂ x) (H₁ x)

end Arxiv2606_14486


