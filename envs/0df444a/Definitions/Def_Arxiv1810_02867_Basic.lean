-- Prove2me | Definitions.Def_Arxiv1810_02867_Basic
-- name    : Arxiv1810_02867_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T05:15:13.091913+00:00
-- url     : https://prove2.me/theorems/1f1f2b78-b96b-4d94-b85c-0fbbfacfd5c6
-- title:
--   Unified wave equations, reciprocity domains and slowness-domain decomposition for non-reciprocal media
-- statement:
--   Objects of Sections II-III and Appendices A-B of Wapenaar and Reinicke (2020).
--
--   1. **Coordinates and derivatives.** Points of the plane of propagation are $\mathbf x=(x_1,x_3)$ and points of space are $(x_1,x_2,x_3)$. $\partial_j$ is the partial derivative along the $j$-th coordinate line and $\partial_t$ the time derivative. A quantity is $x_2$-independent if it is unchanged when $x_2$ changes, and such a quantity is restricted to the plane $x_2=0$. $\delta_{ij}$ is the Kronecker delta and $\epsilon_{ijk}$ the alternating tensor.
--   2. **Unified equations (eqs. (1)-(2)).** For time-independent parameters $\alpha(\mathbf x)$, $\beta_{rs}(\mathbf x)$, $\gamma_r(\mathbf x)$ with $r,s\in\{1,3\}$: $\alpha\partial_tP+(\partial_r+\gamma_r\partial_t)Q_r=B$ and $(\partial_s+\gamma_s\partial_t)P+\beta_{su}\partial_tQ_u=C_s$. $\vartheta_{rs}$ is the inverse of $\beta_{rs}$. In one dimension $c=(\alpha\beta)^{-1/2}$ and $P^\pm(x_1,t)=S(t\mp\frac{x_1}{c}(1\pm\gamma c))$.
--   3. **Frequency domain (eqs. (8)-(9)).** A state consists of complex fields $P,Q_r$, complex sources $B,C_r$ and real parameters $\alpha,\beta_{rs},\gamma_r$ satisfying $-i\omega\alpha P+(\partial_r-i\omega\gamma_r)Q_r=B$ and $(\partial_s-i\omega\gamma_s)P-i\omega\beta_{su}Q_u=C_s$ on a set $\mathbb D$. A state is regular when $P,Q$ are $C^1$ and the sources and parameters are continuous.
--   4. **Domains for Gauss's theorem.** A bounded open set $\mathbb D\subset\mathbb R^2$, with a finite boundary measure carried by $\partial\mathbb D$ and a unit normal $\mathbf n$ on $\partial\mathbb D$, such that $\oint_{\partial\mathbb D}F_rn_r\,\mathrm d\mathbf x=\int_{\mathbb D}\partial_rF_r\,\mathrm d\mathbf x$ for every $C^1$ field $F:\mathbb R^2\to\mathbb C^2$.
--   5. **Electromagnetic waves (A.1).** These are the Maxwell equations (A1)-(A2) and the constitutive relations $D_i=\varepsilon_{ij}E_j+\eta_{ij}B_j$, $H_k=\theta_{kl}E_l+\nu_{kl}B_l$. They are reorganised with $\varepsilon^o_{il}=\varepsilon_{il}-\eta_{ij}\mu_{jk}\theta_{kl}$, $\xi_{ik}=\eta_{ij}\mu_{jk}$ and $\zeta_{jl}=-\mu_{jk}\theta_{kl}$. The resulting first-order system is (A15)-(A16), and the TE and TM systems in the $(x_1,x_3)$-plane are (A17)-(A22).
--   6. **Elastodynamic waves (A.2).** These are the momentum and deformation equations (A23)-(A24) and the Willis relations $m_i=\rho_{ik}v_k+S^{(2)}_{ikl}e_{kl}$, $\tau_{mn}=S^{(1)}_{mnp}v_p+c_{mnpq}e_{pq}$. They are reorganised with $\rho^o_{ip}=\rho_{ip}-S^{(2)}_{ikl}s_{klmn}S^{(1)}_{mnp}$, $\xi_{imn}=-S^{(2)}_{ikl}s_{klmn}$ and $\zeta_{klp}=s_{klmn}S^{(1)}_{mnp}$. The resulting system is (A43)-(A44), and the SH system is (A45)-(A47).
--   7. **Acoustic waves (A.3).** $\kappa=1/K$, $\zeta_p=\frac13\kappa S^{(1)}_{mmp}$, $\rho^o_{ip}=\rho_{ip}-\frac19\kappa S^{(2)}_{ill}S^{(1)}_{mmp}$ and $\xi_i=-\frac13\kappa S^{(2)}_{ill}$. The resulting system is (A66)-(A67), and the 2D acoustic system is (A68)-(A70).
--   8. **Matrix-vector equation (B.1).** $d=\vartheta_{33}^{-1}\vartheta_{13}$, $b_s=\vartheta_{1s}-\vartheta_{13}\vartheta_{33}^{-1}\vartheta_{3s}$. Along a depth level, $\mathcal A_{11}=i\omega\gamma_3-d(\partial_1-i\omega\gamma_1)$, $\mathcal A_{12}=i\omega\vartheta_{33}^{-1}$, $\mathcal A_{21}=i\omega\alpha-\frac1{i\omega}(\partial_1-i\omega\gamma_1)b_1(\partial_1-i\omega\gamma_1)$ and $\mathcal A_{22}=i\omega\gamma_3-(\partial_1-i\omega\gamma_1)d$, where each differential operator acts on all factors to its right. The source vector is $(C^o,B^o)=(dC_1+C_3,\ B+\frac1{i\omega}(\partial_1-i\omega\gamma_1)b_1C_1)$.
--   9. **Slowness domain (B.2-B.3).** The quantities are $s_3^2=\vartheta_{33}^{-1}(\alpha-b_1(s_1-\gamma_1)^2)$, the matrix $\tilde{\mathcal A}$ of (B21), and $s_3$ of (B28) (real for $(s_1-\gamma_1)^2\le\alpha/b_1$, imaginary otherwise). They also include $\lambda^\pm=s_3\pm\{\gamma_3-d(s_1-\gamma_1)\}$, $\tilde{\mathcal H}=\mathrm{diag}(i\omega\lambda^+,-i\omega\lambda^-)$, the matrix $\tilde{\mathcal L}$ of (B25) and the printed inverse of (B26), and the matrices $\mathbf N,\mathbf K,\mathbf J$ of (B31), (B39).
--
--   **Formalization Note** Indices $r,s\in\{1,3\}$ are $0,1$ in Lean and spatial indices $1,2,3$ are $0,1,2$. Partial derivatives are derivatives along coordinate lines. The inverse $\vartheta$ is Mathlib's matrix inverse. $\sqrt{\vartheta_{33}s_3}$ is the principal complex square root. The boundary integral $\oint_{\partial\mathbb D}\cdots n_r\,\mathrm d\mathbf x$ is an integral against the boundary measure of a domain on which Gauss's theorem holds. Every bounded Lipschitz domain with arc length and outward unit normal is such a domain.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), Sections II-III (eqs. (1)-(16)), Appendix A.1-A.4 (eqs. (A1)-(A78), Table 1), Appendix B.1-B.3 (eqs. (B1)-(B39))

import Mathlib

/-!
Wapenaar and Reinicke, *Unified wave field retrieval and imaging method for inhomogeneous
non-reciprocal media*, arXiv:1810.02867v2 (2020): the unified first-order equations and their
time- and frequency-domain forms (Sections II-III, Appendix A.4, Appendix B.1), the
electromagnetic, elastodynamic and acoustic systems they unify (Appendix A.1-A.3), domains for
Gauss's theorem (Section III), and the slowness-domain operator matrix and its decomposition
(Appendix B.2-B.3).

Index conventions. Points of the plane are `Fin 2 → ℝ` with index `0` for `x₁` and `1` for
`x₃`; the paper's indices `r, s, u ∈ {1, 3}` are `0, 1`. Points of space are `Fin 3 → ℝ` and
the paper's indices `1, 2, 3` are `0, 1, 2`. Time-domain fields are real functions of
`(x, t)`; frequency-domain fields are complex functions of `x` at a fixed angular frequency `ω`.
-/

open MeasureTheory

noncomputable section

namespace Arxiv1810_02867

/-- A point `x = (x₁, x₃)` of the plane of propagation (Section II): index `0` is `x₁`,
index `1` is `x₃`. -/
abbrev Plane := Fin 2 → ℝ

/-- A point `x = (x₁, x₂, x₃)` of space (Appendix A): indices `0, 1, 2` are `x₁, x₂, x₃`. -/
abbrev Space := Fin 3 → ℝ

/-- The point `(x₁, x₃)` of the plane (Section II). -/
def pt (x1 x3 : ℝ) : Plane := ![x1, x3]

/-- The partial derivative `∂ⱼ f(x)` (Section II: "operator `∂_r` stands for differentiation in
the `x_r` direction"), the derivative of `f` along the `j`-th coordinate line through `x`. -/
def pd {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : Fin n)
    (f : (Fin n → ℝ) → E) (x : Fin n → ℝ) : E :=
  deriv (fun y : ℝ => f (Function.update x j y)) (x j)

/-- The spatial partial derivative `∂ⱼ f(x, t)` of a time-dependent field (Section II). -/
def pdx {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℝ → ℝ) (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  pd j (fun y => f y t) x

/-- The temporal derivative `∂_t f(x, t)` (Section II). -/
def pdt {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ) (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  deriv (fun s => f x s) t

/-- The component `F_i` of a vector- or tensor-valued time-dependent field `F`. -/
def cmp {X ι : Type*} (F : X → ℝ → ι → ℝ) (i : ι) : X → ℝ → ℝ :=
  fun x t => F x t i

/-- Appendix A: the fields, sources and medium parameters are independent of the
`x₂`-coordinate. -/
def IndepX2 {X : Type*} (f : Space → X) : Prop :=
  ∀ (x : Space) (s : ℝ), f (Function.update x 1 s) = f x

/-- The embedding `(x₁, x₃) ↦ (x₁, 0, x₃)` of the plane of propagation into space
(Appendix A: wave propagation in the `(x₁, x₃)`-plane). -/
def emb (y : Plane) : Space := ![y 0, 0, y 1]

/-- The restriction to the `(x₁, x₃)`-plane of an `x₂`-independent quantity of Appendix A. -/
def restr {X : Type*} (f : Space → X) : Plane → X := fun y => f (emb y)

/-- The Kronecker delta `δ_{ij}` (Appendix A). -/
def kd {n : ℕ} (i j : Fin n) : ℝ := if i = j then 1 else 0

/-- Appendix A.1: the alternating (Levi-Civita) tensor, `ε₁₂₃ = ε₃₁₂ = ε₂₃₁ = 1`,
`ε₂₁₃ = ε₃₂₁ = ε₁₃₂ = -1`, all other components zero. -/
def levi (i j k : Fin 3) : ℝ :=
  if (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 2 ∧ j = 0 ∧ k = 1) ∨ (i = 1 ∧ j = 2 ∧ k = 0) then 1
  else if (i = 1 ∧ j = 0 ∧ k = 2) ∨ (i = 2 ∧ j = 1 ∧ k = 0) ∨ (i = 0 ∧ j = 2 ∧ k = 1) then -1
  else 0

/-! ### Unified equations (Section II, Appendix A.4) -/

/-- Appendix A.4: the inverse `ϑ_{rs}` of the symmetric `2 × 2` tensor `β_{rs}`,
`ϑ_{rs} β_{su} = δ_{ru}` (eqs. (A73)-(A77)). -/
def thetaOf (b : Fin 2 → Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (Matrix.of b)⁻¹

/-- Eq. (1)-(2): the operator `∂_r + γ_r ∂_t` applied to a time-dependent field on the plane. -/
def Dg (gamma : Plane → Fin 2 → ℝ) (r : Fin 2) (f : Plane → ℝ → ℝ) : Plane → ℝ → ℝ :=
  fun x t => pdx r f x t + gamma x r * pdt f x t

/-- Eqs. (1)-(2) (= (A71)-(A72)): the unified first-order equations
`α ∂_t P + (∂_r + γ_r ∂_t) Q_r = B` and `(∂_s + γ_s ∂_t) P + β_{su} ∂_t Q_u = C_s`
for a scalar field `P`, a vector field `Q`, sources `B, C` and time-independent medium
parameters `α, β, γ`, holding at every point and time. -/
def UnifiedEqs (alpha : Plane → ℝ) (beta : Plane → Fin 2 → Fin 2 → ℝ)
    (gamma : Plane → Fin 2 → ℝ) (P : Plane → ℝ → ℝ) (Q : Plane → ℝ → Fin 2 → ℝ)
    (B : Plane → ℝ → ℝ) (C : Plane → ℝ → Fin 2 → ℝ) : Prop :=
  ∀ x t, alpha x * pdt P x t + ∑ r, Dg gamma r (cmp Q r) x t = B x t ∧
    ∀ s, Dg gamma s P x t + ∑ u, beta x s u * pdt (cmp Q u) x t = C x t s

/-- Section II, eq. (5): the operator `∂₁ + γ ∂_t` of the one-dimensional equation, acting on
a field `P(x₁, t)`. -/
def D1g (gamma : ℝ) (P : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x t => deriv (fun y => P y t) x + gamma * deriv (fun s => P x s) t

/-- Section II, eq. (6): `c = (αβ)^{-1/2}`, the propagation velocity of the corresponding
reciprocal medium. -/
def refVel (alpha beta : ℝ) : ℝ := (alpha * beta) ^ (-(1 / 2 : ℝ))

/-- Section II, eq. (6): `P^±(x₁, t) = S(t ∓ (x₁/c)(1 ± γc))` with `c = (αβ)^{-1/2}`;
`oneWay true` is `P⁺` and `oneWay false` is `P⁻`. -/
def oneWay (plus : Bool) (alpha beta gamma : ℝ) (S : ℝ → ℝ) (x t : ℝ) : ℝ :=
  if plus then S (t - x / refVel alpha beta * (1 + gamma * refVel alpha beta))
  else S (t + x / refVel alpha beta * (1 - gamma * refVel alpha beta))

/-! ### Frequency domain and reciprocity theorems (Section III) -/

/-- Section III: one state of the space-frequency domain equations (8)-(9): the fields
`P, Q_r`, the sources `B, C_r` and the real (lossless) medium parameters `α, β_{rs}, γ_r`. -/
structure FreqState where
  /-- The scalar field `P(x, ω)`. -/
  P : Plane → ℂ
  /-- The vector field `Q_r(x, ω)`. -/
  Q : Plane → Fin 2 → ℂ
  /-- The source `B(x, ω)`. -/
  B : Plane → ℂ
  /-- The source `C_r(x, ω)`. -/
  C : Plane → Fin 2 → ℂ
  /-- The medium parameter `α(x)`. -/
  alpha : Plane → ℝ
  /-- The medium parameter `β_{rs}(x)`. -/
  beta : Plane → Fin 2 → Fin 2 → ℝ
  /-- The medium parameter `γ_r(x)`. -/
  gamma : Plane → Fin 2 → ℝ

/-- Eqs. (8)-(9) (= (B1)-(B2)) on a set `D`:
`-iωαP + (∂_r - iωγ_r) Q_r = B` and `(∂_s - iωγ_s) P - iωβ_{su} Q_u = C_s`. -/
def FreqEqs (ω : ℝ) (S : FreqState) (D : Set Plane) : Prop :=
  ∀ x ∈ D,
    (-(Complex.I * ω) * S.alpha x * S.P x +
        ∑ r, (pd r (fun y => S.Q y r) x - Complex.I * ω * S.gamma x r * S.Q x r) = S.B x) ∧
    ∀ s, pd s S.P x - Complex.I * ω * S.gamma x s * S.P x -
        Complex.I * ω * ∑ u, (S.beta x s u : ℂ) * S.Q x u = S.C x s

/-- Section III, standing smoothness convention for the reciprocity theorems: the wave fields
are continuously differentiable, and the sources and medium parameters are continuous. -/
def FreqState.Regular (S : FreqState) : Prop :=
  ContDiff ℝ 1 S.P ∧ ContDiff ℝ 1 S.Q ∧ Continuous S.B ∧ Continuous S.C ∧
    Continuous S.alpha ∧ Continuous S.beta ∧ Continuous S.gamma

/-- Section III: a bounded open domain `𝔻` of the plane with boundary `∂𝔻`, the boundary
(arc-length) measure `σ` carried by `∂𝔻` and the outward pointing unit normal `n = (n₁, n₃)`,
for which the theorem of Gauss `∮_{∂𝔻} F_r n_r dx = ∫_𝔻 ∂_r F_r dx` holds for every
continuously differentiable vector field `F`. -/
structure GaussDomain where
  /-- The domain `𝔻`. -/
  D : Set Plane
  /-- The boundary measure on `∂𝔻`. -/
  sigma : Measure Plane
  /-- The outward pointing normal vector `n`. -/
  normal : Plane → Fin 2 → ℝ
  isOpen_D : IsOpen D
  isBounded_D : Bornology.IsBounded D
  isFiniteMeasure_sigma : IsFiniteMeasure sigma
  sigma_compl_frontier : sigma (frontier D)ᶜ = 0
  normal_unit : ∀ x ∈ frontier D, ∑ r, normal x r ^ 2 = 1
  gauss : ∀ F : Plane → Fin 2 → ℂ, ContDiff ℝ 1 F →
    ∫ x, ∑ r, F x r * (normal x r : ℂ) ∂sigma = ∫ x in D, ∑ r, pd r (fun y => F y r) x

/-! ### Electromagnetic waves (Appendix A.1) -/

/-- Eqs. (A1)-(A2): the Maxwell equations `∂_t D_i - ε_{ijk} ∂_j H_k = -J^e_i` and
`∂_t B_j + ε_{jkl} ∂_k E_l = -J^m_j`. -/
def MaxwellEqs (D B E H Je Jm : Space → ℝ → Fin 3 → ℝ) : Prop :=
  ∀ x t,
    (∀ i, pdt (cmp D i) x t - ∑ j, ∑ k, levi i j k * pdx j (cmp H k) x t = -Je x t i) ∧
    ∀ j, pdt (cmp B j) x t + ∑ k, ∑ l, levi j k l * pdx k (cmp E l) x t = -Jm x t j

/-- Eqs. (A3)-(A4): the low-frequency effective constitutive relations
`D_i = ε_{ij} E_j + η_{ij} B_j`, `H_k = θ_{kl} E_l + ν_{kl} B_l`. -/
def EMConstitutive (eps eta theta nu : Space → Fin 3 → Fin 3 → ℝ)
    (E B D H : Space → ℝ → Fin 3 → ℝ) : Prop :=
  ∀ x t, (∀ i, D x t i = ∑ j, eps x i j * E x t j + ∑ j, eta x i j * B x t j) ∧
    ∀ k, H x t k = ∑ l, theta x k l * E x t l + ∑ l, nu x k l * B x t l

/-- Eq. (A11): `ε°_{il} = ε_{il} - η_{ij} μ_{jk} θ_{kl}`. -/
def epsO (eps eta mu theta : Fin 3 → Fin 3 → ℝ) (i l : Fin 3) : ℝ :=
  eps i l - ∑ j, ∑ k, eta i j * mu j k * theta k l

/-- Eq. (A12): `ξ_{ik} = η_{ij} μ_{jk}`. -/
def xiEM (eta mu : Fin 3 → Fin 3 → ℝ) (i k : Fin 3) : ℝ := ∑ j, eta i j * mu j k

/-- Eq. (A13): `ζ_{jl} = -μ_{jk} θ_{kl}`. -/
def zetaEM (mu theta : Fin 3 → Fin 3 → ℝ) (j l : Fin 3) : ℝ := -∑ k, mu j k * theta k l

/-- Eqs. (A15)-(A16): `ε°_{il} ∂_t E_l + ξ_{ik} ∂_t H_k - ε_{ijk} ∂_j H_k = -J^e_i` and
`ξ_{lj} ∂_t E_l + μ_{jk} ∂_t H_k + ε_{jkl} ∂_k E_l = -J^m_j`. -/
def MaxwellEO (eO xi mu : Space → Fin 3 → Fin 3 → ℝ) (E H Je Jm : Space → ℝ → Fin 3 → ℝ) :
    Prop :=
  ∀ x t,
    (∀ i, ∑ l, eO x i l * pdt (cmp E l) x t + ∑ k, xi x i k * pdt (cmp H k) x t -
        ∑ j, ∑ k, levi i j k * pdx j (cmp H k) x t = -Je x t i) ∧
    ∀ j, ∑ l, xi x l j * pdt (cmp E l) x t + ∑ k, mu x j k * pdt (cmp H k) x t +
        ∑ k, ∑ l, levi j k l * pdx k (cmp E l) x t = -Jm x t j

/-- Eqs. (A17)-(A19): the transverse-electric system in the `(x₁, x₃)`-plane for
`E₂, H₁, H₃`. -/
def TESystem (eO xi mu : Plane → Fin 3 → Fin 3 → ℝ) (E H Je Jm : Plane → ℝ → Fin 3 → ℝ) :
    Prop :=
  ∀ x t,
    eO x 1 1 * pdt (cmp E 1) x t + xi x 1 0 * pdt (cmp H 0) x t +
        xi x 1 2 * pdt (cmp H 2) x t + pdx 0 (cmp H 2) x t - pdx 1 (cmp H 0) x t = -Je x t 1 ∧
    mu x 0 0 * pdt (cmp H 0) x t + mu x 2 0 * pdt (cmp H 2) x t +
        xi x 1 0 * pdt (cmp E 1) x t - pdx 1 (cmp E 1) x t = -Jm x t 0 ∧
    mu x 2 0 * pdt (cmp H 0) x t + mu x 2 2 * pdt (cmp H 2) x t +
        xi x 1 2 * pdt (cmp E 1) x t + pdx 0 (cmp E 1) x t = -Jm x t 2

/-- Eqs. (A20)-(A22): the transverse-magnetic system in the `(x₁, x₃)`-plane for
`H₂, E₁, E₃`. -/
def TMSystem (eO xi mu : Plane → Fin 3 → Fin 3 → ℝ) (E H Je Jm : Plane → ℝ → Fin 3 → ℝ) :
    Prop :=
  ∀ x t,
    mu x 1 1 * pdt (cmp H 1) x t + xi x 0 1 * pdt (cmp E 0) x t +
        xi x 2 1 * pdt (cmp E 2) x t - pdx 0 (cmp E 2) x t + pdx 1 (cmp E 0) x t = -Jm x t 1 ∧
    eO x 0 0 * pdt (cmp E 0) x t + eO x 2 0 * pdt (cmp E 2) x t +
        xi x 0 1 * pdt (cmp H 1) x t + pdx 1 (cmp H 1) x t = -Je x t 0 ∧
    eO x 2 0 * pdt (cmp E 0) x t + eO x 2 2 * pdt (cmp E 2) x t +
        xi x 2 1 * pdt (cmp H 1) x t - pdx 0 (cmp H 1) x t = -Je x t 2

/-! ### Elastodynamic waves (Appendix A.2) -/

/-- Eqs. (A23)-(A24): equilibrium of momentum `∂_t m_i - ∂_j τ_{ij} = F_i` and the
deformation equation `∂_t e_{kl} - ½(∂_k v_l + ∂_l v_k) = -h_{kl}`. -/
def ElastoBase (mom : Space → ℝ → Fin 3 → ℝ) (tau e : Space → ℝ → Fin 3 → Fin 3 → ℝ)
    (v F : Space → ℝ → Fin 3 → ℝ) (h : Space → ℝ → Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ x t,
    (∀ i, pdt (cmp mom i) x t - ∑ j, pdx j (fun y s => tau y s i j) x t = F x t i) ∧
    ∀ k l, pdt (fun y s => e y s k l) x t -
        (1 / 2) * (pdx k (cmp v l) x t + pdx l (cmp v k) x t) = -h x t k l

/-- Eqs. (A26)-(A27): the low-frequency effective (Willis) constitutive relations
`m_i = ρ_{ik} v_k + S⁽²⁾_{ikl} e_{kl}`, `τ_{mn} = S⁽¹⁾_{mnp} v_p + c_{mnpq} e_{pq}`. -/
def WillisConst (rho : Space → Fin 3 → Fin 3 → ℝ) (S2 S1 : Space → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (c : Space → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (mom v : Space → ℝ → Fin 3 → ℝ)
    (e tau : Space → ℝ → Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ x t,
    (∀ i, mom x t i = ∑ k, rho x i k * v x t k + ∑ k, ∑ l, S2 x i k l * e x t k l) ∧
    ∀ m n, tau x t m n = ∑ p, S1 x m n p * v x t p + ∑ p, ∑ q, c x m n p q * e x t p q

/-- Eq. (A39): `ρ°_{ip} = ρ_{ip} - S⁽²⁾_{ikl} s_{klmn} S⁽¹⁾_{mnp}`. -/
def rhoOW (rho : Fin 3 → Fin 3 → ℝ) (S2 : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (s : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (S1 : Fin 3 → Fin 3 → Fin 3 → ℝ) (i p : Fin 3) : ℝ :=
  rho i p - ∑ k, ∑ l, ∑ m, ∑ n, S2 i k l * s k l m n * S1 m n p

/-- Eq. (A40): `ξ_{imn} = -S⁽²⁾_{ikl} s_{klmn}`. -/
def xiW (S2 : Fin 3 → Fin 3 → Fin 3 → ℝ) (s : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (i m n : Fin 3) : ℝ :=
  -∑ k, ∑ l, S2 i k l * s k l m n

/-- Eq. (A41): `ζ_{klp} = s_{klmn} S⁽¹⁾_{mnp}`. -/
def zetaW (s : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (S1 : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (k l p : Fin 3) : ℝ :=
  ∑ m, ∑ n, s k l m n * S1 m n p

/-- Eqs. (A43)-(A44): `ρ°_{ip} ∂_t v_p - ξ_{imn} ∂_t τ_{mn} - ∂_j τ_{ij} = F_i` and
`-ξ_{pkl} ∂_t v_p + s_{klmn} ∂_t τ_{mn} - ½(∂_k v_l + ∂_l v_k) = -h_{kl}`. -/
def ElastoEqs (rhoO : Space → Fin 3 → Fin 3 → ℝ) (xi : Space → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (s : Space → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (v : Space → ℝ → Fin 3 → ℝ)
    (tau : Space → ℝ → Fin 3 → Fin 3 → ℝ) (F : Space → ℝ → Fin 3 → ℝ)
    (h : Space → ℝ → Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ x t,
    (∀ i, ∑ p, rhoO x i p * pdt (cmp v p) x t -
        ∑ m, ∑ n, xi x i m n * pdt (fun y s' => tau y s' m n) x t -
        ∑ j, pdx j (fun y s' => tau y s' i j) x t = F x t i) ∧
    ∀ k l, -∑ p, xi x p k l * pdt (cmp v p) x t +
        ∑ m, ∑ n, s x k l m n * pdt (fun y s' => tau y s' m n) x t -
        (1 / 2) * (pdx k (cmp v l) x t + pdx l (cmp v k) x t) = -h x t k l

/-- Eqs. (A45)-(A47): the horizontally polarised shear (SH) system in the `(x₁, x₃)`-plane for
`v₂, τ₂₁, τ₂₃`. -/
def SHSystem (rhoO : Plane → Fin 3 → Fin 3 → ℝ) (xi : Plane → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (s : Plane → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (v : Plane → ℝ → Fin 3 → ℝ)
    (tau : Plane → ℝ → Fin 3 → Fin 3 → ℝ) (F : Plane → ℝ → Fin 3 → ℝ)
    (h : Plane → ℝ → Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ x t,
    rhoO x 1 1 * pdt (cmp v 1) x t - 2 * xi x 1 1 0 * pdt (fun y s' => tau y s' 1 0) x t -
        2 * xi x 1 1 2 * pdt (fun y s' => tau y s' 1 2) x t -
        pdx 0 (fun y s' => tau y s' 1 0) x t - pdx 1 (fun y s' => tau y s' 1 2) x t = F x t 1 ∧
    -4 * s x 0 1 1 0 * pdt (fun y s' => tau y s' 1 0) x t -
        4 * s x 0 1 1 2 * pdt (fun y s' => tau y s' 1 2) x t +
        2 * xi x 1 1 0 * pdt (cmp v 1) x t + pdx 0 (cmp v 1) x t = 2 * h x t 1 0 ∧
    -4 * s x 0 1 1 2 * pdt (fun y s' => tau y s' 1 0) x t -
        4 * s x 2 1 1 2 * pdt (fun y s' => tau y s' 1 2) x t +
        2 * xi x 1 1 2 * pdt (cmp v 1) x t + pdx 1 (cmp v 1) x t = 2 * h x t 1 2

/-! ### Acoustic waves (Appendix A.3) -/

/-- Eq. (A61): the compressibility `κ = 1/K`. -/
def kappaAc (K : ℝ) : ℝ := 1 / K

/-- Eq. (A60): `ζ_p = ⅓ κ S⁽¹⁾_{mmp}`. -/
def zetaAc (K : ℝ) (S1 : Fin 3 → Fin 3 → Fin 3 → ℝ) (p : Fin 3) : ℝ :=
  (1 / 3) * kappaAc K * ∑ m, S1 m m p

/-- Eq. (A63): `ρ°_{ip} = ρ_{ip} - (1/9) κ S⁽²⁾_{ill} S⁽¹⁾_{mmp}`. -/
def rhoOAc (rho : Fin 3 → Fin 3 → ℝ) (K : ℝ) (S2 S1 : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (i p : Fin 3) : ℝ :=
  rho i p - (1 / 9) * kappaAc K * (∑ l, S2 i l l) * (∑ m, S1 m m p)

/-- Eq. (A64): `ξ_i = -⅓ κ S⁽²⁾_{ill}`. -/
def xiAc (K : ℝ) (S2 : Fin 3 → Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  -(1 / 3) * kappaAc K * ∑ l, S2 i l l

/-- Eqs. (A66)-(A67): `ρ°_{ip} ∂_t v_p + ξ_i ∂_t p + ∂_i p = F_i` and
`ξ_p ∂_t v_p + κ ∂_t p + ∂_k v_k = q`. -/
def AcousticEqs (rhoO : Space → Fin 3 → Fin 3 → ℝ) (xi : Space → Fin 3 → ℝ) (kappa : Space → ℝ)
    (v : Space → ℝ → Fin 3 → ℝ) (p : Space → ℝ → ℝ) (F : Space → ℝ → Fin 3 → ℝ)
    (q : Space → ℝ → ℝ) : Prop :=
  ∀ x t,
    (∀ i, ∑ j, rhoO x i j * pdt (cmp v j) x t + xi x i * pdt p x t + pdx i p x t = F x t i) ∧
    ∑ j, xi x j * pdt (cmp v j) x t + kappa x * pdt p x t + ∑ k, pdx k (cmp v k) x t = q x t

/-- Eqs. (A68)-(A70): the acoustic (AC) system in the `(x₁, x₃)`-plane for `p, v₁, v₃`. -/
def ACSystem (rhoO : Plane → Fin 3 → Fin 3 → ℝ) (xi : Plane → Fin 3 → ℝ) (kappa : Plane → ℝ)
    (v : Plane → ℝ → Fin 3 → ℝ) (p : Plane → ℝ → ℝ) (F : Plane → ℝ → Fin 3 → ℝ)
    (q : Plane → ℝ → ℝ) : Prop :=
  ∀ x t,
    kappa x * pdt p x t + xi x 0 * pdt (cmp v 0) x t + xi x 2 * pdt (cmp v 2) x t +
        pdx 0 (cmp v 0) x t + pdx 1 (cmp v 2) x t = q x t ∧
    rhoO x 0 0 * pdt (cmp v 0) x t + rhoO x 2 0 * pdt (cmp v 2) x t + xi x 0 * pdt p x t +
        pdx 0 p x t = F x t 0 ∧
    rhoO x 2 0 * pdt (cmp v 0) x t + rhoO x 2 2 * pdt (cmp v 2) x t + xi x 2 * pdt p x t +
        pdx 1 p x t = F x t 2

/-! ### Matrix-vector wave equation and its decomposition (Appendix B) -/

/-- Eq. (B20): `d = ϑ₃₃⁻¹ ϑ₁₃`. -/
def dCoef (b : Fin 2 → Fin 2 → ℝ) : ℝ := (thetaOf b 1 1)⁻¹ * thetaOf b 0 1

/-- Eq. (B11): `b_s = ϑ_{1s} - ϑ₁₃ ϑ₃₃⁻¹ ϑ_{3s}`. -/
def bCoef (b : Fin 2 → Fin 2 → ℝ) (s : Fin 2) : ℝ :=
  thetaOf b 0 s - thetaOf b 0 1 * (thetaOf b 1 1)⁻¹ * thetaOf b 1 s

/-- Appendix B.1: the operator `∂₁ - iωγ₁` acting on a function of `x₁` along a depth level,
where `gamma` gives `γ_r` along that level. -/
def D1op (ω : ℝ) (gamma : ℝ → Fin 2 → ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  deriv f y - Complex.I * ω * gamma y 0 * f y

/-- Eqs. (B3)-(B5), (B14)-(B17): the operator matrix `𝒜` applied to `q = (P, Q₃)` along a depth level,
`(𝒜₁₁ P + 𝒜₁₂ Q₃, 𝒜₂₁ P + 𝒜₂₂ Q₃)` with `𝒜₁₁ = iωγ₃ - d(∂₁ - iωγ₁)`, `𝒜₁₂ = iωϑ₃₃⁻¹`,
`𝒜₂₁ = iωα - (iω)⁻¹(∂₁ - iωγ₁) b₁ (∂₁ - iωγ₁)`, `𝒜₂₂ = iωγ₃ - (∂₁ - iωγ₁) d`; differential
operators act on all factors to their right. The arguments are functions of `x₁`. -/
def opA (ω : ℝ) (alpha : ℝ → ℝ) (beta : ℝ → Fin 2 → Fin 2 → ℝ) (gamma : ℝ → Fin 2 → ℝ)
    (P Q3 : ℝ → ℂ) (x1 : ℝ) : Fin 2 → ℂ :=
  ![Complex.I * ω * gamma x1 1 * P x1 - dCoef (beta x1) * D1op ω gamma P x1 +
      Complex.I * ω * ((thetaOf (beta x1) 1 1)⁻¹ : ℝ) * Q3 x1,
    Complex.I * ω * alpha x1 * P x1 -
      (1 / (Complex.I * ω)) * D1op ω gamma (fun y => bCoef (beta y) 0 * D1op ω gamma P y) x1 +
      Complex.I * ω * gamma x1 1 * Q3 x1 - D1op ω gamma (fun y => dCoef (beta y) * Q3 y) x1]

/-- Eqs. (B4), (B18)-(B19): the source vector `d = (C°, B°)` along a depth level, with
`C° = d C₁ + C₃` and `B° = B + (iω)⁻¹(∂₁ - iωγ₁) b₁ C₁`. -/
def srcVec (ω : ℝ) (beta : ℝ → Fin 2 → Fin 2 → ℝ) (gamma : ℝ → Fin 2 → ℝ) (B : ℝ → ℂ)
    (C : ℝ → Fin 2 → ℂ) (x1 : ℝ) : Fin 2 → ℂ :=
  ![dCoef (beta x1) * C x1 0 + C x1 1,
    B x1 + (1 / (Complex.I * ω)) * D1op ω gamma (fun y => bCoef (beta y) 0 * C y 0) x1]

/-- Eq. (B22): `s₃² = ϑ₃₃⁻¹(α - b₁(s₁ - γ₁)²)` for a medium with parameters `α, β, γ` at the
depth level considered and horizontal slowness `s₁`. -/
def s3sq (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ) (s1 : ℝ) : ℝ :=
  (thetaOf beta 1 1)⁻¹ * (alpha - bCoef beta 0 * (s1 - gamma 0) ^ 2)

/-- Eq. (B21): the slowness-domain operator matrix
`𝒜̃ = [[iω{γ₃ - d(s₁ - γ₁)}, iωϑ₃₃⁻¹], [iωϑ₃₃ s₃², iω{γ₃ - d(s₁ - γ₁)}]]`. -/
def Atilde (ω alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ) (s1 : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I * ω * ((gamma 1 - dCoef beta * (s1 - gamma 0) : ℝ) : ℂ),
      Complex.I * ω * (((thetaOf beta 1 1)⁻¹ : ℝ) : ℂ);
    Complex.I * ω * ((thetaOf beta 1 1 * s3sq alpha beta gamma s1 : ℝ) : ℂ),
      Complex.I * ω * ((gamma 1 - dCoef beta * (s1 - gamma 0) : ℝ) : ℂ)]

/-- Eq. (B28): the vertical slowness `s₃ = √(ϑ₃₃⁻¹(α - b₁(s₁ - γ₁)²))` for
`(s₁ - γ₁)² ≤ α/b₁` (propagating waves) and `s₃ = i√(ϑ₃₃⁻¹(b₁(s₁ - γ₁)² - α))` otherwise
(evanescent waves). -/
def s3 (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ) (s1 : ℝ) : ℂ :=
  if (s1 - gamma 0) ^ 2 ≤ alpha / bCoef beta 0 then
    ((Real.sqrt ((thetaOf beta 1 1)⁻¹ * (alpha - bCoef beta 0 * (s1 - gamma 0) ^ 2)) : ℝ) : ℂ)
  else
    Complex.I *
      ((Real.sqrt ((thetaOf beta 1 1)⁻¹ * (bCoef beta 0 * (s1 - gamma 0) ^ 2 - alpha)) : ℝ) : ℂ)

/-- Eq. (B27): `λ^± = s₃ ± {γ₃ - d(s₁ - γ₁)}`; `lamPM true` is `λ⁺`, `lamPM false` is `λ⁻`. -/
def lamPM (plus : Bool) (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ) (s1 : ℝ) :
    ℂ :=
  if plus then s3 alpha beta gamma s1 + ((gamma 1 - dCoef beta * (s1 - gamma 0) : ℝ) : ℂ)
  else s3 alpha beta gamma s1 - ((gamma 1 - dCoef beta * (s1 - gamma 0) : ℝ) : ℂ)

/-- Eq. (B24): `ℋ̃ = diag(iωλ⁺, -iωλ⁻)`. -/
def Htilde (ω alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ) (s1 : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I * ω * lamPM true alpha beta gamma s1, 0;
    0, -(Complex.I * ω * lamPM false alpha beta gamma s1)]

/-- Eqs. (B25)-(B26): the square root `√(ϑ₃₃ s₃)` (principal branch of the complex square
root). -/
def sqrtTS (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ) (s1 : ℝ) : ℂ :=
  ((thetaOf beta 1 1 : ℝ) * s3 alpha beta gamma s1) ^ (1 / 2 : ℂ)

/-- Eq. (B25): `ℒ̃ = (1/√2) [[1/√(ϑ₃₃s₃), 1/√(ϑ₃₃s₃)], [√(ϑ₃₃s₃), -√(ϑ₃₃s₃)]]`. -/
def Ltilde (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ) (s1 : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / (Real.sqrt 2 : ℂ)) •
    !![1 / sqrtTS alpha beta gamma s1, 1 / sqrtTS alpha beta gamma s1;
      sqrtTS alpha beta gamma s1, -sqrtTS alpha beta gamma s1]

/-- Eq. (B26): the printed inverse
`(1/√2) [[√(ϑ₃₃s₃), 1/√(ϑ₃₃s₃)], [√(ϑ₃₃s₃), -1/√(ϑ₃₃s₃)]]`. -/
def LtildeInv (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ) (s1 : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / (Real.sqrt 2 : ℂ)) •
    !![sqrtTS alpha beta gamma s1, 1 / sqrtTS alpha beta gamma s1;
      sqrtTS alpha beta gamma s1, -(1 / sqrtTS alpha beta gamma s1)]

/-- Eq. (B31): `N = [[0, 1], [-1, 0]]`. -/
def Nmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- Eq. (B31): `K = [[0, 1], [1, 0]]`. -/
def Kmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Eq. (B39): `J = diag(1, -1)`. -/
def Jmat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

end Arxiv1810_02867


