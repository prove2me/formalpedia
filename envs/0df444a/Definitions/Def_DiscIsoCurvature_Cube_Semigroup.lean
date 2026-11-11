-- Prove2me | Definitions.Def_DiscIsoCurvature_Cube_Semigroup
-- name    : DiscIsoCurvature_Cube_Semigroup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:07:44.321895+00:00
-- url     : https://prove2.me/theorems/aa875720-9bbb-4b3a-9167-7c3b2dc4e82e
-- title:
--   Transition rates, generator, heat semigroup e^{tL}, weighted Γ-calculus, weighted influences, the log-Sobolev inequality, canonical rates and weights
-- statement:
--   Let $\Omega=\{\pm1\}^n$, $\mu$ a distribution on $\Omega$, **transition rates** $q_i:\Omega\to\mathbb R_+$ and **weights** $w_i:\Omega\to\mathbb R_+$. The **generator** and **heat semigroup** are
--   $$Lf(x)=\sum_{i=1}^nq_i(x)\big(f(x^i)-f(x)\big),\qquad P_t=e^{tL}\ (t\ge0),$$
--   and $P_\infty f=\mathbb E_\mu[f]$. $L$ is **reversible** for $\mu$ when $\mu(x)q_i(x)=\mu(x^i)q_i(x^i)$; weights are **$b$-bounded** when $b\le w_i(x)\le1/b$.
--
--   The **weighted Γ-calculus**: $\Gamma_{w,i}(f,g)(x)=\tfrac12w_i(x)q_i(x)(f(x^i)-f(x))(g(x^i)-g(x))$, $\Gamma_w=\sum_i\Gamma_{w,i}$ ($\Gamma=\Gamma_w$ with $w\equiv1$), $\delta_{w,i}f(x)=\sqrt{\tfrac12w_i(x)q_i(x)}\,(f(x^i)-f(x))$, $|\delta_{w,i}|f=|\delta_{w,i}f|$, and $\Gamma_{2;w}(f)=\tfrac12L\Gamma_w(f)-\Gamma_w(f,Lf)$.
--
--   **Weighted influences** (Definition 3.7): $I_w(f)=\mathbb E_\mu[\Gamma_w(f)]$, $I_{w,i}(f)=\mathbb E_\mu[\Gamma_{w,i}(f)]$, $A_w(f)=\mathbb E_\mu[\sqrt{\Gamma_w(f)}]$, $J_w(f)=\sum_i(\mathbb E_\mu[|\delta_{w,i}|f])^2$; $I(f)$ is $I_w(f)$ with $w\equiv1$.
--
--   The **log-Sobolev inequality** with constant $\rho>0$ (Definition 3.13): $\mathrm{Ent}_\mu[f^2]\le\frac2\rho\mathbb E_\mu[\Gamma(f)]$ for every $f:\Omega\to\mathbb R$.
--
--   The **canonical rates and weights** (Eq. (48)): $q^\star_i(x)=\tfrac12\sqrt{\mu(x^i)/\mu(x)}$, $w^\star_i(x)=2q^\star_i(x)=\sqrt{\mu(x^i)/\mu(x)}$.
--
--   **Formalization Note.** Rates and weights are real families `Fin n → BoolCube n → ℝ`; positivity (`IsPositive`) and reversibility are hypotheses of the theorems. $P_t$ is `NormedSpace.exp (t • generator q)` applied with `mulVec`. $P_\tau$ for $\tau\in[0,\infty]$ takes `τ : WithTop ℝ≥0`, with $P_\top f$ the constant $\mathbb E_\mu[f]$. $\Gamma_w$ is the explicit formula the paper derives from $\tfrac12(L_w(fg)-gL_wf-fL_wg)$. `LSI μ q ρ` includes $\rho>0$. In $q^\star$, $w^\star$, $\mu(x)>0$ is assumed wherever they are used.
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 13 §3.1, pp. 13–14 Definitions 3.1, 3.2, 3.5, p. 15 Definition 3.7, p. 17 Definition 3.13, p. 16 Example 3.9, p. 22 Definition 4.12, p. 32 Eq. (48)

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic

namespace DiscIsoCurvature.Cube

open scoped NNReal

/-!
# Transition rates, the generator, the heat semigroup, the weighted Γ-calculus, weighted
# influences, the log-Sobolev inequality, canonical rates and weights, b-boundedness

Chen, Chen, Zhang, *Discrete Isoperimetric Inequalities via Curvature*, arXiv:2609.24687
(version of November 3, 2026, sha256 ec30d304…): §3.1 (p. 13), Definitions 3.1, 3.2, 3.5
(pp. 13–14), Definition 3.7 (p. 15), Definition 3.13 (p. 17), Definition 4.12 (p. 22),
Example 3.9 (p. 16) and Eq. (48) (p. 32).

* Transition rates and weights are families `q, w : Fin n → BoolCube n → ℝ`. The paper's
  `q_i, w_i : Ω → ℝ₊` are positive (the paper writes `ℝ≥0` where it means nonnegative):
  theorems carry `IsPositive q`, `IsPositive w`. Reversibility
  `μ(x) q_i(x) = μ(x^i) q_i(x^i)` is `IsReversible μ q`.
* `generator q` is the matrix of `L f(x) = ∑ᵢ q_i(x)(f(x^i) − f(x))` on `ℝ^Ω`, and
  `heat q t = e^{tL}` is its matrix exponential (`NormedSpace.exp`); `semigroup q t f = P_t f`.
  `semigroupExt μ q τ` is `P_τ` for `τ ∈ [0, ∞]`, encoded as `τ : WithTop ℝ≥0`, with
  `P_∞ f = E_μ[f]` (the constant function).
* `Γ_w(f, g)(x) = ½ ∑ᵢ w_i(x) q_i(x)(f(x^i) − f(x))(g(x^i) − g(x))` (the explicit formula of
  Definition 3.1); `Γ` is `Γ_w` with `w ≡ 1`.
* `δ_{w,i} f(x) = √(½ w_i(x) q_i(x)) (f(x^i) − f(x))`, `|δ_{w,i}| f = |δ_{w,i} f|`.
* `Γ_{2;w}(f) = ½ L Γ_w(f) − Γ_w(f, Lf)` with `L` the (unweighted) generator of `q`.
-/

/-- Every value is positive: `q_i(x) > 0` for all `i, x` (rates or weights valued in `ℝ₊`). -/
def IsPositive {n : ℕ} (q : Fin n → BoolCube n → ℝ) : Prop :=
  ∀ i x, 0 < q i x

/-- Reversibility of `L` with respect to `μ` (§3.1, p. 13): `μ(x) q_i(x) = μ(x^i) q_i(x^i)`. -/
def IsReversible {n : ℕ} (μ : BoolCube n → ℝ) (q : Fin n → BoolCube n → ℝ) : Prop :=
  ∀ x i, μ x * q i x = μ (flip x i) * q i (flip x i)

/-- `b`-boundedness (Definition 4.12, p. 22): `b ≤ w_i(x) ≤ 1/b` for all `i, x`. -/
def IsBBounded {n : ℕ} (b : ℝ) (w : Fin n → BoolCube n → ℝ) : Prop :=
  ∀ i x, b ≤ w i x ∧ w i x ≤ 1 / b

/-- The generator `L f(x) = ∑ᵢ q_i(x)(f(x^i) − f(x))` applied to a function (§3.1). -/
noncomputable def gen {n : ℕ} (q : Fin n → BoolCube n → ℝ) (f : BoolCube n → ℝ) (x : BoolCube n) : ℝ :=
  ∑ i, q i x * (f (flip x i) - f x)

/-- The matrix of the generator `L` on `ℝ^Ω`: `(generator q) *ᵥ f = gen q f`. -/
noncomputable def generator {n : ℕ} (q : Fin n → BoolCube n → ℝ) : Matrix (BoolCube n) (BoolCube n) ℝ :=
  fun x y => ∑ i, q i x * ((if y = flip x i then 1 else 0) - (if y = x then 1 else 0))

/-- The heat semigroup `P_t = e^{tL}` as a matrix exponential (§3.1). -/
noncomputable def heat {n : ℕ} (q : Fin n → BoolCube n → ℝ) (t : ℝ) : Matrix (BoolCube n) (BoolCube n) ℝ :=
  NormedSpace.exp (t • generator q)

/-- `P_t f = e^{tL} f`. -/
noncomputable def semigroup {n : ℕ} (q : Fin n → BoolCube n → ℝ) (t : ℝ) (f : BoolCube n → ℝ) :
    BoolCube n → ℝ :=
  (heat q t).mulVec f

/-- `P_τ` for `τ ∈ [0, ∞]` (`τ : WithTop ℝ≥0`): `P_τ = e^{τL}` for finite `τ`, and
`P_∞ f = E_μ[f]` (the constant function), as in Definition 4.8 (p. 21). -/
noncomputable def semigroupExt {n : ℕ} (μ : BoolCube n → ℝ) (q : Fin n → BoolCube n → ℝ)
    (τ : WithTop ℝ≥0) (f : BoolCube n → ℝ) : BoolCube n → ℝ :=
  if h : τ = ⊤ then fun _ => expect μ f else semigroup q ((τ.untop h : ℝ≥0) : ℝ) f

/-- `Γ_{w,i}(f, g)(x) = ½ w_i(x) q_i(x)(f(x^i) − f(x))(g(x^i) − g(x))` (p. 14). -/
noncomputable def gammaI {n : ℕ} (w q : Fin n → BoolCube n → ℝ) (i : Fin n) (f g : BoolCube n → ℝ)
    (x : BoolCube n) : ℝ :=
  (1 / 2) * w i x * q i x * (f (flip x i) - f x) * (g (flip x i) - g x)

/-- Weighted carré du champ `Γ_w(f, g) = ∑ᵢ Γ_{w,i}(f, g)` (Definition 3.1, p. 13). The
unweighted `Γ` is `gamma (fun _ _ => 1) q`. -/
noncomputable def gamma {n : ℕ} (w q : Fin n → BoolCube n → ℝ) (f g : BoolCube n → ℝ) (x : BoolCube n) : ℝ :=
  ∑ i, gammaI w q i f g x

/-- The unit weights `w ≡ 1`. -/
def unitWeight (n : ℕ) : Fin n → BoolCube n → ℝ := fun _ _ => 1

/-- Weighted discrete derivative `δ_{w,i} f(x) = √(½ w_i(x) q_i(x)) (f(x^i) − f(x))`
(Definition 3.2, p. 14). -/
noncomputable def delta {n : ℕ} (w q : Fin n → BoolCube n → ℝ) (i : Fin n) (f : BoolCube n → ℝ)
    (x : BoolCube n) : ℝ :=
  Real.sqrt ((1 / 2) * w i x * q i x) * (f (flip x i) - f x)

/-- Absolute weighted discrete derivative `|δ_{w,i}| f = |δ_{w,i} f|` (Definition 3.2); the
vector field `|∇_w| f = (|δ_{w,1}| f, …, |δ_{w,n}| f)`. -/
noncomputable def absDelta {n : ℕ} (w q : Fin n → BoolCube n → ℝ) (i : Fin n) (f : BoolCube n → ℝ)
    (x : BoolCube n) : ℝ :=
  |delta w q i f x|

/-- Iterated weighted carré du champ `Γ_{2;w}(f) = ½ L Γ_w(f) − Γ_w(f, Lf)`
(Definition 3.5, p. 14). -/
noncomputable def gamma2 {n : ℕ} (w q : Fin n → BoolCube n → ℝ) (f : BoolCube n → ℝ) (x : BoolCube n) : ℝ :=
  (1 / 2) * gen q (gamma w q f f) x - gamma w q f (gen q f) x

/-- Total weighted influence `I_w(f) = E_μ[Γ_w(f)]` (Definition 3.7 (1), p. 15). -/
noncomputable def wInfluence {n : ℕ} (μ : BoolCube n → ℝ) (w q : Fin n → BoolCube n → ℝ)
    (f : BoolCube n → ℝ) : ℝ :=
  expect μ (fun x => gamma w q f f x)

/-- Coordinate weighted influence `I_{w,i}(f) = E_μ[Γ_{w,i}(f)]` (Definition 3.7 (1)). -/
noncomputable def wInfluenceI {n : ℕ} (μ : BoolCube n → ℝ) (w q : Fin n → BoolCube n → ℝ) (i : Fin n)
    (f : BoolCube n → ℝ) : ℝ :=
  expect μ (fun x => gammaI w q i f f x)

/-- Weighted surface area `A_w(f) = E_μ[√(Γ_w f)]` (Definition 3.7 (2)). -/
noncomputable def wSurfaceArea {n : ℕ} (μ : BoolCube n → ℝ) (w q : Fin n → BoolCube n → ℝ)
    (f : BoolCube n → ℝ) : ℝ :=
  expect μ (fun x => Real.sqrt (gamma w q f f x))

/-- Weighted total squared influence `J_w(f) = ∑ᵢ (E_μ[|δ_{w,i}| f])²` (Definition 3.7 (3)). -/
noncomputable def wSqInfluence {n : ℕ} (μ : BoolCube n → ℝ) (w q : Fin n → BoolCube n → ℝ)
    (f : BoolCube n → ℝ) : ℝ :=
  ∑ i, (expect μ (absDelta w q i f)) ^ 2

/-- The log-Sobolev inequality with constant `ρ > 0` (Definition 3.13, p. 17):
`Ent_μ[f²] ≤ (2/ρ) E_μ[Γ(f)]` for every `f : Ω → ℝ`, with `Γ` the unweighted carré du champ. -/
def LSI {n : ℕ} (μ : BoolCube n → ℝ) (q : Fin n → BoolCube n → ℝ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ f : BoolCube n → ℝ,
    ent μ (fun x => f x ^ 2) ≤ (2 / ρ) * expect μ (fun x => gamma (unitWeight n) q f f x)

/-- Canonical transition rates `q⋆_i(x) = ½ √(μ(x^i)/μ(x))` (Example 3.9, p. 16; Eq. (48)). -/
noncomputable def qStar {n : ℕ} (μ : BoolCube n → ℝ) : Fin n → BoolCube n → ℝ :=
  fun i x => (1 / 2) * Real.sqrt (μ (flip x i) / μ x)

/-- Canonical weights `w⋆_i(x) = 2 q⋆_i(x) = √(μ(x^i)/μ(x))` (Example 3.9; Eq. (48)). -/
noncomputable def wStar {n : ℕ} (μ : BoolCube n → ℝ) : Fin n → BoolCube n → ℝ :=
  fun i x => Real.sqrt (μ (flip x i) / μ x)

end DiscIsoCurvature.Cube


