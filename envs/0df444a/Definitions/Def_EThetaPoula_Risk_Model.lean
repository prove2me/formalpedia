-- Prove2me | Definitions.Def_EThetaPoula_Risk_Model
-- name    : EThetaPoula_Risk_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:38.963136+00:00
-- url     : https://prove2.me/theorems/df7f6829-6f79-414a-8f01-f502ee9f575c
-- title:
--   The setting of e-TH$\varepsilon$O POULA: §2.1, Assumptions 1–4, the recursion (5)–(7)
-- statement:
--   The data and the assumptions of the paper, and the algorithm.
--
--   A model consists of a probability $P$ on $\Omega$, exponents $q\in[1,\infty)$, $r\in\mathbb N$ with $r\ge q/2$, $\rho\in[1,\infty)$, a loss $U:\mathbb R^d\times\mathbb R^m\to\mathbb R$, a Borel map $G$ and a continuous map $F$ from $\mathbb R^d\times\mathbb R^m$ to $\mathbb R^d$, an initial condition $\theta_0$, i.i.d. data $(X_n)$ and independent standard Gaussians $(\xi_n)$. Then $u(\theta):=E[U(\theta,X_0)]$ is assumed $C^1$, $h:=\nabla u$, and $H=G+F$ of (4) is unbiased: $h(\theta)=E[H(\theta,X_0)]$.
--
--   Assumption 1 gives $E[|\theta_0|^{8r+4}]<\infty$ and $E[|X_0|^{(8r+4)\rho}]<\infty$. Assumption 2 gives the local Lipschitz condition in average on $G$ and a polynomial growth bound with $K_G>1$. Assumption 3 gives the local Lipschitz condition and the componentwise growth bound on $F$. Assumption 4 gives the convexity at infinity condition (31), with positive semidefinite forms $A(x),B(x)$, $0\le\bar r<2r$, $a>0$, $b\ge0$.
--
--   For a stepsize $\lambda>0$, inverse temperature $\beta>0$ and $0<\varepsilon<1$, the algorithm is
--   $$
--   \theta^\lambda_0:=\theta_0,\qquad\theta^\lambda_{n+1}:=\theta^\lambda_n-\lambda H_\lambda(\theta^\lambda_n,X_{n+1})+\sqrt{2\lambda\beta^{-1}}\,\xi_{n+1},
--   $$
--   where $H_\lambda=G_\lambda+F_\lambda$ and, for $i=1,\dots,d$,
--   $$
--   G^{(i)}_\lambda(\theta,x):=\frac{G^{(i)}(\theta,x)}{1+\sqrt\lambda|G^{(i)}(\theta,x)|}\Bigl(1+\frac{\sqrt\lambda}{\varepsilon+|G^{(i)}(\theta,x)|}\Bigr),\qquad F^{(i)}_\lambda(\theta,x):=\frac{F^{(i)}(\theta,x)}{1+\sqrt\lambda|\theta|^{2r}}.
--   $$
--
--   **Formalization Note** The filtration of §2.1 is dropped: $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ are mutually independent as three random objects, which the paper's hypothesis implies. In Assumption 4(iii), $a$ and $b$ are the minimum and maximum of the Rayleigh quotients of $E[A(X_0)]$, $E[B(X_0)]$ on the unit sphere, because $A,B$ are not assumed symmetric and only the quadratic forms enter; for symmetric means these are the extreme eigenvalues. `Model.params` fills the tower of `Params` with the actual moments.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §2.1, pp.3–4; (5)–(7), p.5; §4.1, Assumptions 1–4, p.16; (3) p.3; V_p̄ p.23

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Constants
import Definitions.Def_EThetaPoula_Risk_gibbsMeasure

open MeasureTheory ProbabilityTheory

namespace EThetaPoula.Risk

/-- `ℝ^k` with the Euclidean norm. -/
abbrev Eucl (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The Lyapunov function `V_p̄(θ) := (1 + |θ|²)^{p̄/2}`, Lim, Neufeld, Sabanis, Zhang,
arXiv:2210.13193v3, §6.1, p.23. -/
noncomputable def lyapunov {d : ℕ} (p : ℕ) (θ : Eucl d) : ℝ := vFun p ‖θ‖

/-- The data of §2.1, p.3–4, and of the opening line of §4.1, p.16, of Lim, Neufeld, Sabanis,
Zhang, arXiv:2210.13193v3: the probability `P` on `Ω`, the exponents `q, r, ρ`, the loss `U`, the
two parts `G`, `F` of the stochastic gradient (4), the initial condition `θ₀`, the data `(X_n)` and
the Gaussian noise `(ξ_n)`. The conditions on them are `Model.Admissible` and Assumptions 1–4.

**Formalization Note.** `E = ℝ^d` is `Eucl d`, and `ℝ^m` is `Eucl m`. The paper's `X` is `X 0`,
which has the law of `X`. `r` is a natural number, as in §4.1; `q`, `ρ` are real, so `(1 + |x|)^ρ`
is `Real.rpow`. -/
structure Model (d m : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- the probability `P` -/
  P : Measure Ω
  /-- the exponent `q ∈ [1, ∞)` -/
  q : ℝ
  /-- the exponent `r ∈ [q/2, ∞) ∩ ℕ` -/
  r : ℕ
  /-- the exponent `ρ ∈ [1, ∞)` -/
  ρ : ℝ
  /-- the loss `U(θ, x)` -/
  U : Eucl d → Eucl m → ℝ
  /-- the possibly discontinuous part `G(θ, x)` of the stochastic gradient -/
  G : Eucl d → Eucl m → Eucl d
  /-- the continuous part `F(θ, x)` of the stochastic gradient -/
  F : Eucl d → Eucl m → Eucl d
  /-- the initial condition `θ₀` -/
  θ₀ : Ω → Eucl d
  /-- the data process `(X_n)` -/
  X : ℕ → Ω → Eucl m
  /-- the Gaussian noise `(ξ_n)` -/
  ξ : ℕ → Ω → Eucl d

namespace Model

variable {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)

/-- The objective `u(θ) := E[U(θ, X)]`, §2.1, p.3. -/
noncomputable def u (θ : Eucl d) : ℝ := ∫ ω, S.U θ (S.X 0 ω) ∂S.P

/-- `h := ∇u`, §2.1, p.3. -/
noncomputable def h (θ : Eucl d) : Eucl d := gradient S.u θ

/-- `H(θ, x) := G(θ, x) + F(θ, x)` of (4), p.3. -/
def H (θ : Eucl d) (x : Eucl m) : Eucl d := S.G θ x + S.F θ x

/-- `π_β` of (3), p.3, for the objective `u`. -/
noncomputable def piBeta (β : ℝ) : Measure (Eucl d) := gibbsMeasure S.u β

/-- The standing conditions of §2.1, pp.3–4, and of the opening line of §4.1, p.16.

**Formalization Note.** The paper fixes a filtration `(G_n)` with `(X_n)` adapted, and assumes `θ₀`,
`G_∞`, `(ξ_n)` independent. That implies the two conditions `indep_θ₀`, `indep_X_ξ`, which together
say exactly that `θ₀`, `(X_n)_n`, `(ξ_n)_n` are mutually independent as three random objects; the
filtration is not otherwise used by the recursion, so it is dropped. -/
structure Admissible : Prop where
  /-- `P` is a probability measure -/
  isProb : IsProbabilityMeasure S.P
  /-- `d ≥ 1` -/
  hd : 1 ≤ d
  /-- `m ≥ 1` -/
  hm : 1 ≤ m
  /-- `q ≥ 1` -/
  hq : 1 ≤ S.q
  /-- `r ≥ q/2` -/
  hr : S.q / 2 ≤ S.r
  /-- `ρ ≥ 1` -/
  hρ : 1 ≤ S.ρ
  /-- `U` is Borel -/
  U_meas : Measurable (Function.uncurry S.U)
  /-- `E|U(θ, X)| < ∞` for all `θ` -/
  U_int : ∀ θ, Integrable (fun ω => S.U θ (S.X 0 ω)) S.P
  /-- `u` is continuously differentiable -/
  u_C1 : ContDiff ℝ 1 S.u
  /-- each `X_n` is a random variable -/
  X_meas : ∀ n, Measurable (S.X n)
  /-- the `X_n` are independent -/
  X_indep : iIndepFun S.X S.P
  /-- the `X_n` are identically distributed -/
  X_ident : ∀ n, IdentDistrib (S.X n) (S.X 0) S.P S.P
  /-- each `ξ_n` is a random variable -/
  ξ_meas : ∀ n, Measurable (S.ξ n)
  /-- the `ξ_n` are independent -/
  ξ_indep : iIndepFun S.ξ S.P
  /-- each `ξ_n` is a standard `d`-dimensional Gaussian -/
  ξ_law : ∀ n, S.P.map (S.ξ n) = stdGaussian (Eucl d)
  /-- `θ₀` is a random variable -/
  θ₀_meas : Measurable S.θ₀
  /-- `θ₀` is independent of the pair `((X_n)_n, (ξ_n)_n)` -/
  indep_θ₀ : IndepFun S.θ₀ (fun ω => (fun n => S.X n ω, fun n => S.ξ n ω)) S.P
  /-- `(X_n)_n` and `(ξ_n)_n` are independent -/
  indep_X_ξ : IndepFun (fun ω n => S.X n ω) (fun ω n => S.ξ n ω) S.P
  /-- `G` is Borel -/
  G_meas : Measurable (Function.uncurry S.G)
  /-- `F` is continuous -/
  F_cont : Continuous (Function.uncurry S.F)
  /-- `H` is an unbiased estimator of `h`: `h(θ) = E[H(θ, X₀)]` -/
  unbiased : ∀ θ, S.h θ = ∫ ω, S.H θ (S.X 0 ω) ∂S.P

end Model

/-- The quadratic form `⟨y, M y⟩`. -/
def quadForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (y : Eucl d) : ℝ :=
  ∑ i, ∑ j, y i * M i j * y j

/-- The constants and functions that Assumptions 2–4, p.16, of Lim, Neufeld, Sabanis, Zhang,
arXiv:2210.13193v3 assert to exist. -/
structure AssumptionData (d m : ℕ) where
  /-- `L_G` -/
  LG : ℝ
  /-- `K_G` -/
  KG : ℝ
  /-- `L_F` -/
  LF : ℝ
  /-- `K_F` -/
  KF : ℝ
  /-- `A : ℝ^m → ℝ^{d×d}` -/
  A : Eucl m → Matrix (Fin d) (Fin d) ℝ
  /-- `B : ℝ^m → ℝ^{d×d}` -/
  B : Eucl m → Matrix (Fin d) (Fin d) ℝ
  /-- `r̄` -/
  rbar : ℝ
  /-- `a` -/
  a : ℝ
  /-- `b` -/
  b : ℝ

namespace Model

variable {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω) (C : AssumptionData d m)

/-- **Assumption 1**, p.16: `E[|θ₀|^{8r+4}] < ∞` and `E[|X₀|^{(8r+4)ρ}] < ∞`. The i.i.d. part is in
`Model.Admissible`. -/
def Assumption1 : Prop :=
  Integrable (fun ω => ‖S.θ₀ ω‖ ^ (8 * S.r + 4)) S.P ∧
    Integrable (fun ω => ‖S.X 0 ω‖ ^ ((8 * (S.r : ℝ) + 4) * S.ρ)) S.P

/-- **Assumption 2**, p.16: `G` is locally Lipschitz in average and has polynomial growth, with
`L_G > 0` and `K_G > 1`.

**Formalization Note.** The expectation on the left is a Bochner integral; its integrand is
integrable under the growth bound and Assumption 1. -/
def Assumption2 : Prop :=
  0 < C.LG ∧
  (∀ θ θ' : Eucl d, ∫ ω, ‖S.G θ (S.X 0 ω) - S.G θ' (S.X 0 ω)‖ ∂S.P ≤
    C.LG * (1 + ‖θ‖ + ‖θ'‖) ^ (S.q - 1) * ‖θ - θ'‖) ∧
  1 < C.KG ∧
  ∀ (θ : Eucl d) (x : Eucl m), ‖S.G θ x‖ ≤ C.KG * (1 + ‖x‖) ^ S.ρ * (1 + ‖θ‖) ^ S.q

/-- **Assumption 3**, p.16: `F` is locally Lipschitz and has a componentwise growth bound, with
`L_F > 0` and `K_F > 0`. -/
def Assumption3 : Prop :=
  0 < C.LF ∧
  (∀ (θ θ' : Eucl d) (x x' : Eucl m), ‖S.F θ x - S.F θ' x'‖ ≤
    C.LF * (1 + ‖x‖ + ‖x'‖) ^ (S.ρ - 1) * (1 + ‖θ‖ + ‖θ'‖) ^ (2 * S.r)
      * (‖θ - θ'‖ + ‖x - x'‖)) ∧
  0 < C.KF ∧
  ∀ (θ : Eucl d) (x : Eucl m) (i : Fin d),
    |S.F θ x i| ≤ C.KF * (1 + ‖x‖) ^ S.ρ * (1 + |θ i|) * (1 + ‖θ‖ ^ (2 * S.r))

/-- The matrix `E[M(X₀)]`, entry by entry. -/
noncomputable def meanMatrix (M : Eucl m → Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ ω, M (S.X 0 ω) i j ∂S.P

/-- **Assumption 4**, p.16: the convexity at infinity condition on `F`, with `0 ≤ r̄ < 2r`,
`a > 0`, `b ≥ 0`.

**Formalization Note.** `A`, `B` are not assumed symmetric, and every use of (iii) is through the
quadratic forms, so (iii) is read as: `a` is the minimum and `b` the maximum of the Rayleigh
quotients `⟨y, E[A(X₀)]y⟩`, `⟨y, E[B(X₀)]y⟩` on the unit sphere. For symmetric means these are
the smallest and the largest eigenvalue. The entries of `A(X₀)`, `B(X₀)` are integrable, which
the paper implies by writing `E[A(X₀)]`, `E[B(X₀)]`. -/
def Assumption4 : Prop :=
  (∀ i j, Measurable fun x => C.A x i j) ∧ (∀ i j, Measurable fun x => C.B x i j) ∧
  (∀ i j, Integrable (fun ω => C.A (S.X 0 ω) i j) S.P) ∧
  (∀ i j, Integrable (fun ω => C.B (S.X 0 ω) i j) S.P) ∧
  0 ≤ C.rbar ∧ C.rbar < 2 * (S.r : ℝ) ∧
  (∀ (x : Eucl m) (y : Eucl d), 0 ≤ quadForm (C.A x) y ∧ 0 ≤ quadForm (C.B x) y) ∧
  (∀ (θ θ' : Eucl d) (x : Eucl m),
    quadForm (C.A x) (θ - θ') * (‖θ‖ ^ (2 * S.r) + ‖θ'‖ ^ (2 * S.r))
        - quadForm (C.B x) (θ - θ') * (‖θ‖ ^ C.rbar + ‖θ'‖ ^ C.rbar)
      ≤ inner ℝ (θ - θ') (S.F θ x - S.F θ' x)) ∧
  0 < C.a ∧ IsLeast {s | ∃ y : Eucl d, ‖y‖ = 1 ∧ s = quadForm (S.meanMatrix C.A) y} C.a ∧
  0 ≤ C.b ∧ IsGreatest {s | ∃ y : Eucl d, ‖y‖ = 1 ∧ s = quadForm (S.meanMatrix C.B) y} C.b

/-- Assumptions 1, 2, 3, and 4 together. -/
def Assumptions : Prop :=
  S.Assumption1 ∧ S.Assumption2 C ∧ S.Assumption3 C ∧ S.Assumption4 C

/-- The numeric inputs of the constant tower at the actual laws of the model. `ϵ` is the parameter
of (48). -/
noncomputable def params (β ϵ : ℝ) : Params where
  d := d
  q := S.q
  r := S.r
  ρ := S.ρ
  β := β
  LG := C.LG
  KG := C.KG
  LF := C.LF
  KF := C.KF
  rbar := C.rbar
  a := C.a
  b := C.b
  eps := ϵ
  mom := fun s => ∫ ω, (1 + ‖S.X 0 ω‖) ^ s ∂S.P
  momTwo := ∫ ω, (1 + 2 * ‖S.X 0 ω‖) ^ (S.ρ - 1) ∂S.P
  h0 := ‖S.h 0‖
  gibbsV2 := ∫ θ, lyapunov 2 θ ∂S.piBeta β
  gibbsMom := ∫ θ, ‖θ‖ ^ (4 * S.r + 2) ∂S.piBeta β
  thetaMom := ∫ ω, ‖S.θ₀ ω‖ ^ (4 * (2 * S.r + 1)) ∂S.P

/-- `G_λ(θ, x)` of (7), p.5: the componentwise taming and boosting of `G`, with `0 < ε < 1`. -/
noncomputable def Glam (lam ε : ℝ) (θ : Eucl d) (x : Eucl m) : Eucl d :=
  WithLp.toLp 2 fun i =>
    S.G θ x i / (1 + √lam * |S.G θ x i|) * (1 + √lam / (ε + |S.G θ x i|))

/-- `F_λ(θ, x)` of (7), p.5: the taming of `F` by the full norm `|θ|^{2r}`. -/
noncomputable def Flam (lam : ℝ) (θ : Eucl d) (x : Eucl m) : Eucl d :=
  WithLp.toLp 2 fun i => S.F θ x i / (1 + √lam * ‖θ‖ ^ (2 * S.r))

/-- `H_λ(θ, x) := G_λ(θ, x) + F_λ(θ, x)` of (6), p.5. -/
noncomputable def Hlam (lam ε : ℝ) (θ : Eucl d) (x : Eucl m) : Eucl d :=
  S.Glam lam ε θ x + S.Flam lam θ x

/-- **e-THεO POULA**, (5), p.5: `θ^λ₀ := θ₀`,
`θ^λ_{n+1} := θ^λ_n − λ H_λ(θ^λ_n, X_{n+1}) + √(2λβ⁻¹) ξ_{n+1}`. Step `n + 1` reads `X_{n+1}` and
`ξ_{n+1}`, so `ξ₀` is never used. -/
noncomputable def theta (lam β ε : ℝ) : ℕ → Ω → Eucl d
  | 0 => S.θ₀
  | n + 1 => fun ω =>
      theta lam β ε n ω - lam • S.Hlam lam ε (theta lam β ε n ω) (S.X (n + 1) ω)
        + √(2 * lam * β⁻¹) • S.ξ (n + 1) ω

end Model

end EThetaPoula.Risk


