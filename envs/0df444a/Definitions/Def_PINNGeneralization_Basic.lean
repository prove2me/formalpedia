-- Prove2me | Definitions.Def_PINNGeneralization_Basic
-- name    : PINNGeneralization_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T05:45:31.181807+00:00
-- url     : https://prove2.me/theorems/eafb2f09-c715-4eaa-9406-cd6ec35e0dc2
-- title:
--   Abstract PDEs, quadrature rules, neural networks and PINN residuals and errors
-- statement:
--   Objects of Sections 2-4 of Mishra and Molinaro (arXiv:2006.16144v3).
--
--   1. **Abstract PDE (Section 2.1).** A measurable domain $\mathbb D\subseteq\mathbb R^{\bar d}$, an exponent $1\le p<\infty$, $Y=L^p(\mathbb D;\mathbb R^m)$, a separable Banach space $X$ with a closed subspace $X^*$, a subspace $Y^*\subseteq L^p(\mathbb D)$ closed in $L^p$, an operator $\mathcal D:X^*\to Y^*$ whose values are functions on $\mathbb D$, and an input $f\in Y^*$, such that for every $g\in Y^*$ there is a unique $v\in X^*$ with $\mathcal D(v)=g$ in $Y$ ((H1), (H2), eq. (2.2)). A solution is $u\in X^*$ with $\mathcal D(u)=f$ a.e. on $\mathbb D$. The residual is $\mathcal R(v)=\mathcal D(v)-f$ (eq. 2.12).
--   2. **Stability (H3), Assumption 2.1, eq. (2.3).** $Z\subseteq X^*$ is a closed subspace with a norm $\|\cdot\|_Z$, $C_{pde}(a,b)>0$, and $\|u-v\|_X\le C_{pde}(\|u\|_Z,\|v\|_Z)\,\|\mathcal D(u)-\mathcal D(v)\|_{L^p(\mathbb D)}$ for all $u,v\in Z$.
--   3. **Quadrature (Section 2.2).** A rule has points $y_1,\dots,y_N$ in a set $S$ and weights $w_i\ge0$; $\bar g_N=\sum_iw_ig(y_i)$. The error bound (2.7) for a class $G$ with a norm $\|\cdot\|$ says: every $g\in G$ is integrable on $S$ and $|\int_Sg-\bar g_N|\le C_{quad}(\|g\|)N^{-\alpha}$. The training error is $\mathcal E_T=(\sum_nw_n|\mathcal R(y_n)|^p)^{1/p}$ (eq. 2.21); in Sections 3-4 its components are $(\sum_nw_n\mathcal R(y_n)^2)^{1/2}$. $\|g\|_{C^k(S)}=\max_{j\le k}\sup_{y\in S}\|D^jg(y)\|$.
--   4. **Neural networks (eqs. 2.8-2.9).** $g=C_K\circ\sigma\circ C_{K-1}\circ\cdots\circ\sigma\circ C_1$ with $K>1$ affine maps $C_kz=W_kz+b_k$ and the activation $\sigma$ applied componentwise.
--   5. **Random training points (Section 2.4.1).** $\mathbb D=[0,1]^{\bar d}$; a training set $\mathbb S=(y_1,\dots,y_N)$ has law $d\mathbb S=dy^{\otimes N}$. With $\mathcal R(\mathbb S)(y)$ the residual at $y$ of the network trained on $\mathbb S$: $\bar{\mathcal E}_G=\int\|u-u^*(\mathbb S)\|_Xd\mathbb S$, $\bar{\mathcal E}_T=\int\frac1N\sum_n|\mathcal R(\mathbb S)(y_n)|d\mathbb S$, $\bar{\mathcal E}_V=\frac1N\int\sum_j|\mathcal R(\mathbb S)(z_j)|d\mathbb S$ for validation points $z_j$, $\mathcal E_{TV}=\mathbb E|\bar{\mathcal E}_T-\bar{\mathcal E}_V|$, and $\mathrm{std}(|\mathcal R|)^2=\int_{\mathbb D}\big(\phi(z)-\int_{\mathbb D}\phi\big)^2dz$ with $\phi(z)=\int|\mathcal R(\mathbb S)(z)|d\mathbb S$ (eqs. 2.24-2.30).
--   6. **Semilinear parabolic equation (Section 3).** $D\subseteq\mathbb R^d$, $d=n+1$, is open, connected, bounded, with $C^k$ boundary (locally, after an orthogonal change of coordinates, the region above the graph of a $C^k$ function). $ds$ is the $(d-1)$-dimensional Hausdorff measure normalised to surface area. A classical solution satisfies $u_t=\Delta u+f(u)$ in $D\times(0,T)$, $u(\cdot,0)=\bar u$ in $D$, $u=0$ on $\partial D\times(0,T)$ (eq. 3.1). The residuals are $\mathcal R_{int}=\partial_tu_\theta-\Delta u_\theta-f(u_\theta)$, $\mathcal R_{sb}=u_\theta$ on $\partial D$, $\mathcal R_{tb}=u_\theta(\cdot,0)-\bar u$ (eqs. 3.3-3.5). $\mathcal E_G=(\int_0^T\int_D|u-u^*|^2)^{1/2}$ (eq. 3.7). $\|v\|_{C^1([0,T]\times\partial D)}=\sup|v|+\sup|\partial_tv|+\sup|\nabla_xv|$ over $\partial D\times[0,T]$; $C_1=(T+(1+2C_f)T^2e^{(1+2C_f)T})^{1/2}$ and $C_{\partial D}=|\partial D|^{1/2}(\|u\|_{C^1([0,T]\times\partial D)}+\|u^*\|_{C^1([0,T]\times\partial D)})$ (eq. 3.13).
--   7. **Viscous scalar conservation law (Section 4).** A classical solution satisfies $u_t+f(u)_x=\nu u_{xx}$ in $(0,1)\times(0,T)$, $u(\cdot,0)=\bar u$ in $(0,1)$, $u(0,t)=u(1,t)=0$ (eq. 4.1). $\mathcal R_{int}=\partial_tu_\theta+\partial_xf(u_\theta)-\nu\partial_{xx}u_\theta$, $\mathcal R_{sb,0}=u_\theta(0,\cdot)$, $\mathcal R_{sb,1}=u_\theta(1,\cdot)$, $\mathcal R_{tb}=u_\theta(\cdot,0)-\bar u$ (eqs. 4.2-4.4). With sup norms over $[0,1]\times[0,T]$ and $M=\max(\|u\|_\infty,\|u^*\|_\infty)$: $C_{f,u,u^*}=\max_{|s|\le M}|f''(s)|\,\|u_x\|_\infty$, $\mathbf C_b=\|u_x\|_\infty+\|u^*_x\|_\infty$, $\bar{\mathbf C}_b=\max_{|s|\le\|u^*\|_\infty}|f'(s)|$.
--
--   **Formalization Note** Points of $\mathbb R^{\bar d}$ are `EuclideanSpace ℝ (Fin n)`. The paper's $Y^*$ and $X^*$ norms are not used and are not modelled separately. The sets $Z$ and $Z^*$ carry arbitrary functions required to be norms on them. The constants $C_{f,u,u^*}$ and $\bar{\mathbf C}_b$ are the values that the proof of Theorem 4.1 establishes; the printed definitions are discussed in the statements that use them.
-- source:
--   Mishra and Molinaro, Estimates on the generalization error of Physics Informed Neural Networks (PINNs) for approximating PDEs, arXiv:2006.16144v3 (2023), Sections 2.1-2.4, 3.1-3.3 and 4.1-4.3

import Mathlib

/-!
Mishra and Molinaro, *Estimates on the generalization error of Physics Informed Neural Networks
(PINNs) for approximating PDEs*, arXiv:2006.16144v3 (2023): the abstract PDE, quadrature rules,
neural networks, residuals and errors of Section 2, the semilinear parabolic equation of Section 3
and the viscous scalar conservation law of Section 4.
-/

open MeasureTheory

noncomputable section

namespace PINNGeneralization

/-- Points of `ℝ^n` with the Euclidean norm. -/
abbrev Pt (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `sup_{y ∈ S} g(y)` (used only for continuous `g` on compact nonempty `S`). -/
def supOn {α : Type*} (S : Set α) (g : α → ℝ) : ℝ := sSup (g '' S)

/-! ### Section 2.3: neural networks -/

/-- Eqs. (2.8)-(2.9): `g = C_K ∘ σ ∘ C_{K-1} ∘ ⋯ ∘ σ ∘ C_1` with `1 < K` affine maps
`C_k z = W_k z + b_k` (layer widths `w 0 = din, w 1, …, w K = dout`; written with `0`-based
layers) and the scalar activation `σ` applied componentwise between them. -/
def IsNeuralNet (σ : ℝ → ℝ) {din dout : ℕ} (g : (Fin din → ℝ) → (Fin dout → ℝ)) : Prop :=
  ∃ (K : ℕ) (w : ℕ → ℕ) (W : ∀ k, Matrix (Fin (w (k + 1))) (Fin (w k)) ℝ)
    (b : ∀ k, Fin (w (k + 1)) → ℝ) (h0 : w 0 = din) (hK : w K = dout)
    (z : ∀ k, (Fin din → ℝ) → (Fin (w k) → ℝ)),
    1 < K ∧ (∀ y, z 0 y = fun i => y (Fin.cast h0 i)) ∧
    (∀ k, k + 1 < K → ∀ y, z (k + 1) y = fun i => σ ((W k).mulVec (z k y) i + b k i)) ∧
    (∀ k, k + 1 = K → ∀ y, z (k + 1) y = (W k).mulVec (z k y) + b k) ∧
    ∀ y, g y = fun i => z K y (Fin.cast hK.symm i)

/-! ### Section 2.1: the abstract PDE -/

/-- The `Y = L^p(𝔻; ℝ^m)` norm `‖g‖_{L^p(𝔻)}` (Section 2.1). -/
def lpNorm {n m : ℕ} (dom : Set (Pt n)) (p : ℝ) (g : Pt n → Pt m) : ℝ :=
  (eLpNorm g (ENNReal.ofReal p) (volume.restrict dom)).toReal

/-- Section 2.1: `nrm` is a norm on the subspace `S` (used for `‖·‖_Z` and `‖·‖_{Z*}`). -/
def IsNormOn {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V) (nrm : V → ℝ) :
    Prop :=
  (∀ v ∈ S, 0 ≤ nrm v) ∧ (∀ v ∈ S, nrm v = 0 → v = 0) ∧
    (∀ (a : ℝ), ∀ v ∈ S, nrm (a • v) = |a| * nrm v) ∧
    ∀ v ∈ S, ∀ v' ∈ S, nrm (v + v') ≤ nrm v + nrm v'

/-- Section 2.1: the subspace `S ⊆ L^p(𝔻)` of functions is closed in `L^p(𝔻)`: an `L^p` limit of
elements of `S` agrees a.e. with an element of `S`. -/
def IsLpClosed {n m : ℕ} (dom : Set (Pt n)) (p : ℝ) (S : Submodule ℝ (Pt n → Pt m)) : Prop :=
  ∀ (g : ℕ → Pt n → Pt m) (h : Pt n → Pt m), (∀ j, g j ∈ S) →
    MemLp h (ENNReal.ofReal p) (volume.restrict dom) →
    Filter.Tendsto (fun j => eLpNorm (g j - h) (ENNReal.ofReal p) (volume.restrict dom))
      Filter.atTop (nhds 0) →
    ∃ h' ∈ S, h' =ᵐ[volume.restrict dom] h

/-- Section 2.1, eq. (2.1): the data of the abstract PDE `D(u) = f`: the domain `𝔻 ⊆ ℝ^{d̄}`, the
exponent `p` of `Y = L^p(𝔻; ℝ^m)`, the closed subspaces `X* ⊆ X` and `Y* ⊆ Y`, the differential
operator `D : X* → Y*` (its values are functions, evaluated pointwise as in (2.15)) and the input
`f ∈ Y*`. -/
structure AbstractPDE (n m : ℕ) (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- the domain `𝔻 ⊆ ℝ^{d̄}` -/
  dom : Set (Pt n)
  /-- the exponent `p` of `Y = L^p(𝔻)` -/
  p : ℝ
  /-- the closed subspace `X* ⊆ X` -/
  Xs : Submodule ℝ X
  /-- the closed subspace `Y* ⊆ Y` -/
  Ys : Submodule ℝ (Pt n → Pt m)
  /-- the differential operator `D` -/
  D : X → Pt n → Pt m
  /-- the input `f` -/
  f : Pt n → Pt m

namespace AbstractPDE

variable {n m : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Section 2.1, (H1)-(H2) of eq. (2.2) and well-posedness: `𝔻` is measurable, `1 ≤ p < ∞`,
`X*` is closed, `Y* ⊆ L^p(𝔻)` is closed, `D` maps `X*` into `Y*`, `f ∈ Y*`, and for every
`g ∈ Y*` there is a unique `v ∈ X*` with `D(v) = g` in `Y`. -/
def Hyp (P : AbstractPDE n m X) : Prop :=
  MeasurableSet P.dom ∧ 1 ≤ P.p ∧ IsClosed (P.Xs : Set X) ∧
    (∀ g ∈ P.Ys, MemLp g (ENNReal.ofReal P.p) (volume.restrict P.dom)) ∧
    IsLpClosed P.dom P.p P.Ys ∧ (∀ v ∈ P.Xs, P.D v ∈ P.Ys) ∧ P.f ∈ P.Ys ∧
    ∀ g ∈ P.Ys, ∃! v, v ∈ P.Xs ∧ P.D v =ᵐ[volume.restrict P.dom] g

/-- `u ∈ X*` solves eq. (2.1), `D(u) = f` in `Y`. -/
def IsSolution (P : AbstractPDE n m X) (u : X) : Prop :=
  u ∈ P.Xs ∧ P.D u =ᵐ[volume.restrict P.dom] P.f

/-- Eq. (2.12): the residual `R(v) = D(v) - f`. -/
def residual (P : AbstractPDE n m X) (v : X) : Pt n → Pt m := fun y => P.D v y - P.f y

/-- Assumption (H3), eq. (2.3): `Z ⊆ X*` is a closed subspace with norm `‖·‖_Z`, `C_pde > 0`, and
`‖u - v‖_X ≤ C_pde(‖u‖_Z, ‖v‖_Z) ‖D(u) - D(v)‖_Y` for all `u, v ∈ Z`. -/
def IsStable (P : AbstractPDE n m X) (Z : Submodule ℝ X) (zNorm : X → ℝ)
    (Cpde : ℝ → ℝ → ℝ) : Prop :=
  IsClosed (Z : Set X) ∧ Z ≤ P.Xs ∧ IsNormOn Z zNorm ∧ (∀ a b, 0 < Cpde a b) ∧
    ∀ v ∈ Z, ∀ w ∈ Z, ‖v - w‖ ≤ Cpde (zNorm v) (zNorm w) * lpNorm P.dom P.p (P.D v - P.D w)

end AbstractPDE

/-! ### Section 2.2: quadrature rules -/

/-- Eq. (2.6): a quadrature rule with `N` points `y_i` and weights `w_i`. -/
structure QuadRule (α : Type*) where
  /-- the number of points -/
  N : ℕ
  /-- the quadrature (training) points -/
  pts : Fin N → α
  /-- the weights -/
  wts : Fin N → ℝ

/-- Section 2.2: the points lie in `S` and the weights are nonnegative (`w_i ∈ ℝ_+`). -/
def QuadRule.IsOn {α : Type*} (Q : QuadRule α) (S : Set α) : Prop :=
  (∀ i, Q.pts i ∈ S) ∧ ∀ i, 0 ≤ Q.wts i

/-- Eq. (2.6): `ḡ_N = ∑_i w_i g(y_i)`. -/
def QuadRule.sum {α : Type*} (Q : QuadRule α) (g : α → ℝ) : ℝ := ∑ i, Q.wts i * g (Q.pts i)

/-- Eq. (2.7) (and (3.9)-(3.11)): for every `g` in the class `G`, `g` is integrable on `S` and
`|∫_S g - ḡ_N| ≤ C_quad(‖g‖) N^{-α}`. -/
def QuadErrorBound {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α)
    (G : Set (α → ℝ)) (nrm : (α → ℝ) → ℝ) (Cquad : ℝ → ℝ) (a : ℝ) (Q : QuadRule α) : Prop :=
  ∀ g ∈ G, IntegrableOn g S μ ∧ |∫ y in S, g y ∂μ - Q.sum g| ≤ Cquad (nrm g) * (Q.N : ℝ) ^ (-a)

/-- Eq. (2.21): the training error `E_T = (∑_n w_n |R(y_n)|^p)^{1/p}`. -/
def trainingError {n m : ℕ} (Q : QuadRule (Pt n)) (p : ℝ) (R : Pt n → Pt m) : ℝ :=
  (Q.sum fun y => ‖R y‖ ^ p) ^ (1 / p)

/-- Eqs. (3.8), (4.7): a component `(∑_n w_n |R(y_n)|²)^{1/2}` of the training error. -/
def quadL2 {α : Type*} (Q : QuadRule α) (R : α → ℝ) : ℝ := Real.sqrt (Q.sum fun y => R y ^ 2)

/-- Sections 3.3 and 4.3: the `C^k` norm `‖g‖_{C^k(S)} = max_{j ≤ k} sup_{y ∈ S} ‖D^j g(y)‖`. -/
def ckNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) (S : Set E)
    (g : E → ℝ) : ℝ :=
  sSup {r | ∃ j ≤ k, ∃ y ∈ S, r = ‖iteratedFDeriv ℝ j g y‖}

/-! ### Section 2.4.1: random training points -/

/-- Section 2.4.1: the unit cube `𝔻 = [0,1]^{d̄}`. -/
def unitCube (n : ℕ) : Set (Pt n) := {y | ∀ i, y i ∈ Set.Icc (0 : ℝ) 1}

/-- Section 2.4.1: the law `d𝕊 = dy ⊗ ⋯ ⊗ dy` of a training set `𝕊 = [y_1, …, y_N] ∈ 𝔻^N` of i.i.d.
uniform points. -/
def trainLaw (n N : ℕ) : Measure (Fin N → Pt n) :=
  Measure.pi fun _ => volume.restrict (unitCube n)

/-- Eq. (2.24): the cumulative generalization error `Ē_G = ∫ ‖u - u*(𝕊)‖_X d𝕊`. -/
def cumGenError {n N : ℕ} {X : Type*} [NormedAddCommGroup X] (u : X)
    (ustar : (Fin N → Pt n) → X) : ℝ :=
  ∫ S, ‖u - ustar S‖ ∂trainLaw n N

/-- Eq. (2.25): the cumulative training error `Ē_T = ∫ (1/N) ∑_n |R(y_n; 𝕊)| d𝕊`, where
`R 𝕊 y` is the residual at `y` of the PINN trained on `𝕊`. -/
def cumTrainError {n m N : ℕ} (R : (Fin N → Pt n) → Pt n → Pt m) : ℝ :=
  ∫ S, (1 / (N : ℝ)) * ∑ j, ‖R S (S j)‖ ∂trainLaw n N

/-- Eq. (2.27): the cumulative validation error `Ē_V = (1/N) ∫ ∑_j |R(z_j; 𝕊)| d𝕊` for the
validation points `z_1, …, z_N`. -/
def cumValError {n m N : ℕ} (R : (Fin N → Pt n) → Pt n → Pt m) (z : Fin N → Pt n) : ℝ :=
  (1 / (N : ℝ)) * ∫ S, ∑ j, ‖R S (z j)‖ ∂trainLaw n N

/-- Eq. (2.28): the validation gap `E_TV = 𝔼 |Ē_T - Ē_V|` over the random validation set. -/
def validationGap {n m N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : (Fin N → Pt n) → Pt n → Pt m) (zval : Fin N → Ω → Pt n) : ℝ :=
  ∫ ω, |cumTrainError R - cumValError R (fun j => zval j ω)| ∂P

/-- Eq. (2.30): `std(|R|) = (𝔼 (∫ |R(z, 𝕊)| d𝕊 - ∫_𝔻 ∫ |R(z, 𝕊)| d𝕊 dz)²)^{1/2}` for `z` uniform on
`𝔻`, written as an integral over `𝔻`. -/
def residualStd {n m N : ℕ} (R : (Fin N → Pt n) → Pt n → Pt m) : ℝ :=
  Real.sqrt (∫ z in unitCube n,
    (∫ S, ‖R S z‖ ∂trainLaw n N - ∫ y in unitCube n, ∫ S, ‖R S y‖ ∂trainLaw n N) ^ 2)

/-! ### Section 3: semilinear parabolic equations on `D ⊆ ℝ^d`, `d = n + 1` -/

/-- Section 3.1: `D ⊆ ℝ^{n+1}` has a `C^k` boundary: near each boundary point, after an orthogonal
change of coordinates, `D` is the region above the graph of a `C^k` function of the first `n`
coordinates. -/
def HasCkBoundary (k : ℕ) {n : ℕ} (D : Set (Pt (n + 1))) : Prop :=
  ∀ x₀ ∈ frontier D, ∃ r > 0, ∃ A : Pt (n + 1) ≃ₗᵢ[ℝ] Pt (n + 1), ∃ γ : (Fin n → ℝ) → ℝ,
    ContDiff ℝ k γ ∧
      D ∩ Metric.ball x₀ r =
        {x | x ∈ Metric.ball x₀ r ∧ γ (fun i => A x (Fin.castSucc i)) < A x (Fin.last n)}

/-- Section 3.1: a domain, i.e. an open connected bounded set, with `C^k` boundary. -/
def IsCkDomain (k : ℕ) {n : ℕ} (D : Set (Pt (n + 1))) : Prop :=
  IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧ HasCkBoundary k D

/-- The surface measure `ds` on hypersurfaces of `ℝ^{n+1}`: the `n`-dimensional Hausdorff
measure, normalised by `ω_n / 2^n` so that it agrees with `n`-dimensional area. -/
def surfaceMeasure (n : ℕ) : Measure (Pt (n + 1)) :=
  ENNReal.ofReal ((volume (Metric.ball (0 : Pt n) 1)).toReal / 2 ^ n) • μH[(n : ℝ)]

/-- The measure `ds(x) dt` on `∂D × [0, T]`. -/
def bdryTimeMeasure {n : ℕ} (D : Set (Pt (n + 1))) (T : ℝ) : Measure (Pt (n + 1) × ℝ) :=
  ((surfaceMeasure n).restrict (frontier D)).prod (volume.restrict (Set.Icc 0 T))

/-- The partial derivative `∂_{x_i} g(x)`. -/
def pd {n : ℕ} (i : Fin n) (g : Pt n → ℝ) (x : Pt n) : ℝ :=
  deriv (fun r : ℝ => g (x + r • EuclideanSpace.single i 1)) 0

/-- The Laplacian `Δg = ∑_i ∂²_{x_i} g`. -/
def lap {n : ℕ} (g : Pt n → ℝ) (x : Pt n) : ℝ := ∑ i, pd i (pd i g) x

/-- The Euclidean length `|∇_x u(x, t)|` of the spatial gradient. -/
def gradNorm {n : ℕ} (u : Pt n → ℝ → ℝ) (x : Pt n) (t : ℝ) : ℝ :=
  Real.sqrt (∑ i, pd i (fun y => u y t) x ^ 2)

/-- Eq. (3.13): `‖u‖_{C^1([0,T] × ∂D)} = sup |u| + sup |∂_t u| + sup |∇_x u|` over
`∂D × [0, T]`. -/
def c1NormBdry {n : ℕ} (D : Set (Pt (n + 1))) (T : ℝ) (u : Pt (n + 1) → ℝ → ℝ) : ℝ :=
  supOn (frontier D ×ˢ Set.Icc 0 T) (fun q => |u q.1 q.2|) +
    supOn (frontier D ×ˢ Set.Icc 0 T) (fun q => |deriv (u q.1) q.2|) +
      supOn (frontier D ×ˢ Set.Icc 0 T) (fun q => gradNorm u q.1 q.2)

/-- Eq. (3.1): `u` is a classical solution of `u_t = Δu + f(u)` in `D × (0, T)`,
`u(x, 0) = ū(x)` in `D`, `u = 0` on `∂D × (0, T)`. -/
def IsHeatSolution {n : ℕ} (D : Set (Pt (n + 1))) (T : ℝ) (f : ℝ → ℝ)
    (ubar : Pt (n + 1) → ℝ) (u : Pt (n + 1) → ℝ → ℝ) : Prop :=
  (∀ x ∈ D, ∀ t ∈ Set.Ioo 0 T, deriv (u x) t = lap (fun y => u y t) x + f (u x t)) ∧
    (∀ x ∈ D, u x 0 = ubar x) ∧ ∀ x ∈ frontier D, ∀ t ∈ Set.Ioo 0 T, u x t = 0

/-- Section 3.2: `u*` is (the realization of) a neural network (2.8) of the space-time variable
`(x, t) ∈ ℝ^{n+2}` with scalar output. -/
def IsPINN {n : ℕ} (σ : ℝ → ℝ) (ustar : Pt (n + 1) → ℝ → ℝ) : Prop :=
  ∃ g : (Fin (n + 1 + 1) → ℝ) → (Fin 1 → ℝ), IsNeuralNet σ g ∧
    ∀ x t, ustar x t = g (Fin.snoc (α := fun _ => ℝ) (fun i => x i) t) 0

/-- Eq. (3.3): the interior residual `∂_t u_θ - Δu_θ - f(u_θ)`. -/
def heatResInt {n : ℕ} (f : ℝ → ℝ) (v : Pt (n + 1) → ℝ → ℝ) (x : Pt (n + 1)) (t : ℝ) : ℝ :=
  deriv (v x) t - lap (fun y => v y t) x - f (v x t)

/-- Eq. (3.5): the temporal boundary residual `u_θ(x, 0) - ū(x)`. -/
def heatResTb {n : ℕ} (ubar : Pt (n + 1) → ℝ) (v : Pt (n + 1) → ℝ → ℝ) (x : Pt (n + 1)) : ℝ :=
  v x 0 - ubar x

/-- Eq. (3.7) (also (4.6)): the generalization error `(∫_0^T ∫_D |u - u*|² dx dt)^{1/2}`. -/
def genErrorL2 {E : Type*} [MeasureSpace E] (D : Set E) (T : ℝ) (u ustar : E → ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ t in Set.Ioo 0 T, ∫ x in D, (u x t - ustar x t) ^ 2)

/-- Eq. (3.13): `C_1 = (T + (1 + 2C_f) T² e^{(1 + 2C_f)T})^{1/2}`. -/
def heatC1 (T Cf : ℝ) : ℝ :=
  Real.sqrt (T + (1 + 2 * Cf) * T ^ 2 * Real.exp ((1 + 2 * Cf) * T))

/-- Eq. (3.13): `C_{∂D}(u, u*) = |∂D|^{1/2} (‖u‖_{C^1([0,T]×∂D)} + ‖u*‖_{C^1([0,T]×∂D)})`. -/
def heatCbdry {n : ℕ} (D : Set (Pt (n + 1))) (T : ℝ) (u ustar : Pt (n + 1) → ℝ → ℝ) : ℝ :=
  Real.sqrt ((surfaceMeasure n (frontier D)).toReal) * (c1NormBdry D T u + c1NormBdry D T ustar)

/-! ### Section 4: viscous scalar conservation laws on `(0, 1)` -/

/-- The closed space-time rectangle `[0, 1] × [0, T]`. -/
def rect (T : ℝ) : Set (ℝ × ℝ) := Set.Icc 0 1 ×ˢ Set.Icc 0 T

/-- `∂_x v(x, t)`. -/
def dx (v : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ := deriv (fun y => v y t) x

/-- Eq. (4.1): `u` is a classical solution of `u_t + f(u)_x = ν u_xx` in `(0, 1) × (0, T)`,
`u(x, 0) = ū(x)` in `(0, 1)`, `u(0, t) = u(1, t) = 0` for `t ∈ [0, T]`. -/
def IsVSCLSolution (T ν : ℝ) (f ubar : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Ioo 0 T,
      deriv (u x) t + deriv (fun y => f (u y t)) x = ν * deriv (fun y => dx u y t) x) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, u x 0 = ubar x) ∧ ∀ t ∈ Set.Icc 0 T, u 0 t = 0 ∧ u 1 t = 0

/-- Section 4.2: `u*` is (the realization of) a neural network (2.8) of `(x, t) ∈ ℝ²` with
scalar output. -/
def IsPINN1D (σ : ℝ → ℝ) (ustar : ℝ → ℝ → ℝ) : Prop :=
  ∃ g : (Fin 2 → ℝ) → (Fin 1 → ℝ), IsNeuralNet σ g ∧ ∀ x t, ustar x t = g ![x, t] 0

/-- Eq. (4.2): the interior residual `∂_t u_θ + ∂_x f(u_θ) - ν ∂_xx u_θ`. -/
def vsclResInt (ν : ℝ) (f : ℝ → ℝ) (v : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (v x) t + deriv (fun y => f (v y t)) x - ν * deriv (fun y => dx v y t) x

/-- Eq. (4.4): the temporal boundary residual `u_θ(x, 0) - ū(x)`. -/
def vsclResTb (ubar : ℝ → ℝ) (v : ℝ → ℝ → ℝ) (x : ℝ) : ℝ := v x 0 - ubar x

/-- Eq. (4.9), as used in the proof ((4.14)-(4.15)): `C_{f,u,u*} = max_{|s| ≤ M} |f''(s)| ‖u_x‖_∞`
with `M = max(‖u‖_∞, ‖u*‖_∞)`, all norms over `[0,1] × [0,T]`. -/
def vsclCf (T : ℝ) (f : ℝ → ℝ) (u ustar : ℝ → ℝ → ℝ) : ℝ :=
  supOn (Set.Icc (-max (supOn (rect T) (fun q => |u q.1 q.2|))
      (supOn (rect T) (fun q => |ustar q.1 q.2|)))
      (max (supOn (rect T) (fun q => |u q.1 q.2|)) (supOn (rect T) (fun q => |ustar q.1 q.2|))))
    (fun s => |deriv (deriv f) s|) *
  supOn (rect T) (fun q => |dx u q.1 q.2|)

/-- Eq. (4.9): `𝐂_b = ‖u_x‖_{C([0,1]×[0,T])} + ‖u*_x‖_{C([0,1]×[0,T])}`. -/
def vsclCb (T : ℝ) (u ustar : ℝ → ℝ → ℝ) : ℝ :=
  supOn (rect T) (fun q => |dx u q.1 q.2|) + supOn (rect T) (fun q => |dx ustar q.1 q.2|)

/-- Theorem 4.1, as used in its proof: `𝐂̄_b = max_{|s| ≤ ‖u*‖_{C^0([0,1]×[0,T])}} |f'(s)|`. -/
def vsclCbarb (T : ℝ) (f : ℝ → ℝ) (ustar : ℝ → ℝ → ℝ) : ℝ :=
  supOn (Set.Icc (-supOn (rect T) (fun q => |ustar q.1 q.2|))
      (supOn (rect T) (fun q => |ustar q.1 q.2|)))
    (fun s => |deriv f s|)

end PINNGeneralization


