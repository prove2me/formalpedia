-- Prove2me | Definitions.Def_FullyCoupledSDE_Poisson_Setting
-- name    : FullyCoupledSDE_Poisson_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:24:53.117724+00:00
-- url     : https://prove2.me/theorems/8480ff1d-8274-4dc4-a367-61384d94992f
-- title:
--   Notations (p. 1209), (1.1)–(1.3), (Aσ), (Ab), (3.7) — the operator L0, ∂_yL0, the invariant family μ^y, centering, weighted Hölder classes
-- statement:
--   This module fixes the objects of the parametric Poisson equation of Röckner and Xie. Throughout, $x\in\mathbb R^{d_1}$ is the fast variable and $y\in\mathbb R^{d_2}$ a parameter; the coefficients are a matrix field $a(x,y)=(a^{ij}(x,y))_{i,j\le d_1}$ and a vector field $b(x,y)\in\mathbb R^{d_1}$.
--
--   1. **The frozen operator** (1.2). For fixed $y$ and a twice differentiable function $u$ of $x$,
--   $$\mathscr L_0(x,y)u(x)=\sum_{i,j=1}^{d_1}a^{ij}(x,y)\,\frac{\partial^2u}{\partial x_i\partial x_j}(x)+\sum_{i=1}^{d_1}b^i(x,y)\,\frac{\partial u}{\partial x_i}(x).$$
--   The Poisson equation (1.1) is $\mathscr L_0(x,y)u(x,y)=f(x,y)$ for all $x$, with $y$ a parameter.
--   2. **The $y$-derivative of the operator** (p. 1214, $\ell=1$). For a direction $v\in\mathbb R^{d_2}$, $\frac{\partial\mathscr L_0}{\partial y}(x,y)\cdot v$ is the operator (1.2) with $a^{ij},b^i$ replaced by $\partial_ya^{ij}(x,y)\cdot v$ and $\partial_yb^i(x,y)\cdot v$.
--   3. **(Aσ)** (p. 1209): $a(x,y)$ is symmetric positive semidefinite (it is $\sigma\sigma^*$), and there is $\lambda>1$ with $\lambda^{-1}|\xi|^2\le|a(x,y)\xi|^2\le\lambda|\xi|^2$ for all $x,y,\xi$.
--   4. **(Ab)** (p. 1210): $\lim_{|x|\to\infty}\sup_y\langle x,b(x,y)\rangle=-\infty$, i.e. for every $M$ there is $R$ with $\langle x,b(x,y)\rangle\le M$ whenever $|x|\ge R$.
--   5. **The invariant family** $\mu^y$ (below (1.3) and (1.7)): for each $y$, $\mu^y$ is a probability measure on $\mathbb R^{d_1}$ with $\int\mathscr L_0(x,y)g(x)\,\mu^y(dx)=0$ for every smooth compactly supported $g$.
--   6. **Centering** (1.3): $f(\cdot,y)$ is $\mu^y$-integrable and $\int f(x,y)\,\mu^y(dx)=0$ for every $y$. The **average** (3.7) is $\bar h(y)=\int h(x,y)\,\mu^y(dx)$.
--   7. **Weighted Hölder classes** (Notations, p. 1209), for $0<\delta\le1$:
--      - $C^{\delta,0}_p$: there are $C,m>0$ with $|f(x,y)|\le C(1+|x|^m)$ and $|f(x_1,y)-f(x_2,y)|\le C(|x_1-x_2|^\delta\wedge1)(1+|x_1|^m+|x_2|^m)$;
--      - $C^{\delta,\vartheta}_p$, $0<\vartheta<1$: the growth bound and $|f(x_1,y_1)-f(x_2,y_2)|\le C[(|x_1-x_2|^\delta\wedge1)+(|y_1-y_2|^\vartheta\wedge1)](1+|x_1|^m+|x_2|^m)$;
--      - the bounded versions $C^{\delta,0}_b$, $C^{\delta,\vartheta}_b$ (weight $1$, $|f|\le C$);
--      - for real $\eta\ge0$ with $k=[\eta]$, $\vartheta=\eta-k$: $f\in C^{\delta,\eta}_p$ if $f(x,\cdot)$ is $C^k$, $\partial^j_yf\in C^{\delta,0}_p$ for $j<k$ and $\partial^k_yf\in C^{\delta,\vartheta}_p$ (in $C^{\delta,0}_p$ if $\vartheta=0$); likewise $C^{\delta,\eta}_b$;
--      - $C^{2+\delta,\eta}_p$: for every $j\le k$, $\partial^j_yu$ is $C^2$ in $x$, it and its $x$-gradient grow polynomially, and $\nabla^2_x\partial^j_yu\in C^{\delta,0}_p$ ($j<k$), respectively $\in C^{\delta,\vartheta}_p$ ($j=k$);
--      - $\|g\|_{C^\eta_b(\mathbb R^{d_2})}\le K$: $g$ is $C^k$, $|\partial^jg|\le K$ for $j\le k$, and $|\partial^kg(y_1)-\partial^kg(y_2)|\le K|y_1-y_2|^\vartheta$ when $\vartheta>0$.
--
--   These are the objects in which Theorem 2.1 and Lemma 3.2 are stated.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. Second derivatives are `iteratedFDeriv ℝ 2`, so norms of $\nabla_x u$, $\nabla^2_x u$ and $\partial^j_y u$ are operator norms (equivalent to the Euclidean ones up to dimensional constants). The paper defines $\mu^y$ as the unique invariant measure of the frozen SDE (1.7); here it is read analytically as an infinitesimally invariant probability measure, which under (Aσ), (Ab) and bounded Hölder coefficients exists, is unique, and is that invariant measure (Bogachev–Krylov–Röckner). Positive semidefiniteness of $a$ is the content of "$a=\sigma\sigma^*$"; the printed inequality alone admits $a=-I$. Matrix coefficients are in $C^{\delta,\eta}_b$ entrywise. The classes include the growth bound and all lower $y$-derivatives (the page states only the top one), and for $x$-index $2+\delta$ with $\delta=1$ the Hölder clause ($\nabla^2_x u$ Lipschitz) is used. A $y$-derivative "exists" is read as $C^k$ in $y$. The $C^\eta_b$ norm is in max form (equivalent to the sum form up to a factor $k+2$).
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), pp. 1205–1207, (1.1)–(1.3), (1.7); p. 1209, Notations, (Aσ); p. 1210, (Ab); p. 1214, ∂^ℓL0/∂y^ℓ and (3.7)

import Mathlib

namespace FullyCoupledSDE.Poisson

open MeasureTheory
open scoped ContDiff

/-- The Euclidean space `ℝ^d`. Points of the fast variable live in `E d1`, the parameter in `E d2`. -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The `i`-th standard basis vector `e_i` of `ℝ^d`. -/
noncomputable def e {d : ℕ} (i : Fin d) : E d := EuclideanSpace.single i (1 : ℝ)

variable {d1 d2 : ℕ}

/-! ### The operator `L0` (1.2) and its `y`-derivative (p. 1214) -/

/-- The frozen operator (1.2): for fixed `y` and a function `u` of `x` only,
`L0 a b y u x = Σ_{i,j} a^{ij}(x,y) ∂²u/∂x_i∂x_j (x) + Σ_i b^i(x,y) ∂u/∂x_i (x)`. -/
noncomputable def L0 (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (y : E d2) (u : E d1 → ℝ) (x : E d1) : ℝ :=
  (∑ i, ∑ j, a x y i j * iteratedFDeriv ℝ 2 u x ![e i, e j]) +
    ∑ i, b x y i * fderiv ℝ u x (e i)

/-- `∂L0/∂y` in the direction `v ∈ ℝ^{d2}` (p. 1214, `ℓ = 1`): the operator (1.2) with the
coefficients `a^{ij}`, `b^i` replaced by their directional derivatives `∂_y a^{ij}(x,y)·v`,
`∂_y b^i(x,y)·v`. -/
noncomputable def dL0 (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (y v : E d2) (u : E d1 → ℝ) (x : E d1) : ℝ :=
  (∑ i, ∑ j, fderiv ℝ (fun y' => a x y' i j) y v * iteratedFDeriv ℝ 2 u x ![e i, e j]) +
    ∑ i, fderiv ℝ (fun y' => b x y' i) y v * fderiv ℝ u x (e i)

/-! ### Assumptions (Aσ) and (Ab) (pp. 1209–1210) -/

/-- (Aσ): `a = σσ*` (so `a(x,y)` is symmetric positive semidefinite) and there is `Λ > 1` with
`Λ⁻¹|ξ|² ≤ |a(x,y)ξ|² ≤ Λ|ξ|²` for all `x, y, ξ`. -/
def AssumpSigma (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) : Prop :=
  (∀ x y, (a x y).PosSemidef) ∧
    ∃ Λ : ℝ, 1 < Λ ∧ ∀ (x : E d1) (y : E d2) (ξ : Fin d1 → ℝ),
      Λ⁻¹ * dotProduct ξ ξ ≤ dotProduct ((a x y).mulVec ξ) ((a x y).mulVec ξ) ∧
        dotProduct ((a x y).mulVec ξ) ((a x y).mulVec ξ) ≤ Λ * dotProduct ξ ξ

/-- (Ab): `lim_{|x|→∞} sup_y ⟨x, b(x,y)⟩ = -∞`, i.e. for every `M` there is `R` such that
`⟨x, b(x,y)⟩ ≤ M` for all `y` and all `|x| ≥ R`. -/
def AssumpB (b : E d1 → E d2 → E d1) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ (x : E d1) (y : E d2), R ≤ ‖x‖ → inner ℝ x (b x y) ≤ M

/-! ### The invariant family `μ^y` (below (1.3), (1.7)), centering (1.3), the average (3.7) -/

/-- `μ y` is, for every `y`, a probability measure on `ℝ^{d1}` that is infinitesimally invariant
for the frozen generator `L0(·, y)`: `∫ L0(·,y) g dμ^y = 0` for every smooth compactly supported
`g`. This is the analytic characterization of the invariant measure of the frozen SDE (1.7). -/
def IsInvariantFamily (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (μ : E d2 → Measure (E d1)) : Prop :=
  (∀ y, IsProbabilityMeasure (μ y)) ∧
    ∀ (y : E d2) (g : E d1 → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      Integrable (fun x => L0 a b y g x) (μ y) ∧ ∫ x, L0 a b y g x ∂(μ y) = 0

/-- The centering condition (1.3): for every `y`, `f(·, y)` is `μ^y`-integrable with integral `0`. -/
def Centered (μ : E d2 → Measure (E d1)) (f : E d1 → E d2 → ℝ) : Prop :=
  ∀ y, Integrable (fun x => f x y) (μ y) ∧ ∫ x, f x y ∂(μ y) = 0

/-- The average (3.7): `h̄(y) = ∫ h(x, y) μ^y(dx)`. -/
noncomputable def avg (μ : E d2 → Measure (E d1)) (h : E d1 → E d2 → ℝ) (y : E d2) : ℝ :=
  ∫ x, h x y ∂(μ y)

/-! ### Weighted Hölder classes (Notations, p. 1209) -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `j`-th derivative in `y`: `∂^j_y g(x, y)`, a `j`-multilinear map on `ℝ^{d2}`. -/
noncomputable def Dy (j : ℕ) (g : E d1 → E d2 → F) (x : E d1) (y : E d2) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => E d2) F :=
  iteratedFDeriv ℝ j (g x) y

/-- The gradient in `x`: `∇_x w(x, y)`. -/
noncomputable def D1x (w : E d1 → E d2 → F) (x : E d1) (y : E d2) : E d1 →L[ℝ] F :=
  fderiv ℝ (fun x' => w x' y) x

/-- The Hessian in `x`: `∇²_x w(x, y)`, a bilinear map on `ℝ^{d1}`. -/
noncomputable def D2x (w : E d1 → E d2 → F) (x : E d1) (y : E d2) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E d1) F :=
  iteratedFDeriv ℝ 2 (fun x' => w x' y) x

/-- Polynomial growth in `x`, uniformly in `y`: `|g(x,y)| ≤ C(1 + |x|^m)`. -/
def PolyGrowth (g : E d1 → E d2 → F) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ m : ℝ, 0 < m ∧ ∀ (x : E d1) (y : E d2), ‖g x y‖ ≤ C * (1 + ‖x‖ ^ m)

/-- `C^{δ,0}_p` (`0 < δ ≤ 1`): polynomial growth in `x` uniformly in `y`, and
`|g(x1,y) − g(x2,y)| ≤ C(|x1 − x2|^δ ∧ 1)(1 + |x1|^m + |x2|^m)`. -/
def CpX (δ : ℝ) (g : E d1 → E d2 → F) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ m : ℝ, 0 < m ∧
    (∀ (x : E d1) (y : E d2), ‖g x y‖ ≤ C * (1 + ‖x‖ ^ m)) ∧
    ∀ (x1 x2 : E d1) (y : E d2),
      ‖g x1 y - g x2 y‖ ≤ C * min (‖x1 - x2‖ ^ δ) 1 * (1 + ‖x1‖ ^ m + ‖x2‖ ^ m)

/-- `C^{δ,ϑ}_p` (`0 < δ ≤ 1`, `0 < ϑ < 1`): polynomial growth in `x` and
`|g(x1,y1) − g(x2,y2)| ≤ C[(|x1 − x2|^δ ∧ 1) + (|y1 − y2|^ϑ ∧ 1)](1 + |x1|^m + |x2|^m)`. -/
def CpXY (δ θ : ℝ) (g : E d1 → E d2 → F) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ m : ℝ, 0 < m ∧
    (∀ (x : E d1) (y : E d2), ‖g x y‖ ≤ C * (1 + ‖x‖ ^ m)) ∧
    ∀ (x1 x2 : E d1) (y1 y2 : E d2),
      ‖g x1 y1 - g x2 y2‖ ≤
        C * (min (‖x1 - x2‖ ^ δ) 1 + min (‖y1 - y2‖ ^ θ) 1) * (1 + ‖x1‖ ^ m + ‖x2‖ ^ m)

/-- `C^{δ,0}_b`: bounded, and `|g(x1,y) − g(x2,y)| ≤ C(|x1 − x2|^δ ∧ 1)`. -/
def CbX (δ : ℝ) (g : E d1 → E d2 → F) : Prop :=
  ∃ C : ℝ, 0 < C ∧ (∀ (x : E d1) (y : E d2), ‖g x y‖ ≤ C) ∧
    ∀ (x1 x2 : E d1) (y : E d2), ‖g x1 y - g x2 y‖ ≤ C * min (‖x1 - x2‖ ^ δ) 1

/-- `C^{δ,ϑ}_b` (`0 < ϑ < 1`): bounded, and
`|g(x1,y1) − g(x2,y2)| ≤ C[(|x1 − x2|^δ ∧ 1) + (|y1 − y2|^ϑ ∧ 1)]`. -/
def CbXY (δ θ : ℝ) (g : E d1 → E d2 → F) : Prop :=
  ∃ C : ℝ, 0 < C ∧ (∀ (x : E d1) (y : E d2), ‖g x y‖ ≤ C) ∧
    ∀ (x1 x2 : E d1) (y1 y2 : E d2),
      ‖g x1 y1 - g x2 y2‖ ≤ C * (min (‖x1 - x2‖ ^ δ) 1 + min (‖y1 - y2‖ ^ θ) 1)

/-- `C^{δ,η}_p` for real `η ≥ 0`, with `k = ⌊η⌋` and `θ = η − k`: `g(x,·)` is `C^k` (when `k ≥ 1`),
the `y`-derivatives `∂^j_y g` for `j < k` lie in `C^{δ,0}_p`, and the top one `∂^k_y g` lies in
`C^{δ,θ}_p` (in `C^{δ,0}_p` when `θ = 0`). -/
def Cp (δ η : ℝ) (g : E d1 → E d2 → F) : Prop :=
  (0 < ⌊η⌋₊ → ∀ x, ContDiff ℝ (⌊η⌋₊ : ℕ) (g x)) ∧
    (∀ j < ⌊η⌋₊, CpX δ (Dy j g)) ∧
    (if η - ⌊η⌋₊ = 0 then CpX δ (Dy ⌊η⌋₊ g) else CpXY δ (η - ⌊η⌋₊) (Dy ⌊η⌋₊ g))

/-- `C^{δ,η}_b` for real `η ≥ 0`: as `Cp` with the bounded classes `C^{δ,0}_b`, `C^{δ,θ}_b`. -/
def Cb (δ η : ℝ) (g : E d1 → E d2 → F) : Prop :=
  (0 < ⌊η⌋₊ → ∀ x, ContDiff ℝ (⌊η⌋₊ : ℕ) (g x)) ∧
    (∀ j < ⌊η⌋₊, CbX δ (Dy j g)) ∧
    (if η - ⌊η⌋₊ = 0 then CbX δ (Dy ⌊η⌋₊ g) else CbXY δ (η - ⌊η⌋₊) (Dy ⌊η⌋₊ g))

/-- A matrix-valued coefficient lies in `C^{δ,η}_b` when each entry does. -/
def CbMat (δ η : ℝ) (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) : Prop :=
  ∀ i j, Cb δ η (fun x y => a x y i j)

/-- The `x`-part of `C^{2+δ,θ}_p` for one function `w` (`0 < δ ≤ 1`, `0 ≤ θ < 1`): `w(·, y)` is
`C²` for every `y`; `w`, `∇_x w` have polynomial growth; and `∇²_x w` lies in `C^{δ,0}_p`
(`θ = 0`) or `C^{δ,θ}_p` (`θ > 0`). -/
def C2pX (δ θ : ℝ) (w : E d1 → E d2 → F) : Prop :=
  (∀ y, ContDiff ℝ 2 (fun x => w x y)) ∧ PolyGrowth w ∧ PolyGrowth (D1x w) ∧
    (if θ = 0 then CpX δ (D2x w) else CpXY δ θ (D2x w))

/-- `C^{2+δ,η}_p` for real `η ≥ 0`, with `k = ⌊η⌋`, `θ = η − k`: `u(x,·)` is `C^k` (when `k ≥ 1`),
each `∂^j_y u` (`j < k`) satisfies `C2pX δ 0`, and `∂^k_y u` satisfies `C2pX δ θ`; that is,
`∂²_x ∂^j_y u ∈ C^{δ,0}_p` for `j < k` and `∂²_x ∂^k_y u ∈ C^{δ,θ}_p`, together with the lower
derivatives and their growth. -/
def Cp2 (δ η : ℝ) (u : E d1 → E d2 → ℝ) : Prop :=
  (0 < ⌊η⌋₊ → ∀ x, ContDiff ℝ (⌊η⌋₊ : ℕ) (u x)) ∧
    (∀ j < ⌊η⌋₊, C2pX δ 0 (Dy j u)) ∧
    C2pX δ (η - ⌊η⌋₊) (Dy ⌊η⌋₊ u)

/-- `‖g‖_{C^η_b(ℝ^{d2})} ≤ K` (max form) for `g : ℝ^{d2} → F`, `η ≥ 0`, `k = ⌊η⌋`, `θ = η − k`:
`g` is `C^k`, `|∂^j g| ≤ K` for `j ≤ k`, and, when `θ > 0`,
`|∂^k g(y1) − ∂^k g(y2)| ≤ K |y1 − y2|^θ`. -/
def CbYNormLe (η : ℝ) (g : E d2 → F) (K : ℝ) : Prop :=
  ContDiff ℝ (⌊η⌋₊ : ℕ) g ∧
    (∀ j ≤ ⌊η⌋₊, ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ K) ∧
    (0 < η - ⌊η⌋₊ → ∀ y1 y2,
      ‖iteratedFDeriv ℝ ⌊η⌋₊ g y1 - iteratedFDeriv ℝ ⌊η⌋₊ g y2‖ ≤ K * ‖y1 - y2‖ ^ (η - ⌊η⌋₊))

/-- `g ∈ C^η_b(ℝ^{d2})`. -/
def CbY (η : ℝ) (g : E d2 → F) : Prop := ∃ K : ℝ, CbYNormLe η g K

end FullyCoupledSDE.Poisson


