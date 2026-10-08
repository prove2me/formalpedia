-- Prove2me | Definitions.Def_BoydADMM_Convergence_Model
-- name    : BoydADMM_Convergence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:41:01.674991+00:00
-- url     : https://prove2.me/theorems/825759ef-e5a1-4ba2-b448-e29a72cab2d7
-- title:
--   Problem (3.1), the augmented Lagrangian, Assumptions 1–2, ADMM iterations (3.2)–(3.4), residuals and the Lyapunov function $V^k$
-- statement:
--   This file fixes the setting of Chapter 3 and Appendix A.
--
--   **Problem (3.1).** Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ and $g:\mathbb R^m\to\mathbb R\cup\{+\infty\}$, $A\in\mathbb R^{p\times n}$, $B\in\mathbb R^{p\times m}$ and $c\in\mathbb R^p$. The problem is
--
--   $$
--   \text{minimize } f(x)+g(z)\quad\text{subject to } Ax+Bz=c,
--   $$
--
--   with optimal value $p^\star=\inf\{f(x)+g(z)\mid Ax+Bz=c\}$. For a pair $(x,z)$ the **primal residual** is $r=Ax+Bz-c$.
--
--   **Assumption 1.** $f$ and $g$ are closed, proper and convex: the epigraph $\{(x,t)\mid f(x)\le t\}$ is a closed nonempty convex set, and likewise for $g$.
--
--   **Augmented Lagrangian.** For $\rho\ge0$,
--
--   $$
--   L_\rho(x,z,y)=f(x)+g(z)+y^T(Ax+Bz-c)+\frac{\rho}{2}\|Ax+Bz-c\|_2^2 ;
--   $$
--
--   $L_0$ is the (unaugmented) Lagrangian.
--
--   **Assumption 2.** $(x^\star,z^\star,y^\star)$ is a saddle point of $L_0$: $L_0(x^\star,z^\star,y)\le L_0(x^\star,z^\star,y^\star)\le L_0(x,z,y^\star)$ for all $x,z,y$.
--
--   **ADMM (3.2)–(3.4).** For $\rho>0$, sequences $(x^k,z^k,y^k)_{k\ge0}$ form an ADMM run if for every $k\ge0$
--
--   $$
--   x^{k+1}\in\operatorname*{argmin}_x L_\rho(x,z^k,y^k),\qquad
--   z^{k+1}\in\operatorname*{argmin}_z L_\rho(x^{k+1},z,y^k),\qquad
--   y^{k+1}=y^k+\rho(Ax^{k+1}+Bz^{k+1}-c).
--   $$
--
--   The starting state $(z^0,y^0)$ is arbitrary and $x^0$ plays no role.
--
--   **Dual residual and Lyapunov function.** $s^{k+1}=\rho A^TB(z^{k+1}-z^k)$ (§3.3), and, relative to a saddle point, $V^k=(1/\rho)\|y^k-y^\star\|_2^2+\rho\|B(z^k-z^\star)\|_2^2$ (Appendix A).
--
--   These are the objects of every statement in the mission.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin n)`, so $\|\cdot\|$ is the Euclidean norm and `inner ℝ` the dot product; matrices act through `Matrix.toEuclideanLin`. An extended-real-valued $f$ is encoded by its effective domain $C_f=\operatorname{dom}f$ and its real values on $C_f$; values off $C_f$ are never used. Assumption 1 is `ClosedProperConvex`: $C_f$ nonempty, $f$ convex on $C_f$ (which includes convexity of $C_f$), and the epigraph $\{(x,t)\mid x\in C_f,\ f(x)\le t\}$ closed. The saddle-point condition requires $x^\star\in C_f$, $z^\star\in C_g$ and states the right inequality for $x\in C_f$, $z\in C_g$ only; outside the domains $L_0=+\infty$ and the inequality holds trivially, so this is equivalent to the book's "for all $x,z,y$". Minimizations in (3.2)–(3.3) are over the domains, for the same reason. The book claims on p. 16 that Assumption 1 makes the subproblems solvable; this is false in general (e.g. $f(x)=e^{x_1}$ on $\mathbb R^2$ with $A=[0\ 1]$), so an ADMM run is a hypothesis (`IsADMMSeq`, any sequences satisfying (3.2)–(3.4) exactly), never constructed. $p^\star$ is `optVal`, the real infimum over feasible points in the domains; the real `sInf` is $0$ on an empty or unbounded-below set, but under Assumption 2 the feasible set is nonempty and the values are bounded below by $f(x^\star)+g(z^\star)$, so `optVal` is the true $p^\star$ wherever it is used. The problem data are bundled in the structure `Problem n m p`.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), pp. 13–16, (3.1)–(3.4), Assumptions 1–2; p. 18 (residuals r^k, s^k); p. 106 (V^k). DOI 10.1561/2200000016

import Mathlib

namespace BoydADMM.Convergence

/-- The data of problem (3.1) (Boyd et al. 2011, p. 13):
minimize `f(x) + g(z)` subject to `Ax + Bz = c`, with `x ∈ ℝⁿ`, `z ∈ ℝᵐ`, `A ∈ ℝ^{p×n}`,
`B ∈ ℝ^{p×m}`, `c ∈ ℝᵖ`. An extended-real-valued `f : ℝⁿ → ℝ ∪ {+∞}` is encoded by its
effective domain `Cf = dom f = {x | f x < +∞}` and its finite values `f` on `Cf`; the values of
`f` outside `Cf` are never used. Likewise `(Cg, g)` encodes `g`. -/
structure Problem (n m p : ℕ) where
  /-- the effective domain `dom f` -/
  Cf : Set (EuclideanSpace ℝ (Fin n))
  /-- the values of `f` on `dom f` -/
  f : EuclideanSpace ℝ (Fin n) → ℝ
  /-- the effective domain `dom g` -/
  Cg : Set (EuclideanSpace ℝ (Fin m))
  /-- the values of `g` on `dom g` -/
  g : EuclideanSpace ℝ (Fin m) → ℝ
  /-- the matrix `A ∈ ℝ^{p×n}` -/
  A : Matrix (Fin p) (Fin n) ℝ
  /-- the matrix `B ∈ ℝ^{p×m}` -/
  B : Matrix (Fin p) (Fin m) ℝ
  /-- the vector `c ∈ ℝᵖ` -/
  c : EuclideanSpace ℝ (Fin p)

/-- Assumption 1 for one function (p. 16): the extended-real-valued function equal to `f` on `C`
and `+∞` off `C` is closed, proper and convex, i.e. its epigraph
`{(x, t) | x ∈ C, f x ≤ t}` is a closed nonempty convex set. Proper: `C` nonempty (`f > −∞` is
automatic for real values). Convex: `ConvexOn ℝ C f` (which includes convexity of `C`).
Closed: the epigraph is closed. -/
structure ClosedProperConvex {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  nonempty : C.Nonempty
  convexOn : ConvexOn ℝ C f
  isClosed_epigraph : IsClosed {q : EuclideanSpace ℝ (Fin n) × ℝ | q.1 ∈ C ∧ f q.1 ≤ q.2}

namespace Problem

variable {n m p : ℕ} (P : Problem n m p)

/-- `Ax`, the matrix `A` acting on `x ∈ ℝⁿ`. -/
noncomputable def Amul (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin p) :=
  Matrix.toEuclideanLin P.A x

/-- `Bz`, the matrix `B` acting on `z ∈ ℝᵐ`. -/
noncomputable def Bmul (z : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin p) :=
  Matrix.toEuclideanLin P.B z

/-- `Aᵀy`, the transpose of `A` acting on `y ∈ ℝᵖ`. -/
noncomputable def ATmul (y : EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin P.A.transpose y

/-- `Bᵀy`, the transpose of `B` acting on `y ∈ ℝᵖ`. -/
noncomputable def BTmul (y : EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanLin P.B.transpose y

/-- The (primal) residual `r = Ax + Bz − c` (p. 15; `r^k = Ax^k + Bz^k − c`, p. 18). -/
noncomputable def resid (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin p) :=
  P.Amul x + P.Bmul z - P.c

/-- Assumption 1 (p. 16): `f` and `g` are closed, proper and convex. -/
def Assumption1 : Prop :=
  ClosedProperConvex P.Cf P.f ∧ ClosedProperConvex P.Cg P.g

/-- The augmented Lagrangian (p. 13), for `x ∈ dom f`, `z ∈ dom g`:
`L_ρ(x, z, y) = f(x) + g(z) + yᵀ(Ax + Bz − c) + (ρ/2)‖Ax + Bz − c‖₂²`.
The unaugmented Lagrangian `L_0` is the case `ρ = 0`. -/
noncomputable def augLag (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin p)) : ℝ :=
  P.f x + P.g z + inner ℝ y (P.resid x z) + (ρ / 2) * ‖P.resid x z‖ ^ 2

/-- Assumption 2 (p. 16): `(x⋆, z⋆, y⋆)` is a saddle point of `L_0`, i.e.
`L_0(x⋆, z⋆, y) ≤ L_0(x⋆, z⋆, y⋆) ≤ L_0(x, z, y⋆)` for all `x, z, y`. Here `x⋆ ∈ dom f`,
`z⋆ ∈ dom g`, and the right inequality is required for `x ∈ dom f`, `z ∈ dom g` (off the
domains `L_0(x, z, y⋆) = +∞` and it holds trivially). -/
def IsSaddlePoint (xs : EuclideanSpace ℝ (Fin n)) (zs : EuclideanSpace ℝ (Fin m))
    (ys : EuclideanSpace ℝ (Fin p)) : Prop :=
  xs ∈ P.Cf ∧ zs ∈ P.Cg ∧
    (∀ y : EuclideanSpace ℝ (Fin p), P.augLag 0 xs zs y ≤ P.augLag 0 xs zs ys) ∧
    ∀ x ∈ P.Cf, ∀ z ∈ P.Cg, P.augLag 0 xs zs ys ≤ P.augLag 0 x z ys

/-- The optimal value `p⋆ = inf {f(x) + g(z) | Ax + Bz = c}` of (3.1) (p. 13), the infimum
over feasible points in the domains. (As a real `sInf` it is `0` on an empty or unbounded-below
set; under Assumption 2 the set is nonempty and bounded below, so this is the true infimum.) -/
noncomputable def optVal : ℝ :=
  sInf {t : ℝ | ∃ x ∈ P.Cf, ∃ z ∈ P.Cg, P.resid x z = 0 ∧ t = P.f x + P.g z}

/-- The ADMM iterations (3.2)–(3.4) (p. 14) in unscaled form, with penalty `ρ`:
`x^{k+1}` minimizes `L_ρ(·, z^k, y^k)` over `dom f`, `z^{k+1}` minimizes `L_ρ(x^{k+1}, ·, y^k)`
over `dom g`, and `y^{k+1} = y^k + ρ(Ax^{k+1} + Bz^{k+1} − c)`. The sequences are any run of
the method (the minimizers need not be unique); `z 0` and `y 0` are an arbitrary starting
state, and `x 0` is not part of the state (p. 14) and is unconstrained. -/
structure IsADMMSeq (ρ : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (z : ℕ → EuclideanSpace ℝ (Fin m)) (y : ℕ → EuclideanSpace ℝ (Fin p)) : Prop where
  x_mem : ∀ k, x (k + 1) ∈ P.Cf
  x_min : ∀ k, ∀ x' ∈ P.Cf, P.augLag ρ (x (k + 1)) (z k) (y k) ≤ P.augLag ρ x' (z k) (y k)
  z_mem : ∀ k, z (k + 1) ∈ P.Cg
  z_min : ∀ k, ∀ z' ∈ P.Cg,
    P.augLag ρ (x (k + 1)) (z (k + 1)) (y k) ≤ P.augLag ρ (x (k + 1)) z' (y k)
  y_succ : ∀ k, y (k + 1) = y k + ρ • P.resid (x (k + 1)) (z (k + 1))

/-- The dual residual (p. 18): `s^{k+1} = ρAᵀB(z^{k+1} − z^k)`, as a function of the previous
`z^k = zprev` and the new `z^{k+1} = znew`. -/
noncomputable def dualResid (ρ : ℝ) (zprev znew : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) :=
  ρ • P.ATmul (P.Bmul (znew - zprev))

/-- The Lyapunov function of Appendix A (p. 106), relative to a saddle point `(x⋆, z⋆, y⋆)`:
`V = (1/ρ)‖y − y⋆‖₂² + ρ‖B(z − z⋆)‖₂²`, evaluated at a state `(z, y)`. -/
noncomputable def lyapunov (ρ : ℝ) (zs : EuclideanSpace ℝ (Fin m))
    (ys : EuclideanSpace ℝ (Fin p)) (z : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin p)) : ℝ :=
  (1 / ρ) * ‖y - ys‖ ^ 2 + ρ * ‖P.Bmul (z - zs)‖ ^ 2

end Problem

end BoydADMM.Convergence


