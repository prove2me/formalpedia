-- Prove2me | Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
-- name    : BirkhoffGlobalSection_DynamicalConvexity
-- status  : Definition
-- author  : @caleb
-- created : 2026-09-28T00:36:52.513993+00:00
-- url     : https://prove2.me/theorems/0b7f7c2d-c471-482b-892a-cbf3b990d95b
-- title:
--   Dynamical convexity in winding form (Conley–Zehnder index at least 3)
-- statement:
--   Dynamical convexity of a Hamiltonian flow on a regular energy surface in $\mathbb{R}^4$, stated through the winding of the transverse linearized flow.
--
--   Let $F:\mathbb{R}^4\to\mathbb{R}$ be a Hamiltonian in the coordinates $(q_1,q_2,p_1,p_2)$, with Hamiltonian vector field $X_F=I\nabla F=(\partial_{p}F,-\partial_{q}F)$. Here $I,J,K$ are the quaternionic matrices of `Def_BirkhoffGlobalSection_TangentialHessian`, which satisfy $IJ=K$. At a point with gradient $g=\nabla F\neq0$, the vectors $Ig,Jg,Kg$ form an orthogonal basis of the tangent space $g^{\perp}$ of the level set, and $Ig$ spans the flow direction. For a vector $w$ set
--
--   $$
--   \tau_g(w)=\big(\langle w,Jg\rangle,\ \langle w,Kg\rangle\big)\in\mathbb{R}^2 .
--   $$
--
--   On $g^{\perp}$ this map vanishes exactly on the flow direction, so it trivializes the transverse plane bundle of the level set. Let $S\subset\mathbb{R}^4$.
--
--   1. A closed solution in $S$ is a solution $x$ of $\dot x=X_F(x)$ with $x(t)\in S$ for all $t$ and $x(T)=x(0)$ for some $T>0$. The time $T$ need not be the least period, so multiple covers are included.
--   2. Let $Y$ solve the variational equation $\dot Y(t)=DX_F(x(t))\,Y(t)$ with $Y(0)=\mathrm{id}$. Take a tangent vector $v$ at $x(0)$ with $\tau_{g(0)}(v)\neq0$, where $g(t)=\nabla F(x(t))$, and write $\tau_{g(t)}(Y(t)v)=\rho(t)\,(\cos\theta(t),\sin\theta(t))$ with $\rho>0$ and $\theta$ continuous. The closed solution has transverse winding above one if, for all such $v$ and $\theta$,
--
--   $$
--   \theta(T)-\theta(0)>2\pi .
--   $$
--
--   3. The flow of $F$ is dynamically convex on $S$ if every closed solution in $S$ has transverse winding above one.
--
--   By the winding-interval description of the Conley–Zehnder index, a closed orbit has winding above one exactly when its index in this global frame is at least $3$, where degenerate orbits use the lower semicontinuous extension of the index. So item 3 is dynamical convexity in the sense of Hofer–Wysocki–Zehnder. With this orientation, the Hopf fibers of the round three-sphere wind exactly twice per period. On the Levi-Civita double cover of a regularized $\mathbb{R}P^3$ component, the closed orbits are the lifts of the contractible orbits downstairs. For such a cover this is therefore the dynamical convexity used by Liu–Salomão in Definition 1.10(i) and Theorem 1.16(i).
--
--   **Formalization Note** `transverseFrameCoordinates g w` is $\tau_g(w)$, built from `TangentialHessian.frame` and `TangentialHessian.grad`. `IsPeriodicHamiltonianSolutionIn F S x T` is item 1, `HasTransverseWindingAboveOne F x T` is item 2, and `IsDynamicallyConvexOn F S` is item 3. The linearized flow and the polar angle are quantified over all of their solutions and continuous lifts. Both exist, and the angle difference does not depend on the choice.
-- source:
--   Hofer--Wysocki--Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998): dynamical convexity means every periodic orbit has Conley--Zehnder index at least 3. Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2, Definition 1.10(i) and Theorem 1.16(i). Quaternionic frame as in Def_BirkhoffGlobalSection_TangentialHessian (Joung--van Koert, Section 2.3).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection

noncomputable section

/-- Coordinates of `w` against the quaternionic vectors `J g` and `K g` of the
frame `I g, J g, K g` built from a gradient `g`. On the tangent space `g^⊥` of
a regular level set they vanish exactly on the Hamiltonian direction `I g`, so
they trivialize the transverse plane bundle of the level set. With this order,
positive rotation is counterclockwise: along a Hopf fiber of the round sphere
the linearized flow turns every transverse vector twice per period. -/
def transverseFrameCoordinates (g w : Phase) : Plane :=
  ![w ⬝ᵥ TangentialHessian.frame g 1, w ⬝ᵥ TangentialHessian.frame g 2]

/-- `x` solves Hamilton's equations for `F`, stays in `S`, and closes up after
the time `T > 0`. The time `T` need not be the least period. -/
def IsPeriodicHamiltonianSolutionIn (F : Phase → ℝ) (S : Set Phase)
    (x : ℝ → Phase) (T : ℝ) : Prop :=
  0 < T ∧ (∀ t : ℝ, x t ∈ S) ∧
    (∀ t : ℝ, HasDerivAt x (hamiltonianVectorField F (x t)) t) ∧
    x T = x 0

/-- Along the closed solution `x` of period `T`, the linearized flow turns every
tangent vector transverse to the flow by more than one full turn, measured
in the frame coordinates `transverseFrameCoordinates`. The linearized flow is
the solution `Y` of the variational equation with `Y 0 = id`. The angle is any
continuous polar angle of the frame coordinates.

This is the winding-interval form of the condition that the Conley--Zehnder
index of `(x, T)` is at least `3`, in the global frame. Degenerate orbits use
the lower semicontinuous extension of the index. -/
def HasTransverseWindingAboveOne (F : Phase → ℝ) (x : ℝ → Phase) (T : ℝ) :
    Prop :=
  ∀ Y : ℝ → (Phase →L[ℝ] Phase),
    Y 0 = ContinuousLinearMap.id ℝ Phase →
    (∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField F) (x t)).comp (Y t)) t) →
    ∀ v : Phase, fderiv ℝ F (x 0) v = 0 →
      transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0 →
      ∀ θ : ℝ → ℝ, Continuous θ →
        (∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
          transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) =
            ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)]) →
        2 * Real.pi < θ T - θ 0

/-- Dynamical convexity of the Hamiltonian flow of `F` on `S`: every closed
solution in `S`, including every multiple cover, has transverse winding above
one. Equivalently, every periodic orbit in `S` has Conley--Zehnder index at
least `3` in the global quaternionic frame. On the Levi-Civita cover, closed
orbits are exactly the lifts of contractible orbits of the regularized
quotient, so this is dynamical convexity of that quotient. -/
def IsDynamicallyConvexOn (F : Phase → ℝ) (S : Set Phase) : Prop :=
  ∀ (x : ℝ → Phase) (T : ℝ), IsPeriodicHamiltonianSolutionIn F S x T →
    HasTransverseWindingAboveOne F x T

end

end BirkhoffGlobalSection


