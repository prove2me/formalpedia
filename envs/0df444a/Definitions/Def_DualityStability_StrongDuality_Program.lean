-- Prove2me | Definitions.Def_DualityStability_StrongDuality_Program
-- name    : DualityStability_StrongDuality_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:50.861497+00:00
-- url     : https://prove2.me/theorems/0e1126ae-2581-47a2-91a9-6fd18f7d9812
-- title:
--   Convex dual program and perturbation function (§§2–4)
-- statement:
--   Let $(E,E')$ and $(F,F')$ be topologically paired real locally convex Hausdorff spaces. Let $A:E\to F$ and $A^*:F'\to E'$ be continuous linear maps satisfying $\langle Ax,y'\rangle_F=\langle x,A^*y'\rangle_E$. Let $f:E\to[-\infty,+\infty]$ be lower semicontinuous, proper and convex, and $g:F\to[-\infty,+\infty]$ be upper semicontinuous, proper and concave. Proper means that $f$ never equals $-\infty$ and is finite somewhere, while $g$ never equals $+\infty$ and is finite somewhere. Convexity is defined by the convexity of the real epigraph; concavity means convexity of $-g$.
--
--   The conjugates, primal and dual objectives, and perturbed value function are
--   $$
--   f^*(x')=\sup_{x\in E}\bigl(\langle x,x'\rangle_E-f(x)\bigr),\qquad
--   g^*(y')=\inf_{y\in F}\bigl(\langle y,y'\rangle_F-g(y)\bigr),
--   $$
--   $$
--   P_z(x)=f(x)-g(Ax-z),\quad h(z)=\inf_{x\in E}P_z(x),\quad
--   P^*(y')=g^*(y')-f^*(A^*y').
--   $$
--
--   The dual's minimization form $(P')$ has objective $-g^*(y')+f^*(A^*y')$ and perturbation function $h'(z')=\inf_{y'\in F'}\{-g^*(y')+f^*(A^*y'-z')\}$ for $z'\in E'$. The definition also supplies the subdifferential $\partial h(0)$, the one-sided directional derivative of $h$ at zero, and the paper's definitions of unstable and stable setting. Stability requires $h(0)<+\infty$ and excludes arbitrarily negative directional derivatives near zero; instability is tested only when $h(0)$ is finite.
--
--   These objects are the common setting of every result in this mission. The infima and suprema use extended real values, so $h(0)=-\infty$ is retained as a legitimate stable case.
--
--   **Formalization Note** The paired-space requirements are carried by `TopPairing`. The conjugates are defined by the displayed formulas; their further regularity follows from the standing hypotheses rather than being assumed. The derivative is encoded as the lower limit of positive difference quotients, which equals the one-sided limit for convex $h$.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), pp. 170–175, (2.2)–(2.5), §3, (4.3)

import Definitions.Def_DualityStability_StrongDuality_TopPairing

namespace DualityStability.StrongDuality

/-- Convexity of the real epigraph of an extended-real function (§2, p. 170).
This formulation also applies when the function takes the value `-∞`. -/
def EpiConvex {X : Type*} [AddCommGroup X] [Module ℝ X] (h : X → EReal) : Prop :=
  Convex ℝ {q : X × ℝ | h q.1 ≤ (q.2 : EReal)}

/-- The subdifferential (2.3) in a topologically paired space. -/
def subdiff {X X' : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
    [TopologicalSpace X'] [AddCommGroup X'] [Module ℝ X']
    [IsTopologicalAddGroup X'] [ContinuousSMul ℝ X'] [LocallyConvexSpace ℝ X'] [T2Space X']
    (π : TopPairing X X') (hX : X → EReal) (x : X) : Set X' :=
  {x' | ∀ z : X, hX (x + z) ≥ hX x + (π.pair z x' : EReal)}

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- The standing setting of §3, pp. 171–173. `f` is proper, lower semicontinuous
and convex; `g` is proper, upper semicontinuous and concave. The adjoint is
given as continuous linear data with the paper's defining identity. -/
structure Program (E E' F F' : Type*)
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
    [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
    [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F'] where
  ePair : TopPairing E E'
  fPair : TopPairing F F'
  A : E →L[ℝ] F
  Astar : F' →L[ℝ] E'
  adjoint : ∀ (x : E) (y' : F'), fPair.pair (A x) y' = ePair.pair x (Astar y')
  f : E → EReal
  g : F → EReal
  f_convex : EpiConvex f
  f_lsc : LowerSemicontinuous f
  f_no_neg_inf : ∀ x : E, f x ≠ ⊥
  f_some_finite : ∃ x : E, f x ≠ ⊤
  g_concave : EpiConvex (fun y : F => -g y)
  g_usc : LowerSemicontinuous (fun y : F => -g y)
  g_no_pos_inf : ∀ y : F, g y ≠ ⊤
  g_some_finite : ∃ y : F, g y ≠ ⊥

namespace Program

variable (p : Program E E' F F')

/-- The convex conjugate `f*` of (2.2), with the given pairing. -/
noncomputable def fstar (x' : E') : EReal :=
  ⨆ x : E, (p.ePair.pair x x' : EReal) - p.f x

/-- The concave conjugate `g*` of (2.5), with the given pairing. -/
noncomputable def gstar (y' : F') : EReal :=
  ⨅ y : F, (p.fPair.pair y y' : EReal) - p.g y

/-- The perturbed primal minimand of (P(z)), §4, p. 174. -/
noncomputable def primalAt (z : F) (x : E) : EReal := p.f x - p.g (p.A x - z)

/-- `h(z) = inf (P(z))`, §4, p. 174. -/
noncomputable def h (z : F) : EReal := ⨅ x : E, p.primalAt z x

/-- The maximand of (P*) on p. 172. -/
noncomputable def dualAt (y' : F') : EReal := p.gstar y' - p.fstar (p.Astar y')

/-- The supremum of (P*) on p. 173. -/
noncomputable def dualValue : EReal := ⨆ y' : F', p.dualAt y'

/-- The perturbation function of (P'), the minimization version of (P*) on p. 173.
Its perturbations lie in `E'`, as required by the dual reading of §4. -/
noncomputable def dualH (z' : E') : EReal :=
  ⨅ y' : F', (-p.gstar y') - (-p.fstar (p.Astar y' - z'))

end Program

/-- The right-hand directional derivative (4.3). Under convexity of `h` this
liminf is the actual limit. The real `r` is the finite value of `h(0)`. -/
noncomputable def rightDerivative {X : Type*} [TopologicalSpace X]
    [AddCommGroup X] [Module ℝ X] (hX : X → EReal) (r : ℝ) (z : X) : EReal :=
  Filter.liminf (fun ε : ℝ => ((ε⁻¹ : ℝ) : EReal) * (hX (ε • z) - (r : EReal)))
    (nhdsWithin 0 (Set.Ioi 0))

/-- "Unstably set" from (4.3), §4, p. 175. The definition applies only when
`h(0)` is finite and quantifies over every neighborhood and every magnitude. -/
def UnstablySet {X : Type*} [TopologicalSpace X] [AddCommGroup X]
    [Module ℝ X] (hX : X → EReal) : Prop :=
  ∃ r : ℝ, hX 0 = (r : EReal) ∧
    ∀ U ∈ nhds (0 : X), ∀ M : ℝ, ∃ z ∈ U,
      rightDerivative hX r z < ((-M : ℝ) : EReal)

/-- "Stably set" from §4, p. 175: consistency and absence of instability.
In particular `h(0) = -∞` is allowed. -/
def StablySet {X : Type*} [TopologicalSpace X] [AddCommGroup X]
    [Module ℝ X] (hX : X → EReal) : Prop :=
  hX 0 < ⊤ ∧ ¬ UnstablySet hX

end DualityStability.StrongDuality


