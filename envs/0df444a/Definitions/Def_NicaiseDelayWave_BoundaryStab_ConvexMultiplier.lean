-- Prove2me | Definitions.Def_NicaiseDelayWave_BoundaryStab_ConvexMultiplier
-- name    : NicaiseDelayWave_BoundaryStab_ConvexMultiplier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T17:22:38.33084+00:00
-- url     : https://prove2.me/theorems/3c2757b5-d11d-46ca-84dd-79fd80a4a46d
-- title:
--   Geometric hypothesis (1.6)–(1.7): a strictly convex C² multiplier v with ∇v·ν ≤ 0 on Γ_D
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain with outer unit normal $\nu$. A function $v : \mathbb R^n \to \mathbb R$ and a number $\alpha$ satisfy the **geometric hypothesis** if
--
--   1. $v$ is of class $C^2$;
--   2. $\alpha > 0$ and $v$ is uniformly strictly convex on $\overline\Omega$:
--   $$\langle D^2 v(x)\,\xi, \xi\rangle \ \ge\ 2\alpha\,|\xi|^2 \qquad \forall x \in \overline\Omega,\ \forall \xi \in \mathbb R^n, \tag{1.6}$$
--   where $D^2 v$ is the Hessian of $v$;
--   3. the vector field $H := \nabla v$ points weakly inward on the Dirichlet part:
--   $$H(x)\cdot\nu(x) \le 0 \qquad \forall x \in \Gamma_D. \tag{1.7}$$
--
--   This is the hypothesis under which the Carleman estimates of Lasiecka, Triggiani and Yao yield boundary observability for the wave equation; in Nicaise–Pignotti it is assumed throughout, and it enters the observability inequality (Proposition 3.2) and hence the exponential stability theorem.
--
--   **Formalization Note** The paper takes $v \in C^2(\overline\Omega)$; here $v$ is $C^2$ on all of $\mathbb R^n$, which loses nothing because a $C^2(\overline\Omega)$ function on a $C^2$ domain extends to a $C^2$ function on $\mathbb R^n$. The Hessian quadratic form is the second Fréchet derivative applied to $(\xi, \xi)$.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1562, (1.6)–(1.7)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain

namespace NicaiseDelayWave.BoundaryStab

/-- The geometric hypothesis (1.6)–(1.7) of Nicaise–Pignotti (p. 1562): `v` is `C²`, strictly
convex on `closure Ω` with `⟨D²v(x)ξ, ξ⟩ ≥ 2α|ξ|²` for some `α > 0`, and `H := ∇v` satisfies
`H(x) · ν(x) ≤ 0` on `Γ_D`. -/
structure ConvexMultiplier {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 v
  pos : 0 < α
  /-- (1.6) -/
  hessian : ∀ x ∈ closure D.Ω, ∀ ξ : EuclideanSpace ℝ (Fin n),
    2 * α * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ v) x ξ ξ
  /-- (1.7) -/
  normal : ∀ x ∈ D.ΓD, inner ℝ (gradient v x) (D.ν x) ≤ 0

end NicaiseDelayWave.BoundaryStab


