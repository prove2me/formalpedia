-- Prove2me | Definitions.Def_FenchelRobust_Counterpart_ConvexDuality
-- name    : FenchelRobust_Counterpart_ConvexDuality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:45:18.87939+00:00
-- url     : https://prove2.me/theorems/4bcb0059-52d9-4bb7-93d4-87053e8cf0dd
-- title:
--   Support functions and restricted Fenchel conjugates
-- statement:
--   For a set $S\subseteq\mathbb R^k$, its **support function** at $y\in\mathbb R^k$ is
--   $$\delta^*(y\mid S)=\sup_{a\in S}y^Ta.$$
--   For a convex function $F$ finite on its effective domain $C$ and a concave function $G$ finite on its effective domain $D$, their restricted conjugates are
--   $$F^*(y)=\sup_{a\in C}(y^Ta-F(a)),\qquad G_*(y)=\inf_{a\in D}(a^Ty-G(a)).$$
--
--   These general convex-analysis objects supply the paper's support function and partial concave conjugate. All extrema take values in the extended real line, including empty or unbounded cases.
-- source:
--   Ben-Tal, den Hertog, Vial, Deriving robust counterparts of nonlinear uncertain inequalities, CentER Discussion Paper 2012-053 (July 2, 2012), pp. 2–3, Notation and Eqs. (1), (3)

import Mathlib

namespace FenchelRobust.Counterpart

/-- The support function of a subset of a finite-dimensional real vector space, (3). -/
noncomputable def supportFun {k : ℕ} (S : Set (Fin k → ℝ)) (y : Fin k → ℝ) : EReal :=
  ⨆ a ∈ S, ((y ⬝ᵥ a : ℝ) : EReal)

/-- The convex conjugate of a real function restricted to its effective domain. -/
noncomputable def convexConj {k : ℕ} (C : Set (Fin k → ℝ))
    (F : (Fin k → ℝ) → ℝ) (y : Fin k → ℝ) : EReal :=
  ⨆ a ∈ C, ((y ⬝ᵥ a - F a : ℝ) : EReal)

/-- The lower (concave) conjugate of a real function on its effective domain, (1). -/
noncomputable def concaveConj {k : ℕ} (D : Set (Fin k → ℝ))
    (G : (Fin k → ℝ) → ℝ) (y : Fin k → ℝ) : EReal :=
  ⨅ a ∈ D, ((a ⬝ᵥ y - G a : ℝ) : EReal)

end FenchelRobust.Counterpart


