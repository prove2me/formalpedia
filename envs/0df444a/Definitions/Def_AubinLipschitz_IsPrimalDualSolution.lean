-- Prove2me | Definitions.Def_AubinLipschitz_IsPrimalDualSolution
-- name    : AubinLipschitz_IsPrimalDualSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:33.295979+00:00
-- url     : https://prove2.me/theorems/f0c8bdef-90d4-42a6-8e87-76a5422519f0
-- title:
--   §5, (3) — solutions of the primal–dual optimization problem
-- statement:
--   A pair $(x_0,q_0)\in X\times Y^*$ **solves problem (3)** if
--
--   1. $U(x_0)+V(A_0x_0+y_0)-\langle p_0,x_0\rangle=\min_{x\in X}\big(U(x)+V(A_0x+y_0)-\langle p_0,x\rangle\big)$;
--   2. $U^*(-A_0^*q_0+p_0)+V^*(q_0)-\langle q_0,y_0\rangle=\min_{q\in Y^*}\big(U^*(-A_0^*q+p_0)+V^*(q)-\langle q,y_0\rangle\big)$;
--   3. $U(x_0)+U^*(-A_0^*q_0+p_0)+V(A_0x_0+y_0)+V^*(q_0)=\langle p_0,x_0\rangle+\langle q_0,y_0\rangle$.
--
--   So $x_0$ is primal optimal, $q_0$ is a Lagrange multiplier (dual optimal), and there is no duality gap.
--
--   **Formalization Note** "$=\min$" is stated as "at most the value at every competitor". The third clause forces all four terms on its left to be finite.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (3), p.31

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
open RockafellarMaxMono.Shared

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (3), p.31: `(x₀, q₀) ∈ X × Y*` solves the optimization problem:
(i) `x₀` minimizes `U(x) + V(A₀x + y₀) − ⟨p₀, x⟩` over `X`;
(ii) `q₀` minimizes `U*(−A₀*q + p₀) + V*(q) − ⟨q, y₀⟩` over `Y*`;
(iii) `U(x₀) + U*(−A₀*q₀ + p₀) + V(A₀x₀ + y₀) + V*(q₀) = ⟨p₀, x₀⟩ + ⟨q₀, y₀⟩`.

**Formalization Note** "`= min`" is written as "`≤` every competitor". For proper `U`, `V` none
of the terms is `⊥`, so the `EReal` sums carry no `⊥ + ⊤` artefact, and (iii) forces all terms
to be finite. -/
def IsPrimalDualSolution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : X → EReal) (V : Y → EReal) (A₀ : X →L[ℝ] Y)
    (p₀ : StrongDual ℝ X) (y₀ : Y) (x₀ : X) (q₀ : StrongDual ℝ Y) : Prop :=
  (∀ x : X, U x₀ + V (A₀ x₀ + y₀) - ((p₀ x₀ : ℝ) : EReal) ≤
      U x + V (A₀ x + y₀) - ((p₀ x : ℝ) : EReal)) ∧
  (∀ q : StrongDual ℝ Y,
      conj U (-(q₀.comp A₀) + p₀) + conj V q₀ - ((q₀ y₀ : ℝ) : EReal) ≤
        conj U (-(q.comp A₀) + p₀) + conj V q - ((q y₀ : ℝ) : EReal)) ∧
  U x₀ + conj U (-(q₀.comp A₀) + p₀) + V (A₀ x₀ + y₀) + conj V q₀ =
    ((p₀ x₀ : ℝ) : EReal) + ((q₀ y₀ : ℝ) : EReal)

end AubinLipschitz


