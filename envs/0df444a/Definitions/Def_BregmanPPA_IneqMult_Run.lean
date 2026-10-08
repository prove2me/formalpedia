-- Prove2me | Definitions.Def_BregmanPPA_IneqMult_Run
-- name    : BregmanPPA_IneqMult_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:36.610373+00:00
-- url     : https://prove2.me/theorems/e8dbf8e6-e2e5-4264-a4f6-e2761d968504
-- title:
--   Recursion (11) — nonquadratic inequality multiplier run
-- statement:
--   Given a convex inequality program, a Bregman function $h$ with zone $S$, and step sizes $c_k$, a sequence $(x^k,p^k)$ **conforms to recursion (11)** when $p^k\in S$ and $x^{k+1}\in C$ minimizes the stated primal objective over $C$, followed by the multiplier update:
--
--   $$\begin{aligned}x^{k+1}&\in\operatorname*{argmin}_{y\in C}\Big\{f(y)+c_k^{-1}h^{*+}(\nabla h(p^k)+c_kg(y))\Big\},\\ p^{k+1}&=\nabla h^{*+}(\nabla h(p^k)+c_kg(x^{k+1})).\end{aligned}$$
--
--   The predicate records minimality rather than choosing an optimizer. Theorem 7 concerns any infinite run satisfying it.
--
--   **Formalization Note** Every $p^k$ lies in $S$, where $\nabla h$ is defined. The value $x^0$ is unused. The real form of $h^{*+}$ is valid under Lemma 3's finiteness conclusion.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 216, Theorem 7, recursion (11), https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology

namespace BregmanPPA.IneqMult

/-- Equation (11): the primal point minimizes the displayed objective on `C`, and the next
multiplier is the gradient of the finite-valued monotone conjugate. -/
def IsIneqMultiplierRun {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m) : Prop :=
  ∀ k, p k ∈ S ∧ x (k + 1) ∈ C ∧
    (∀ y ∈ C,
      f (x (k + 1)) + (((c k)⁻¹ * (monoConj h
        (gradient h (p k) + c k • gvec g (x (k + 1)))).toReal : ℝ) : EReal) ≤
      f y + (((c k)⁻¹ * (monoConj h
        (gradient h (p k) + c k • gvec g y)).toReal : ℝ) : EReal)) ∧
    p (k + 1) = gradient (fun z => (monoConj h z).toReal)
      (gradient h (p k) + c k • gvec g (x (k + 1)))

end BregmanPPA.IneqMult


