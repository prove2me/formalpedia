-- Prove2me | Definitions.Def_AubinLipschitz_paramMap
-- name    : AubinLipschitz_paramMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:29.196784+00:00
-- url     : https://prove2.me/theorems/ecad27e3-0b09-424b-ae3e-3cbc796c3b99
-- title:
--   §5, (9)–(10) — the map $F$ from solutions to parameters
-- statement:
--   Let $G$ be a set-valued map from $X$ to $X^*$ and $H^{-1}$ a set-valued map from $Y^*$ to $Y$. The map $F$ from $X\times Y^*$ to $X^*\times Y\times L(X,Y)$ is defined by: $(p,y,A)\in F(x,q)$ if and only if
--
--   1. $p\in G(x)+A^*q$;
--   2. $y\in -Ax+H^{-1}(q)$.
--
--   The paper takes $G=\partial U$ and $H^{-1}=\partial V^*$. A point of $X\times Y^*$ is a candidate solution–multiplier pair, and $F$ returns the parameters for which it solves the system.
--
--   **Formalization Note** The transpose $A^*q$ is the composition $q\circ A$.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (9)–(10), p.33

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (9)–(10), p.33: the map `F : X × Y* ⇉ X* × Y × L(X, Y)` given by
`(p, y, A) ∈ F(x, q)` iff `p ∈ G(x) + A*q` and `y ∈ −A x + H⁻¹(q)`.

**Formalization Note** `G : X ⇉ X*` and `Hinv = H⁻¹ : Y* ⇉ Y` are parameters here; the paper's
are `G = ∂U` and `H⁻¹ = ∂V*` (`solMap`). `A* q` is `q.comp A`. -/
def paramMap {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (G : X → Set (StrongDual ℝ X)) (Hinv : StrongDual ℝ Y → Set Y) :
    X × StrongDual ℝ Y → Set (StrongDual ℝ X × Y × (X →L[ℝ] Y)) :=
  fun z => {w | (∃ g ∈ G z.1, w.1 = g + z.2.comp w.2.2) ∧
    ∃ h ∈ Hinv z.2, w.2.1 = -(w.2.2 z.1) + h}

end AubinLipschitz


