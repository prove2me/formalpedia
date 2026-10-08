-- Prove2me | Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
-- name    : MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:20.210652+00:00
-- url     : https://prove2.me/theorems/7fc00ce0-2993-4b1b-8499-56f9b0c698e4
-- title:
--   Quasisupermodularity on a lattice
-- statement:
--   Let $X$ be a lattice, $S\subseteq X$, and $g:X\to\mathbb R$. The function is **quasisupermodular on $S$** when, for every $x,y\in S$, both implications hold:
--
--   $$g(x\wedge y)\le g(x)\ \Longrightarrow\ g(y)\le g(x\vee y),\qquad
--   g(x\wedge y)<g(x)\ \Longrightarrow\ g(y)<g(x\vee y).$$
--
--   The first implication preserves weak preference and the second preserves strict preference as the other coordinate rises. The paper uses this property on the whole lattice $X$.
--
--   **Formalization Note** The predicate accepts a set argument for reuse; every theorem in this mission applies it with $S=X$. The meet and join are evaluated in $X$.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 162 (PDF 7), definition preceding Theorem 4

import Mathlib

namespace MonotoneCompStatics.Monotonicity

def QuasiSupermodularOn {X : Type*} [Lattice X] (g : X → ℝ) (S : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ S → ∀ ⦃y : X⦄, y ∈ S →
    (g (x ⊓ y) ≤ g x → g y ≤ g (x ⊔ y)) ∧ (g (x ⊓ y) < g x → g y < g (x ⊔ y))

end MonotoneCompStatics.Monotonicity


