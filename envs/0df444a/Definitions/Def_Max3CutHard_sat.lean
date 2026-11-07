-- Prove2me | Definitions.Def_Max3CutHard_sat
-- name    : Max3CutHard_sat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:41.750952+00:00
-- url     : https://prove2.me/theorems/2a80d47e-65ed-49dd-bdda-fbdb02611c6d
-- title:
--   Satisfying tuples $\mathrm{sat}_t$ of type $t$
-- statement:
--   For $t\in\mathbb Z_3$,
--
--   $$\mathrm{sat}_t=\{x\in\mathbb Z_3^3:\ x_1+x_2+x_3=t\},$$
--
--   the set of satisfying tuples of type $t$. It is nonempty.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Gadgets, p.5

import Mathlib

namespace Max3CutHard

/-- **Satisfying tuples of type `t`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Gadgets, p.5: "Let
`sat_t = {x ∈ ℤ₃^3 : x1 + x2 + x3 = t}` be the set of satisfying tuples of type `t`".

**Formalization Note.** Tuples are `Fin 3 → ℤ₃`, 0-based. -/
def sat (t : ZMod 3) : Finset (Fin 3 → ZMod 3) :=
  Finset.univ.filter fun x => x 0 + x 1 + x 2 = t

theorem sat_nonempty (t : ZMod 3) : (sat t).Nonempty :=
  ⟨![t, 0, 0], by simp [sat]⟩

end Max3CutHard


