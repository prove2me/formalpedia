-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_lin2OPT
-- name    : HeilmanMax3Cut_Supplement_lin2OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:05:49.24933+00:00
-- url     : https://prove2.me/theorems/4018286b-b0b6-49ba-8afc-ac69f1e444e1
-- title:
--   The optimum $\mathrm{OPT}(I)$ of a MAX-2-LIN(3) instance
-- statement:
--   For an instance $I$ with $m\ge1$ equations in $n$ variables,
--
--   $$\mathrm{OPT}(I)=\max_{x\in(\mathbb Z/3)^n}\frac{\#\{\text{equations of }I\text{ satisfied by }x\}}{m}.$$
--
--   It is the quantity whose gap Theorem 1.5 proves hard to decide.
--
--   **Formalization Note** For the empty list the value is $0$; the theorem excludes the empty list.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.5, p.4

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Supplement_Lin2Inst

namespace HeilmanMax3Cut.Supplement

/-- **The optimum `OPT(I)` of a MAX-2-LIN(3) instance.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.5, p.4: `OPT(I)` is the
largest fraction of the equations of `I` that an assignment `x ∈ (ℤ/3)ⁿ` satisfies, i.e.
`max_x |{e ∈ I : x_i − x_j = c}| / m` for `m` equations.

**Formalization Note.** The maximum is a real `⨆` over the finitely many assignments
`x : Fin n → ZMod 3` (a nonempty finite family, so it is attained). For the empty list the value is
`0` (`0/0 = 0` in Lean); the hardness statements exclude the empty list. -/
noncomputable def lin2OPT (I : Lin2Inst) : ℝ :=
  ⨆ x : Fin I.n → ZMod 3,
    ((I.eqs.countP fun e => decide (x e.i - x e.j = e.c) : ℕ) : ℝ) / (I.eqs.length : ℝ)

end HeilmanMax3Cut.Supplement


