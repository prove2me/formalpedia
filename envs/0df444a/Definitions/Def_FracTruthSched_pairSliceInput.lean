-- Prove2me | Definitions.Def_FracTruthSched_pairSliceInput
-- name    : FracTruthSched_pairSliceInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:09.467318+00:00
-- url     : https://prove2.me/theorems/5cc45fb6-607b-41fa-b195-c8317e3cdbf7
-- title:
--   Input of the $(e,f)$-slice with own values $t$ and opposing values $s$
-- statement:
--   Given a base graph input $z$, two parallel edges $e,f$ with endpoints $i,j$, own values $t=(t_1,t_2)$ of machine $i$ and values $s=(s_1,s_2)$ of machine $j$ on $e,f$, this is the input that agrees with $z$ everywhere except $t_{ie}=t_1$, $t_{if}=t_2$, $t_{je}=s_1$, $t_{jf}=s_2$. All values on the other tasks are fixed at those of $z$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 2, p.11

import Mathlib
import Definitions.Def_FracTruthSched_CoreTask

set_option autoImplicit false

namespace FracTruthSched

/-- The input of the **`(e, f)`-slice** of Lemma 2 (Anastasiadis et al., arXiv:2611.06642v1, Lemma 2,
p.11: "Choose two tasks e, f with the same endpoints i, j, and fix all values on the other tasks.
Write t = (t1, t2) for machine i's values on e and f, and s = (s1, s2) for machine j's values on
them"): the base input `z` with `t_ie = t.1`, `t_if = t.2`, `t_je = s.1`, `t_jf = s.2`.

**Formalization Note.** `t` and `s` are pairs in `ℝ × ℝ`. All other values are those of `z`. -/
def pairSliceInput {n ℓ : ℕ} (z : Fin n → CoreTask n ℓ → ℝ) (i j : Fin n) (e f : CoreTask n ℓ)
    (t s : ℝ × ℝ) : Fin n → CoreTask n ℓ → ℝ :=
  fun u g =>
    if u = i ∧ g = e then t.1 else if u = i ∧ g = f then t.2
    else if u = j ∧ g = e then s.1 else if u = j ∧ g = f then s.2 else z u g

end FracTruthSched


