-- Prove2me | Definitions.Def_FracTruthSched_disutility
-- name    : FracTruthSched_disutility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:50.190023+00:00
-- url     : https://prove2.me/theorems/cb03d642-c028-42e3-a1dd-66f4a6e5be7f
-- title:
--   Disutility $V_i(a;t_{-i})$ of a machine (Definition 1)
-- statement:
--   Fix a machine $i$ and the values $t_{-i}$ of the other machines. The **disutility** of machine $i$ at own values $a$ is
--   $$V_i(a;t_{-i})=a\cdot x_i(a,t_{-i})-P_i(a,t_{-i})+P_i(0,t_{-i}),$$
--   its processing cost minus its payment, normalized so that $V_i(0;t_{-i})=0$. It is the decrease in truthful utility when the type changes from $0$ to $a$. In a truthful mechanism it satisfies the incentive inequalities $x(b)\cdot(b-a)\le V(b)-V(a)\le x(a)\cdot(b-a)$.
--
--   **Formalization Note.** The function takes the whole input $t$ (own row $t_i=a$ and the opposing rows) and machine $i$; $(0,t_{-i})$ is $t$ with row $i$ set to $0$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Definition 1, p.5

import Mathlib
import Definitions.Def_FracTruthSched_FracMech

set_option autoImplicit false

namespace FracTruthSched

/-- The **disutility** of machine `i` (Anastasiadis et al., arXiv:2611.06642v1, Definition 1, p.5):
with own values `a = t_i` and opposing values `t_{-i}`,
`V_i(a; t_{-i}) = a · x_i(a, t_{-i}) − P_i(a, t_{-i}) + P_i(0, t_{-i})`.

**Formalization Note.** The input `t` carries both the own row `t i = a` and the opposing rows;
`Function.update t i 0` is `(0, t_{-i})`, so `disutility M (Function.update t i 0) i = 0`, the
paper's normalization `V_i(0; t_{-i}) = 0`. The restricted disutilities of §2.3 (slices, eq. (6))
are differences of this function. -/
def disutility {n : ℕ} {τ : Type*} [Fintype τ] (M : FracMech n τ) (t : Fin n → τ → ℝ)
    (i : Fin n) : ℝ :=
  ∑ j, t i j * M.x t i j - M.P t i + M.P (Function.update t i 0) i

end FracTruthSched


