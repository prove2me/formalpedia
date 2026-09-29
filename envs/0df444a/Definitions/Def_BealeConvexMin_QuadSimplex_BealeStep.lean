-- Prove2me | Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep
-- name    : BealeConvexMin_QuadSimplex_BealeStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:31:56.54103+00:00
-- url     : https://prove2.me/theorems/24e2fbe7-42a6-4411-975d-d6b63cc17215
-- title:
--   Beale (1955), §§2–3: one step of the simplex method for a quadratic objective
-- statement:
--   One step of Beale's iteration (§2, pp. 174–175, specialised to a quadratic $C$ as in §3) passes from a tableau $T$ to a tableau $T'$ as follows.
--
--   1. **Choice of $z_p$.** A nonbasic variable can *profitably be altered* if it is free with $c_{p0}\neq0$, or restricted with $c_{p0}<0$. The step picks such a $z_p$, and it must pick a free one whenever a free one is profitable: "We see if $C$ can be reduced by making a (small) change in some nonbasic free variable, or failing that by increasing some nonbasic restricted variable". No further pricing rule is fixed.
--   2. **Orientation.** "If it is a free variable to be decreased we change its sign throughout": when $c_{p0}>0$ the variable in slot $p$ is replaced by its negative (row and column $p$ of $(c_{kl})$ and entry $p$ of every row change sign). Afterwards $c_{p0}<0$ and $z_p$ is to be increased.
--   3. **Ratio test.** With the other nonbasic variables at zero, $x_h$ stays nonnegative as long as
--   $$z_p\le\frac{a_{q0}}{-a_{qp}}=\min_{a_{hp}<0}\frac{a_{h0}}{-a_{hp}}=Z_p .\tag{2.4}$$
--   4. **Stationary point.** Along the ray, $C=c_{00}+2c_{p0}z_p+c_{pp}z_p^2$; when $c_{pp}>0$ it stops decreasing at $t^*=-c_{p0}/c_{pp}$, where the free variable $u_r=c_{p0}+\sum_{l}c_{pl}z_l$ of (3.2) vanishes.
--   5. **A restricted variable enters** when $Z_p$ is defined, attained at $x_q$, and $C$ decreases all the time as $z_p$ increases from $0$ to $Z_p$ ($c_{pp}\le0$ or $Z_p\le t^*$): $x_q$ becomes nonbasic in slot $p$, and the pivot uses the row of $x_q$ as (3.3).
--   6. **A free variable enters** when $c_{pp}>0$ and $t^*\le a_{h0}/(-a_{hp})$ for every $h$ with $a_{hp}<0$ (in particular when $Z_p$ is undefined): $u_r$ becomes nonbasic in slot $p$, and the pivot uses $(c_{p0},c_{p1},\dots,c_{pN})$ as (3.3).
--   7. If $Z_p$ is undefined and $c_{pp}\le0$, $C$ decreases indefinitely and there is no step.
--
--   In cases 5 and 6, $(c_{kl})$ is replaced by $(c''_{kl})$ of (3.5)–(3.6), every row of (2.3) is transformed by the same substitution, and slot $p$ receives its new label.
--
--   **Formalization Note** The step is a relation, not a function: it is nondeterministic in the choice of $z_p$, in the choice of $x_q$ at a tie in (2.4), and in the branch when $Z_p=t^*$. The paper removes such ties with Charnes's $\varepsilon$-perturbations ("the $\varepsilon$-perturbations ensure both that $x_q$ is defined uniquely, and that $x_q$ and $u_r$ do not vanish simultaneously"); here every resolution is allowed, and the positivity hypothesis on the run excludes the degenerate outcomes. The ratio test ranges over all rows; nonbasic rows are unit vectors and never have a negative entry in slot $p$.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, pp. 174–175 (PDF pp. 2–3), §2, 'A general step of this iteration', eq. (2.4); p. 175 (PDF p. 3), §3, eq. (3.2) and the paragraph before it; pp. 175–176, eqs. (3.3)–(3.6)

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau

namespace BealeConvexMin.QuadSimplex

/-!
Beale (1955), §2, pp. 174–175 ("A general step of this iteration"), specialised to a quadratic `C`
as in §3, pp. 175–176. Nonbasic slot `p : Fin N` is matrix index `p.succ`; slot `0` is `z_0 = 1`.
-/

variable {n N : ℕ}

/-- "If it is a free variable to be decreased we change its sign throughout" (p. 174): replace the
variable in slot `p.succ` by its negative. Row and column `p.succ` of `c` change sign (so `c_pp`
is unchanged), and so does entry `p.succ` of every row. -/
def negateSlot (T : Tableau n N) (p : Fin N) : Tableau n N where
  lab := T.lab
  row := fun j l => if l = p.succ then -T.row j l else T.row j l
  c := Matrix.of fun k l =>
    (if k = p.succ then (-1 : ℝ) else 1) * (if l = p.succ then (-1 : ℝ) else 1) * T.c k l

/-- The tableau after the pivot at slot `p.succ` whose new nonbasic variable has coefficients `d`
(eq. (3.3)) and label `newLab`: `c` becomes `pivotC` (eqs. (3.5)–(3.6)), every row is transformed
by the same substitution (p. 176, "in the same way"), and the slot receives the new label. -/
noncomputable def pivotTableau (T : Tableau n N) (p : Fin N) (d : Fin (N + 1) → ℝ)
    (newLab : Option (Fin n)) : Tableau n N where
  lab := Function.update T.lab p newLab
  row := fun j => pivotRow (T.row j) p.succ d
  c := pivotC T.c p.succ d

/-- The variable in slot `p.succ` can profitably be altered (p. 175): a free `z_p` with
`c_p0 ≠ 0`, or a restricted `z_p` with `c_p0 < 0`. -/
def IsProfitable (T : Tableau n N) (p : Fin N) : Prop :=
  (T.lab p = none ∧ T.c p.succ 0 ≠ 0) ∨ (T.lab p ≠ none ∧ T.c p.succ 0 < 0)

/-- The choice of `z_p` (p. 174): "We see if `C` can be reduced by making a (small) change in some
nonbasic free variable, or failing that by increasing some nonbasic restricted variable". The slot
is profitable, and it is free whenever some free slot is profitable. -/
def AdmissibleChoice (T : Tableau n N) (p : Fin N) : Prop :=
  IsProfitable T p ∧ ((∃ k : Fin N, T.lab k = none ∧ T.c k.succ 0 ≠ 0) → T.lab p = none)

/-- Orientation: after the choice, `z_p` is to be increased. A free `z_p` with `c_p0 > 0` is
negated. (A profitable restricted `z_p` has `c_p0 < 0` and is left as it is.) -/
noncomputable def orient (T : Tableau n N) (p : Fin N) : Tableau n N :=
  if 0 < T.c p.succ 0 then negateSlot T p else T

/-- The ratio `a_h0 / (-a_hp)` of eq. (2.4) for row `h`. -/
noncomputable def ratio (T : Tableau n N) (p : Fin N) (h : Fin n) : ℝ :=
  T.row h 0 / (-T.row h p.succ)

/-- `x_q` attains the minimum in eq. (2.4): `a_qp < 0` and
`a_q0/(-a_qp) = min_{a_hp < 0} a_h0/(-a_hp) = Z_p`. -/
def IsRatioMin (T : Tableau n N) (p : Fin N) (q : Fin n) : Prop :=
  T.row q p.succ < 0 ∧ ∀ h : Fin n, T.row h p.succ < 0 → ratio T p q ≤ ratio T p h

/-- One step of Beale's iteration for a quadratic `C` (§2, pp. 174–175; §3, eqs. (3.2)–(3.6)).
After choosing `p` (`AdmissibleChoice`) and orienting (`U = orient T p`), along the ray
`z_p = t ≥ 0`, other nonbasic variables zero, `C = c_00 + 2 c_p0 t + c_pp t²`; if `c_pp > 0` it
stops decreasing at `t* = -c_p0/c_pp`, where `u_r = c_p0 + Σ_l c_pl z_l` of (3.2) vanishes.
* Restricted variable enters: `Z_p` is defined (attained at `x_q`) and `C` decreases all the time as
  `z_p` increases from `0` to `Z_p` (`c_pp ≤ 0` or `Z_p ≤ t*`); then `x_q` becomes nonbasic in place
  of `z_p`, with (3.3) the row of `x_q`.
* Free variable enters: `c_pp > 0` and `t* ≤ a_h0/(-a_hp)` for every `h` with `a_hp < 0` (in
  particular when `Z_p` is undefined); then the free variable `u_r` of (3.2) becomes nonbasic in
  place of `z_p`, with (3.3) the row `(c_p0, c_p1, …, c_pN)` of `c`.
If `Z_p` is undefined and `c_pp ≤ 0`, `C` decreases indefinitely and there is no step. At a tie
`Z_p = t*` both branches are allowed. -/
def BealeStep (T T' : Tableau n N) : Prop :=
  ∃ p : Fin N, AdmissibleChoice T p ∧
    ((∃ q : Fin n, IsRatioMin (orient T p) p q ∧
        ((orient T p).c p.succ p.succ ≤ 0 ∨
          ratio (orient T p) p q ≤ -(orient T p).c p.succ 0 / (orient T p).c p.succ p.succ) ∧
        T' = pivotTableau (orient T p) p ((orient T p).row q) (some q)) ∨
     (0 < (orient T p).c p.succ p.succ ∧
        (∀ h : Fin n, (orient T p).row h p.succ < 0 →
          -(orient T p).c p.succ 0 / (orient T p).c p.succ p.succ ≤ ratio (orient T p) p h) ∧
        T' = pivotTableau (orient T p) p ((orient T p).c p.succ) none))

end BealeConvexMin.QuadSimplex


