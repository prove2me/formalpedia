-- Prove2me | Definitions.Def_GarberOLO_Alg3_alg2Iter
-- name    : GarberOLO_Alg3_alg2Iter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:54:20.657984+00:00
-- url     : https://prove2.me/theorems/af9d46a1-3252-4ae9-a850-6613b19871c0
-- title:
--   Iterates $\tilde y_i$ of Algorithm 2
-- statement:
--   Algorithm 2 (infeasible projection onto $\mathrm{CH}(\alpha K)$) receives $y \in \mathbb R^d$ and $\varepsilon > 0$ and sets
--   $$\tilde y_1 = \frac{y}{\max\{1, \|y\|/(\alpha R)\}}.$$
--   At pass $i$ it runs the Separation-or-Decomposition procedure at $\tilde y_i$ with $N = N(\tilde y_i)$; if the procedure returns a separating vector $w$, then $\tilde y_{i+1} = \tilde y_i - \varepsilon w$, otherwise the algorithm returns $\tilde y_i$ (and the sequence stays there).
--
--   $\mathrm{alg2Iter}(i)$ is $\tilde y_{i+1}$ (passes counted from $0$).
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Algorithm 2, p. 12

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_sepOrDec
import Definitions.Def_GarberOLO_Alg3_Nprescribed

namespace GarberOLO.Alg3

/-- **The iterates ỹ of Algorithm 2** ((infeasible) projection onto CH(αK)).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Algorithm 2, p. 12: "1: input: point y ∈ ℝᵈ, tolerance ε > 0 2: ỹ ← y/max{1, ‖y‖/(αR)} 3: for t = 1 . . . do 4: call the Separation-or-Decompostion procedure described in Lemma 5 with parameters (ỹ, ε) 5: if the procedure outputs a separating hyperplane w then 6: ỹ ← ỹ − εw 7: else 8: let (a₁, …, a_N), {(v₁, s₁), …, (v_N, s_N)} be the decomposition returned, where N is as prescribed in Lemma 5. 9: return ỹ, (a₁, …, a_N), {(v₁, s₁), …, (v_N, s_N)}".

`alg2Iter S OK c ε y i` is the value of ỹ at the start of the `(i+1)`-st pass through the loop
(the paper's ỹ_{i+1} in the proof of Lemma 7): `alg2Iter … 0 = y / max{1, ‖y‖/(αR)}`, and if the
procedure `sepOrDec` run at `ỹ := alg2Iter … i` with `N = Nprescribed S c ε ỹ` returns a
separating vector `w`, then `alg2Iter … (i+1) = ỹ − ε w`; otherwise (the algorithm has returned)
the sequence stays at `ỹ`.

**Formalization Note.** (Reading 2.) N is recomputed at the current ỹ of every pass. The division
`y / max{1, ‖y‖/(αR)}` is the scalar multiple by `(max 1 (‖y‖/(αR)))⁻¹`. -/
noncomputable def alg2Iter {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (c ε : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => (max 1 (‖y‖ / (S.α * S.R)))⁻¹ • y
  | i + 1 =>
    let yi := alg2Iter S OK c ε y i
    let out := sepOrDec S OK yi ε (Nprescribed S c ε yi)
    if out.isSep then yi - ε • out.w else yi

end GarberOLO.Alg3


