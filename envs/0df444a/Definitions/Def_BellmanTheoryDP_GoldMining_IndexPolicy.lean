-- Prove2me | Definitions.Def_BellmanTheoryDP_GoldMining_IndexPolicy
-- name    : BellmanTheoryDP_GoldMining_IndexPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:34:04.192463+00:00
-- url     : https://prove2.me/theorems/f5fa8055-96c1-4d8b-9d48-4b6f05ddddc9
-- title:
--   The index rule of Bellman's (8.3) (corrected) and the choice sequence it generates
-- statement:
--   In Bellman's gold-mining problem (mines $A$ and $B$ with success probabilities $p, q$ and mined fractions $r, s$), the **index rule** at current amounts $(x, y)$ compares the index of Anaconda, $\dfrac{p r x}{1-p}$, with the index of Bonanza, $\dfrac{q s y}{1-q}$, and chooses
--   $$\text{A} \quad\text{if}\quad \frac{p r x}{1-p} \ge \frac{q s y}{1-q}, \qquad \text{B otherwise.}$$
--   Each index is the immediate expected gain of a use divided by its immediate expected loss (the probability of destroying the machine). Ties are broken towards $A$.
--
--   Applying the rule to the current amounts at every use, starting from $(x_0, y_0) = (x, y)$, gives the states
--   $$(x_{n+1}, y_{n+1}) = \begin{cases} ((1-r)x_n,\ y_n) & \text{if the rule chooses } A \text{ at } (x_n, y_n),\\ (x_n,\ (1-s)y_n) & \text{if it chooses } B,\end{cases}$$
--   and the **index policy** is the choice sequence $\sigma^*_n$ = the rule's choice at $(x_n, y_n)$. Because the only observation is survival, this feedback rule is the same thing as this fixed choice sequence.
--
--   This is the policy described by Bellman's (8.3) with the corrected denominators; the companion theorem `index_policy_optimal` says it attains $f(x,y)$.
--
--   **Formalization Note** The paper prints $prx/(1-r)$ and $qsy/(1-s)$; this is a misprint, and the rule defined here uses $(1-p)$ and $(1-q)$, which is the rule the paper describes in words ("immediate expected gain over immediate expected loss"). The definitions carry no hypotheses; the theorems assume $0 < p, q < 1$, so the divisions are by nonzero numbers.
-- source:
--   Bellman, The theory of dynamic programming, Bull. Amer. Math. Soc. 60 (1954), p. 509, Eq. (8.3) (with (1−p), (1−q) in place of the misprinted (1−r), (1−s))

import Mathlib
import Definitions.Def_BellmanTheoryDP_GoldMining_Model

namespace BellmanTheoryDP.GoldMining

/-- The (corrected) index rule of Bellman's (8.3) at amounts `x` in Anaconda and `y` in
Bonanza: choose Anaconda iff `p r x / (1 - p) ≥ q s y / (1 - q)` (ties broken towards
Anaconda), otherwise Bonanza. -/
noncomputable def indexChoice (p q r s x y : ℝ) : Mine :=
  if q * s * y / (1 - q) ≤ p * r * x / (1 - p) then Mine.A else Mine.B

/-- The amounts left in the two mines before use number `n` when the index rule is applied
from initial amounts `(x, y)` (along the event that the machine stays undamaged). -/
noncomputable def indexState (p q r s x y : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x, y)
  | n + 1 =>
    let z := indexState p q r s x y n
    match indexChoice p q r s z.1 z.2 with
    | Mine.A => ((1 - r) * z.1, z.2)
    | Mine.B => (z.1, (1 - s) * z.2)

/-- The choice sequence obtained by unrolling the index rule from `(x, y)`: use number `n` goes
to the mine the rule selects at the current amounts `indexState … n`. -/
noncomputable def indexPolicy (p q r s x y : ℝ) : ChoiceSeq :=
  fun n => indexChoice p q r s (indexState p q r s x y n).1 (indexState p q r s x y n).2

end BellmanTheoryDP.GoldMining


