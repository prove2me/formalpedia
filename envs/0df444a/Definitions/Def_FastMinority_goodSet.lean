-- Prove2me | Definitions.Def_FastMinority_goodSet
-- name    : FastMinority_goodSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:42.086307+00:00
-- url     : https://prove2.me/theorems/67a46953-d419-46d5-ab38-88cb8bd333f1
-- title:
--   Good states $\mathcal H=\{x>0:\mathbb E[X_{t+1}\mid X_t=x]\le b\}$
-- statement:
--   For a constant $b$, a positive minority size $x\in\{1,\dots,\lfloor n/2\rfloor\}$ is **good** if the expected minority size after the next round is at most $b$. The set of good states is
--   $$
--   \mathcal H=\{x>0:\ \mathbb E[X_{t+1}\mid X_t=x]\le b\}. \tag{3.1}
--   $$
--   From every good state the next round reaches consensus with probability at least $e^{-8b}$ (Proposition 3.2), so good states are the attempts at consensus in the analysis.
--
--   **Formalization Note** States are counts with $2x\le n$. The source also writes $\mathcal H=[M'+1,R'-1]$ with $M'$, $R'$ never defined; this mission uses (3.1) as the definition of $\mathcal H$.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Eq. (3.1), p.6 (PDF p.8)

import Mathlib
import Definitions.Def_FastMinority_meanNext

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The set `H` of **good states** (3.1) (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.6 = PDF p.8):
`H = {x > 0 : E[X_{t+1} | X_t = x] ≤ b}`, a positive minority size whose expected next minority
size is at most the constant `b`.

**Formalization Note** States are counts `x ∈ Fin (n + 1)` restricted to the paper's state space
`{0, …, ⌊n/2⌋}` (`2x ≤ n`). The page also writes `H = [M′ + 1, R′ − 1]` with `M′`, `R′` never defined;
this mission uses (3.1) as the definition of `H` (the page: "it will be enough to use the upper and
lower bound on the endpoints of H given by M and R"). -/
def goodSet (n k : ℕ) (b : ℝ) : Set (Fin (n + 1)) :=
  {x | 0 < (x : ℕ) ∧ 2 * (x : ℕ) ≤ n ∧ meanNext n k x ≤ b}

end FastMinority


