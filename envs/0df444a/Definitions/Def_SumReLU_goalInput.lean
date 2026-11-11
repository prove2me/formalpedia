-- Prove2me | Definitions.Def_SumReLU_goalInput
-- name    : SumReLU_goalInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:39.644378+00:00
-- url     : https://prove2.me/theorems/59a88b21-ce8c-4f73-b101-d415eb540ddf
-- title:
--   Input, output and resource conventions of the learner
-- statement:
--   The learner of the main theorem receives $k$ and $\epsilon$ in memory (cells $0$ and $1$) and the dimension through the machine dimension $d+1$. When it halts, its hypothesis is read from memory starting at the cell held in pointer register $1$: the vector $g\in\mathbb R^d$, then $k$ blocks each holding a coefficient $\alpha_j$ and a direction $v_j\in\mathbb R^d$. The decoded hypothesis is
--   $$
--   h(x)=g\cdot x+\sum_{j=1}^k\alpha_j\,|v_j\cdot x|,
--   $$
--   the form described on p.2 ("a linear function plus a positive linear combination of at most $k$ absolute-value functions"). The resource bound is $C\,(d+k+1/\epsilon)^C$, the reading of $\mathrm{poly}(d,k,1/\epsilon)$ by the convention of §2 with a single constant $C$.
--
--   **Formalization Note** The page fixes no input or output format; these are conventions. Every state decodes to exactly $k$ slots (an unused slot has $\alpha_j=0$), so there is no "no output" case.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Theorem 1.3 and the hypothesis form, p.2 (PDF p.4); Algorithm 1, lines 1, 8–9, p.12 (PDF p.14); §2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_GaussMixHH_Machine

namespace SumReLU

/-- **The input list of the learner** (Theorem 1.3; Algorithm 1, line 1), in memory from cell `0`:
`k, ε`. The machine dimension is `d + 1` (one example `(x, y)` per `sample`), held in pointer
`0` by `GaussMixHH.initState`, so the program reads `d` as `p[0] − 1`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Theorem 1.3, p.2 (PDF p.4): "given d, k ∈ ℤ₊, ϵ ∈ (0, 1), and access to independent examples";
Algorithm 1, p.12 (PDF p.14): "Input: k, ϵ > 0, and sample access to …".

**Formalization Note.** The page fixes no input format; this one is a convention. -/
noncomputable def goalInput (k : ℕ) (ε : ℝ) : List ℝ := [(k : ℝ), ε]

/-- A hypothesis of the paper's form `h(x) = g · x + ∑_{j<k} α_j |v_j · x|`: a linear part `g`,
`k` coefficients `α` and `k` directions `v`. -/
structure Hypothesis (d k : ℕ) where
  /-- the linear part `g` -/
  g : EuclideanSpace ℝ (Fin d)
  /-- the coefficients `α_j` -/
  α : Fin k → ℝ
  /-- the directions `v_j` -/
  v : Fin k → EuclideanSpace ℝ (Fin d)

/-- The function `h(x) = g · x + ∑_j α_j |v_j · x|` of a hypothesis.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), p.2 (PDF p.4): "its hypothesis has a simple form: a linear function plus a positive linear
combination of at most k absolute-value functions, i.e., h(x) = g · x + ∑_{i=1}^k α_i|v_i · x|";
Algorithm 1, line 9, p.12 (PDF p.14). -/
noncomputable def hypFun {d k : ℕ} (H : Hypothesis d k) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ H.g x + ∑ j, H.α j * |inner ℝ (H.v j) x|

/-- **The output of a halted state**, decoded from memory with base `b = p[1]`: coordinate `i` of
`g` is cell `b + i`; `α_j` is cell `b + d + j(d + 1)`; coordinate `i` of `v_j` is cell
`b + d + j(d + 1) + 1 + i` (`i < d`, `j < k`).

**Formalization Note.** The page fixes no output format; this one is a convention. Every state
decodes to exactly `k` slots (an unused slot has `α_j = 0`), so there is no "no output" case. -/
noncomputable def decodeHypothesis (d k : ℕ) (s : GaussMixHH.State) : Hypothesis d k where
  g := WithLp.toLp 2 fun i : Fin d => s.core.mem (s.core.ptrs 1 + (i : ℤ))
  α := fun j => s.core.mem (s.core.ptrs 1 + (d : ℤ) + (j : ℤ) * ((d : ℤ) + 1))
  v := fun j => WithLp.toLp 2 fun i : Fin d =>
    s.core.mem (s.core.ptrs 1 + (d : ℤ) + (j : ℤ) * ((d : ℤ) + 1) + 1 + (i : ℤ))

/-- The resource bound `C · (d + k + 1/ε)^C`, the reading of `poly(d, k, 1/ϵ)` (§2, p.9, PDF p.11:
"g(t) ≤ poly(t) … there exist constants c, C > 0 such that g(t) ≤ Ct^c") with one constant `C`
for both the factor and the exponent. -/
noncomputable def resourceBound (C d k : ℕ) (ε : ℝ) : ℝ := (C : ℝ) * ((d : ℝ) + k + 1 / ε) ^ C

end SumReLU


