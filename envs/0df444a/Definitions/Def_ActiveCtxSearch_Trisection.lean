-- Prove2me | Definitions.Def_ActiveCtxSearch_Trisection
-- name    : ActiveCtxSearch_Trisection
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:40:49.041253+00:00
-- url     : https://prove2.me/theorems/cbc61ce0-c9dd-4e21-8297-49a62b7252cf
-- title:
--   Algorithm 2: trisection search for the balancing action
-- statement:
--   **Algorithm 2** ($\mathrm{TrisectionSearch}(\varepsilon_s,\delta_s)$) with the bound $B$ of (A1):
--
--   1. Initialize $n=0$, $\hat b_1=-B$, $\hat b_2=B$.
--   2. While $\hat b_2-\hat b_1>\varepsilon_s$: set $\hat b_3=\hat b_1+(\hat b_2-\hat b_1)/3$, $\hat b_4=\hat b_2-(\hat b_2-\hat b_1)/3$, $\hat n=\hat r_3=\hat r_4=0$, $\underline p_3=\underline p_4=0$, $\overline p_3=\overline p_4=1$.
--   3. While $\underline p_3\le 0.5\le\overline p_3$ and $\underline p_4\le0.5\le\overline p_4$: query the next item at $\hat b_3$ (feedback $y$) and the item after it at $\hat b_4$ (feedback $y'$); set $n\leftarrow n+1$, $\hat n\leftarrow\hat n+1$, $\hat r_3\leftarrow\hat r_3+\mathbf 1\{y=1\}$, $\hat r_4\leftarrow\hat r_4+\mathbf 1\{y'=1\}$ and
--   $$[\underline p_j,\overline p_j]\leftarrow\frac{\hat r_j}{\hat n}\pm\sqrt{\frac{\ln(8n^2/\delta_s)}{2\hat n}},\qquad j=3,4.$$
--   4. Set $\hat b_1\leftarrow\hat b_3$ if $\underline p_3>0.5$ or $\underline p_4>0.5$, and $\hat b_2\leftarrow\hat b_4$ otherwise.
--   5. Return $(\hat b_1,\hat b_2)$.
--
--   The run on a stream records the returned pair, the number of queries $2n$ and the position after the last item read; it has no result if some inner loop never stops.
--
--   **Formalization Note** The source's $y\in\{0,1\}$ is $\mathbf 1\{\text{feedback}=+1\}$, and line 8's $y_3,y_4$ are the $y,y'$ of lines 6–7. The global counter $n$ is never reset. Every item read is queried.
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, Algorithm 2, p.11

import Mathlib
import Definitions.Def_ActiveCtxSearch_Stream
import Definitions.Def_ActiveCtxSearch_WhileLoop

open MeasureTheory

namespace ActiveCtxSearch

/-- The state of the outer loop of Algorithm 2: the bracket `[b̂₁, b̂₂]`, the global counter `n` of
inner iterations, and the position of the next unread item of the stream. -/
structure TriState where
  b1 : ℝ
  b2 : ℝ
  n : ℕ
  pos : ℕ

/-- The state of the inner loop of Algorithm 2: the global counter `n`, the local counter `n̂`, the
counts `r̂₃, r̂₄` of positive feedback, the confidence intervals `[p̲₃, p̄₃]`, `[p̲₄, p̄₄]`, and the
position of the next unread item. -/
structure TriInner where
  n : ℕ
  nh : ℕ
  r3 : ℕ
  r4 : ℕ
  p3lo : ℝ
  p3hi : ℝ
  p4lo : ℝ
  p4hi : ℝ
  pos : ℕ

/-- The output of Algorithm 2: the returned pair `(b̂₁, b̂₂)`, the number of queries, and the position
of the next unread item (so items `0, …, endPos − 1` relative to the start have been read). -/
structure TriResult where
  b1 : ℝ
  b2 : ℝ
  queries : ℕ
  endPos : ℕ

namespace Problem

variable {d : ℕ}

/-- The continuation condition of the inner loop of Algorithm 2, line 5:
`p̲₃ ≤ 0.5 ≤ p̄₃` and `p̲₄ ≤ 0.5 ≤ p̄₄`. -/
def triInnerCond (s : TriInner) : Prop :=
  s.p3lo ≤ 1 / 2 ∧ 1 / 2 ≤ s.p3hi ∧ s.p4lo ≤ 1 / 2 ∧ 1 / 2 ≤ s.p4hi

/-- One pass of the inner loop of Algorithm 2, lines 6–9 (arXiv:2110.01072v2, p.11): query the next
item at `b̂₃` (feedback `y`) and the item after it at `b̂₄` (feedback `y′`), set `n ← n + 1`,
`n̂ ← n̂ + 1`, `r̂₃ ← r̂₃ + 1{y = 1}`, `r̂₄ ← r̂₄ + 1{y′ = 1}`, and
`[p̲ⱼ, p̄ⱼ] ← r̂ⱼ/n̂ ± √(ln(8n²/δ_s)/(2n̂))`.

**Formalization Note** The `y ∈ {0, 1}` of lines 6–7 is `1{response = 1}`; line 8's `y₃, y₄` are the
`y, y′` of lines 6–7. -/
noncomputable def triInnerStep (I : Problem d) (b3 b4 δs : ℝ) (ω : ℕ → E d × ℝ)
    (s : TriInner) : TriInner :=
  let y : ℕ := if I.response (ω s.pos) b3 = 1 then 1 else 0
  let y' : ℕ := if I.response (ω (s.pos + 1)) b4 = 1 then 1 else 0
  let n := s.n + 1
  let nh := s.nh + 1
  let r3 := s.r3 + y
  let r4 := s.r4 + y'
  let rad := Real.sqrt (Real.log (8 * (n : ℝ) ^ 2 / δs) / (2 * nh))
  { n := n, nh := nh, r3 := r3, r4 := r4,
    p3lo := r3 / nh - rad, p3hi := r3 / nh + rad,
    p4lo := r4 / nh - rad, p4hi := r4 / nh + rad,
    pos := s.pos + 2 }

/-- One pass of the outer loop of Algorithm 2, lines 4–11 (arXiv:2110.01072v2, p.11):
`b̂₃ ← b̂₁ + (b̂₂ − b̂₁)/3`, `b̂₄ ← b̂₂ − (b̂₂ − b̂₁)/3`, reset `n̂ = r̂₃ = r̂₄ = 0`, `p̲₃ = p̲₄ = 0`,
`p̄₃ = p̄₄ = 1`, run the inner loop, then set `b̂₁ ← b̂₃` if `p̲₃ > 0.5` or `p̲₄ > 0.5`, and `b̂₂ ← b̂₄`
otherwise. Returns `none` if the inner loop does not halt. -/
noncomputable def triOuterStep (I : Problem d) (δs : ℝ) (ω : ℕ → E d × ℝ) (s : TriState) :
    Option TriState :=
  let b3 := s.b1 + (s.b2 - s.b1) / 3
  let b4 := s.b2 - (s.b2 - s.b1) / 3
  let init : TriInner :=
    { n := s.n, nh := 0, r3 := 0, r4 := 0, p3lo := 0, p3hi := 1, p4lo := 0, p4hi := 1,
      pos := s.pos }
  (whileRun triInnerCond (fun t => some (I.triInnerStep b3 b4 δs ω t)) init).map fun t =>
    if 1 / 2 < t.p3lo ∨ 1 / 2 < t.p4lo then
      { b1 := b3, b2 := s.b2, n := t.n, pos := t.pos }
    else
      { b1 := s.b1, b2 := b4, n := t.n, pos := t.pos }

/-- **Algorithm 2** (`TrisectionSearch(ε_s, δ_s)`), arXiv:2110.01072v2, p.11, run on the stream `ω`
from item `start`, with the bound `B` of (A1) as the initial bracket `[−B, B]` (line 2):
`while b̂₂ − b̂₁ > ε_s do` the outer step; `return (b̂₁, b̂₂)`.

The result records the returned pair, the number of queries (two per inner iteration, so `2n`
with `n` the final global counter) and the position after the last item read. It is `none` if the
algorithm does not halt on `ω`.

**Formalization Note** Every item read by Algorithm 2 is queried, so the number of items read is also
`2n`. -/
noncomputable def trisection (I : Problem d) (B εs δs : ℝ) (ω : ℕ → E d × ℝ) (start : ℕ) :
    Option TriResult :=
  (whileRun (fun s : TriState => εs < s.b2 - s.b1) (I.triOuterStep δs ω)
      { b1 := -B, b2 := B, n := 0, pos := start }).map fun s =>
    { b1 := s.b1, b2 := s.b2, queries := 2 * s.n, endPos := s.pos }

end Problem

end ActiveCtxSearch


