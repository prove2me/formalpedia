-- Prove2me | Definitions.Def_FreedmanTail_Bernstein_PartialSums
-- name    : FreedmanTail_Bernstein_PartialSums
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:31:50.132095+00:00
-- url     : https://prove2.me/theorems/c1541bd2-2977-43cb-964b-0048d7afcd63
-- title:
--   Definition (1.2)(f), (g) — S_n = X_1 + ⋯ + X_n, V_n = Var{X_n | ℱ_{n−1}}, T_n = V_1 + ⋯ + V_n
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability triple, $\mathcal F_0\subset\mathcal F_1\subset\mathcal F_2\subset\cdots$ an increasing sequence of sub-$\sigma$-fields of $\mathcal F$, and $X_1,X_2,\dots$ real random variables with $X_n$ measurable with respect to $\mathcal F_n$. This file defines, for $n\ge0$,
--
--   1. the **partial sums** $S_n=X_1+\cdots+X_n$, so $S_0=0$;
--   2. the **conditional variances** $V_n=\operatorname{Var}\{X_n\mid\mathcal F_{n-1}\}$ for $n\ge1$;
--   3. the **intrinsic time** $T_n=V_1+\cdots+V_n$, so $T_0=0$:
--   $$S_n=\sum_{i=1}^{n}X_i,\qquad T_n=\sum_{i=1}^{n}\operatorname{Var}\{X_i\mid\mathcal F_{i-1}\}.$$
--
--   Freedman measures time by $T_n$ rather than by $n$: run on the clock $T_n$, the process $S_n$ behaves like Brownian motion, and all tail bounds of the paper are stated jointly in $S_n$ and $T_n$.
--
--   **Formalization Note** The sequence of increments is indexed by all natural numbers but only $X_1,X_2,\dots$ are used ($X_0$ is never read), so indices agree with the paper. The conditional variance is Mathlib's `condVar`, $\operatorname{Var}\{X\mid\mathcal G\}=E[(X-E[X\mid\mathcal G])^2\mid\mathcal G]$; like every conditional expectation in Mathlib it is $0$ when its argument is not integrable, so the theorems that use $T_n$ assume each $X_n$ square integrable.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 101 (PDF p. 2), setup paragraph and (1.2) Definition (f), (g)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Freedman (1975), Definition (1.2)(f), p. 101: `S_n = X_1 + ⋯ + X_n`, so `S_0 = 0`.
The increments are indexed from `1`; `X 0` is never read. -/
def S (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, X i ω

/-- Freedman (1975), p. 101: `V_n = Var{X_n | ℱ_{n−1}}`, the conditional variance of the
`n`-th increment given `ℱ_{n−1}` (meaningful for `n ≥ 1`). -/
noncomputable def V (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) : Ω → ℝ :=
  condVar (ℱ (n - 1)) (X n) P

/-- Freedman (1975), Definition (1.2)(g), p. 101: `T_n = V_1 + ⋯ + V_n`, so `T_0 = 0`. -/
noncomputable def T (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, V ℱ X P i ω

end FreedmanTail.Bernstein


