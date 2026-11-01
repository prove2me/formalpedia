-- Prove2me | Definitions.Def_ActiveCtxSearch_MetaAlgorithm
-- name    : ActiveCtxSearch_MetaAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:43:05.459754+00:00
-- url     : https://prove2.me/theorems/f776039f-e718-4cef-87f4-e1598688b8f3
-- title:
--   Algorithm 1: the meta-algorithm
-- statement:
--   **Algorithm 1**, with inputs $d$, $\varepsilon$, $\delta$, $\kappa_m,\kappa_n,\kappa_\varepsilon,\beta_0$ and the bound $B$ of (A1), reads one stream:
--
--   1. $(\hat b_1,\hat b_2)\leftarrow\mathrm{TrisectionSearch}(\varepsilon_s,\delta_s)$ with $\varepsilon_s=0.1/\sqrt{d-1}$ and $\delta_s=\delta/3$;
--   2. $\varepsilon_a=\kappa_\varepsilon\varepsilon^2/\ln^2(1/\varepsilon)$, $\delta_a=\delta/3$;
--   3. $(\hat w_1,\hat\beta_1)\leftarrow\mathrm{MarginBasedActiveLearning}(\hat b_1,\varepsilon_a,\delta_a,\kappa_m,\kappa_n,\sqrt{\varepsilon_a},\beta_0)$;
--   4. $(\hat w_2,\hat\beta_2)\leftarrow\mathrm{MarginBasedActiveLearning}(\hat b_2,\varepsilon_a,\delta_a,\kappa_m,\kappa_n,\sqrt{\varepsilon_a},\beta_0)$;
--   5. $\hat\alpha=(\hat b_2-\hat b_1)/(\hat\beta_2-\hat\beta_1)$;
--   6. output $\hat v(\cdot)=\langle\cdot,\hat w\rangle-\hat\mu$ with $\hat w=\hat\alpha\hat w_1$ and $\hat\mu=\hat\alpha\hat\beta_1-\hat b_1$.
--
--   The three subroutines read consecutive segments of the stream. The run records $(\hat w,\hat\mu)$, the number of queries $n$ and the number of items read $m$; it has no result if a subroutine does not halt.
--
--   **Formalization Note** Logarithms are natural. If $\hat\beta_2=\hat\beta_1$, Lean's division gives $\hat\alpha=0$; the source leaves the case undefined and no statement excludes it.
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, Algorithm 1, p.9

import Mathlib
import Definitions.Def_ActiveCtxSearch_Trisection
import Definitions.Def_ActiveCtxSearch_MarginAL

open MeasureTheory
open scoped RealInnerProductSpace

namespace ActiveCtxSearch

/-- The output of Algorithm 1: the estimate `v̂(·) = ⟨·, ŵ⟩ − μ̂` as `(ŵ, μ̂)`, the number of queries
`n` and the number of items read `m` (queried or passed). -/
structure MetaResult (d : ℕ) where
  what : E d
  μhat : ℝ
  queries : ℕ
  items : ℕ

namespace Problem

variable {d : ℕ}

/-- **Algorithm 1**, arXiv:2110.01072v2, p.9, run on the stream `ω` from its first item, with the
bound `B` of (A1) (used by Algorithm 2's initialization), accuracy parameters `ε, δ`, algorithm
parameters `κ_m, κ_n, κ_ε` and the tie-breaking rule `sel` of the arg min in Algorithm 3:

1. `(b̂₁, b̂₂) ← TrisectionSearch(ε_s, δ_s)` with `ε_s = 0.1/√(d − 1)`, `δ_s = δ/3`;
2. `ε_a = κ_ε ε²/ln²(1/ε)`, `δ_a = δ/3`;
3. `(ŵ₁, β̂₁) ← MarginBasedActiveLearning(b̂₁, ε_a, δ_a, κ_m, κ_n, √ε_a, β₀)`;
4. `(ŵ₂, β̂₂) ← MarginBasedActiveLearning(b̂₂, ε_a, δ_a, κ_m, κ_n, √ε_a, β₀)`;
5. `α̂ = (b̂₂ − b̂₁)/(β̂₂ − β̂₁)`;
6. output `v̂(·) = ⟨·, ŵ⟩ − μ̂` with `ŵ = α̂ ŵ₁` and `μ̂ = α̂ β̂₁ − b̂₁`.

The three subroutines read consecutive segments of the same stream. The result is `none` if a
subroutine does not halt.

**Formalization Note** Logarithms are natural. `β₀` enters only through the hypothesis
`IsERMSelection β₀ sel`. If `β̂₂ = β̂₁`, Lean's division gives `α̂ = 0`; the source leaves this case
undefined, and no statement excludes it. -/
noncomputable def metaAlgorithm (I : Problem d) (B ε δ κm κn κε : ℝ)
    (sel : List (E d × ℤ) → E d × ℝ) (ω : ℕ → E d × ℝ) : Option (MetaResult d) :=
  let εs := 0.1 / Real.sqrt ((d : ℝ) - 1)
  let δs := δ / 3
  let εa := κε * ε ^ 2 / Real.log (1 / ε) ^ 2
  (I.trisection B εs δs ω 0).bind fun T =>
    (I.marginAL T.b1 εa κm κn (Real.sqrt εa) sel ω T.endPos).bind fun R1 =>
      (I.marginAL T.b2 εa κm κn (Real.sqrt εa) sel ω R1.endPos).map fun R2 =>
        let α := (T.b2 - T.b1) / (R2.c.2 - R1.c.2)
        { what := α • R1.c.1, μhat := α * R1.c.2 - T.b1,
          queries := T.queries + R1.queries + R2.queries, items := R2.endPos }

end Problem

end ActiveCtxSearch


