-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_alg1Loop
-- name    : OracleStateHSP_Supplement_alg1Loop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:08:45.10831+00:00
-- url     : https://prove2.me/theorems/4db9ccc4-0cf1-47c8-9c62-47105ad80910
-- title:
--   The while-loop of Algorithm 1 (HSP-Sampling framework)
-- statement:
--   Algorithm 1 keeps an iteration counter $t$ and a counter $i$ of span-increasing generators, both initially $0$, and an initial budget $b$. While $t < 3(i + b)$ it calls $s^\perp \leftarrow \mathrm{HSP\text{-}SAMPLER}(S^\perp, 1/2)$; if $s^\perp \ne \mathrm{END}$ it sets $S^\perp \leftarrow \mathrm{UPDATE}(S^\perp, s^\perp)$ and $i \leftarrow i + 1$; then $t \leftarrow t + 1$.
--
--   This definition is the law of the full list of sampler outputs produced by the loop, started from a given list of outputs and allowed at most a given number $k$ of further iterations: $t$ is the length of the list and $i$ the number of its non-END entries.
--
--   **Formalization Note** The bound $k$ only makes the recursion well-founded; the run of Algorithm 1 (`alg1Run`) uses a bound that the loop never reaches on an output list of positive probability, and Theorem 3.4 states that the loop's own exit condition holds there.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Algorithm 1, p.21

import Mathlib

namespace OracleStateHSP

namespace Supplement

/-- The while-loop of Algorithm 1 (HSP-Sampling framework, Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.21), run for at most `k` more
iterations from the history `hist` of sampler outputs (`none` = END). With `t = |hist|` iterations
done and `i` = the number of non-END outputs so far (one `UPDATE` call and one increment of `i`
each), the loop body runs while `t < 3(i + b)`: it draws `s⊥ ← samp hist` (one HSP-SAMPLER call)
and appends it to the history. The result is the law of the final history.

**Formalization Note.** `k` is a fuel bound for the recursion; `alg1Run` uses a fuel that the loop
never exhausts on a trace of positive probability (theorem 3.4 proves the exit condition holds
there). -/
noncomputable def alg1Loop {Gh : Type*} (samp : List (Option Gh) → PMF (Option Gh)) (b : ℕ) :
    ℕ → List (Option Gh) → PMF (List (Option Gh))
  | 0, hist => PMF.pure hist
  | k + 1, hist =>
      if hist.length < 3 * ((hist.filter Option.isSome).length + b) then
        (samp hist).bind fun o => alg1Loop samp b k (hist ++ [o])
      else PMF.pure hist

end Supplement

end OracleStateHSP


