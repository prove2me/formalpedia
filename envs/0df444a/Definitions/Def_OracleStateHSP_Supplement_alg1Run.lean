-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_alg1Run
-- name    : OracleStateHSP_Supplement_alg1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:09:23.986949+00:00
-- url     : https://prove2.me/theorems/b57103a5-9863-473b-ba76-a48202a42c0a
-- title:
--   The run of Algorithm 1 with failure probability δ
-- statement:
--   Algorithm 1 (HSP-Sampling framework), on input a failure probability $\delta \in (0, 1]$ and an HSP-sampler, sets $S^\perp \leftarrow \emptyset$, $t \leftarrow 0$, $i \leftarrow 0$ and the initial budget
--   $$
--   b = \lceil \log_2 (1/\delta) \rceil ,
--   $$
--   runs the while-loop (`alg1Loop`) from the empty list of outputs, and returns $\mathrm{DUAL\text{-}SOLVER}(S^\perp)$. This definition is the law of the full list of sampler outputs; the returned generating set is $\mathrm{DUAL\text{-}SOLVER}$ applied to the data structure built from that list by UPDATE (`foldUpdate`).
--
--   **Formalization Note** Logarithms are base 2 (p.15). The recursion bound is $3(|G| + b) + 1$, more than the number of iterations of any run of positive probability when the sampler meets Definition 3.1.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Algorithm 1, p.21

import Mathlib
import Definitions.Def_OracleStateHSP_Supplement_alg1Loop

namespace OracleStateHSP

namespace Supplement

/-- The run of Algorithm 1 (HSP-Sampling framework, Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.21) with failure probability `δ`:
`S⊥ ← ∅`, `t ← 0`, `b ← ⌈log₂(1/δ)⌉`, `i ← 0`, then the while-loop `alg1Loop` from the empty
history. The result is the law of the full history of HSP-SAMPLER outputs.

**Formalization Note.** `log` is base 2 (p.15), and `b = ⌈log₂(1/δ)⌉₊` (`Nat.ceil`;
`log₂(1/δ) ≥ 0` for `δ ∈ (0, 1]`). The fuel `3(|G| + b) + 1` exceeds the number of iterations of
any trace of positive probability when the sampler meets Definition 3.1. The returned generating
set `DUAL-SOLVER(S⊥)` with `S⊥ = foldUpdate upd hist` is computed from the history. -/
noncomputable def alg1Run {Gh : Type*} [Fintype Gh] (samp : List (Option Gh) → PMF (Option Gh))
    (δ : ℝ) : PMF (List (Option Gh)) :=
  alg1Loop samp ⌈Real.logb 2 (1 / δ)⌉₊ (3 * (Fintype.card Gh + ⌈Real.logb 2 (1 / δ)⌉₊) + 1) []

end Supplement

end OracleStateHSP


