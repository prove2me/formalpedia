-- Prove2me | Definitions.Def_PCLAssort_PipageStep
-- name    : PCLAssort_PipageStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:20.012791+00:00
-- url     : https://prove2.me/theorems/a37aca0e-6315-4267-9e3b-238286051d31
-- title:
--   One step of pipage rounding
-- statement:
--   One iteration of pipage rounding, for sizes $s$ and objective $F$, replaces $x$ by $\tilde x$ as follows:
--
--   1. pick two fractional variables $i\ne j$, i.e. $0<x_i,x_j<1$;
--   2. let $\epsilon^*$ be one of $-\min\{x_i,\tfrac{s_j}{s_i}(1-x_j)\}$ and $\min\{1-x_i,\tfrac{s_j}{s_i}x_j\}$ with $\phi(x,i,j,\epsilon^*)\ge F(x)$;
--   3. set $\tilde x=(x_1,\dots,x_i+\epsilon^*,\dots,x_j-\tfrac{s_i}{s_j}\epsilon^*,\dots,x_n)$.
--
--   **Formalization Note** The step is a relation: every admissible choice of the pair and of the endpoint is a possible step, matching "pick any two fractional variables".
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.3, pipage rounding steps 1–4, p.794 (PDF p.10)

import Mathlib
import Definitions.Def_PCLAssort_pipageMove
import Definitions.Def_PCLAssort_pipageEpsLo
import Definitions.Def_PCLAssort_pipageEpsHi

namespace PCLAssort

/-- One iteration of pipage rounding (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.3, steps 1–4, p.794): pick two fractional variables
`i ≠ j` (`0 < x_i, x_j < 1`); let `ε*` be `−min{x_i, (s_j/s_i)(1 − x_j)}` or
`min{(1 − x_i), (s_j/s_i) x_j}` with `φ(x, i, j, ε*) ≥ F(x)`; and replace `x` by
`x̃ = (x_1, …, x_i + ε*, …, x_j − (s_i/s_j) ε*, …, x_n)`.

**Formalization Note.** The step is a relation `x ↦ x'`: every choice of the pair and of an
admissible endpoint is a possible step, as in the text ("pick any two fractional variables"). -/
def PipageStep {V : Type} [DecidableEq V] (s : V → ℝ) (F : (V → ℝ) → ℝ) (x x' : V → ℝ) : Prop :=
  ∃ i j : V, i ≠ j ∧ (0 < x i ∧ x i < 1) ∧ (0 < x j ∧ x j < 1) ∧
    ∃ ε : ℝ, (ε = pipageEpsLo s x i j ∨ ε = pipageEpsHi s x i j) ∧
      F x ≤ F (pipageMove s x i j ε) ∧ x' = pipageMove s x i j ε

end PCLAssort


