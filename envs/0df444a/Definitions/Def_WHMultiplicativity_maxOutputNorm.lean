-- Prove2me | Definitions.Def_WHMultiplicativity_maxOutputNorm
-- name    : WHMultiplicativity_maxOutputNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:24:31.227527+00:00
-- url     : https://prove2.me/theorems/34d8945a-bf77-44e0-b79a-148b1e1e6335
-- title:
--   Maximal output $p$-norm $\nu_p(\Phi) = \sup_\rho \|\Phi(\rho)\|_p$ (eq. 1)
-- statement:
--   For a map $\Phi$ taking density operators on $\mathbb C^n$ to operators on $\mathbb C^m$ and $1 < p \le \infty$, the **maximal output $p$-norm** is
--
--   $$
--   \nu_p(\Phi) = \sup_{\rho} \|\Phi(\rho)\|_p ,
--   $$
--
--   where the supremum is over all input density operators $\rho$. Large $\nu_p(\Phi)$ means that $\Phi$ can produce nearly pure outputs. The conjecture of Amosov, Holevo and Werner disproved by this mission is that $\nu_p(S_1\otimes S_2) = \nu_p(S_1)\,\nu_p(S_2)$ for all channels $S_1, S_2$.
--
--   **Formalization Note** $\nu_p$ is the real supremum (`sSup`) of `outputNorms p Φ`. Lean's `sSup` of an empty or unbounded set of reals is $0$, so every theorem of the mission that uses $\nu_p$ also asserts that the set of output norms is bounded above.
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, eq. (1), p.1

import Mathlib
import Definitions.Def_WHMultiplicativity_outputNorms

open scoped ENNReal

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, eq. (1), p.1: the maximal output `p`-norm
`ν_p(S) = sup ‖S(ρ)‖_p`, "where the supremum is over all input density operators"; with `p = ⊤`
this is `ν_∞(S)`, the supremum of the operator norms of the outputs (§I.B, p.1).

**Formalization Note.** `ν_p` is the real `sSup` of `outputNorms p Φ`. Lean's `sSup` of an empty
or unbounded set of reals is `0`, so every statement of this mission that uses `maxOutputNorm`
also asserts `BddAbove (outputNorms p Φ)` for the maps it mentions (the sets are nonempty
whenever the input type is nonempty). -/
noncomputable def maxOutputNorm {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ℝ≥0∞) (Φ : QAlgorithms.Superop ι κ) : ℝ :=
  sSup (outputNorms p Φ)

end WHMultiplicativity


