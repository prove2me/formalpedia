-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_ucbIndex
-- name    : FoundationsRL_EluderUCB_ucbIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:42.744444+00:00
-- url     : https://prove2.me/theorems/81b4b448-93f9-4796-b768-70b647af8e48
-- title:
--   The upper confidence bound $\bar f^t$
-- statement:
--   The upper confidence bound of round $t$ is
--
--   $$
--   \bar f^t(\pi):=\max_{f\in\mathcal F^t}f(\pi).
--   $$
--
--   **Formalization Note** The maximum is a real supremum. In every theorem $\mathcal F$ is finite and contains $\hat f^t$ in $\mathcal F^t$ (for $\beta\ge0$), so the supremum is over a finite nonempty set and is attained.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (4.6) and the line before it, p. 58

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_confidenceSet

namespace FoundationsRL.EluderUCB

/-- **The upper confidence bound.** Foster & Rakhlin, arXiv:2312.16730v1, p. 58:
`f̄ᵗ(π) := max_{f ∈ Fᵗ} f(π)`.

**Formalization Note.** The maximum is the real `sSup` of `{f(π) : f ∈ Fᵗ}`. In every theorem `F` is
finite and `f̂ᵗ ∈ Fᵗ` (the minimizer belongs to its own confidence set when `β ≥ 0`), so that set is
finite and nonempty, the supremum is attained, and neither junk value of `sSup` occurs. -/
noncomputable def ucbIndex {Act : Type*} (F : Set (Act → ℝ)) (β : ℝ) (π : ℕ → Act) (r : ℕ → ℝ)
    (t : ℕ) (fhat : Act → ℝ) (p : Act) : ℝ :=
  sSup ((fun f : Act → ℝ => f p) '' confidenceSet F β π r t fhat)

end FoundationsRL.EluderUCB


