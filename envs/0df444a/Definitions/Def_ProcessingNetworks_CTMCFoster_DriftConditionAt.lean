-- Prove2me | Definitions.Def_ProcessingNetworks_CTMCFoster_DriftConditionAt
-- name    : ProcessingNetworks_CTMCFoster_DriftConditionAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:43.521483+00:00
-- url     : https://prove2.me/theorems/4ee315a3-9cfc-45f5-bc97-35ca35cdbdf7
-- title:
--   The drift inequality (D.36) at a state
-- statement:
--   Let $\Lambda$ be a generator matrix on $\mathscr S$, let $V:\mathscr S\to\mathbb R$, let $b,c\in\mathbb R$ and $C\subseteq\mathscr S$. The drift inequality at the state $i$ says that the series defining $\Lambda V(i)$ converges and
--
--   $$
--   \Lambda V(i)=\sum_{j}\Lambda_{ij}V(j)\le -c+b\,1_C(i).
--   $$
--
--   This is the condition of the Foster–Lyapunov criterion for continuous-time chains.
--
--   **Formalization Note** Convergence of the row is part of the condition, because Lean assigns the value $0$ to a divergent real series. For $V\ge0$ the only negative term is the diagonal one, so a divergent row means $\Lambda V(i)=+\infty$, for which the printed inequality fails too.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.27, eq. (D.36), p.298 (PDF 314)

import Mathlib

namespace ProcessingNetworks.CTMCFoster

/-- The drift inequality (D.36) at the state `i`: the row sum
`ΛV(i) = ∑_j Λ i j * V j` converges and `ΛV(i) ≤ -c + b 1_C(i)`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.27,
eq. (D.36), p.298 (PDF 314).

**Formalization Note** Convergence of the row is part of the condition: a real `tsum` of a
non-summable row is `0` in Lean, which would make the inequality easier to satisfy for unbounded
`V`. For `V ≥ 0` the only negative term of the row is the diagonal one, so a divergent row means
`ΛV(i) = +∞`, for which the book's inequality fails as well. -/
def DriftConditionAt {S : Type*} (Λ : S → S → ℝ) (V : S → ℝ) (b c : ℝ) (C : Set S) (i : S) : Prop :=
  Summable (fun j => Λ i j * V j) ∧
    ∑' j, Λ i j * V j ≤ -c + C.indicator (fun _ => b) i

end ProcessingNetworks.CTMCFoster


