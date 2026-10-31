-- Prove2me | Definitions.Def_SVFAppt_walkMax
-- name    : SVFAppt_walkMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:59.008192+00:00
-- url     : https://prove2.me/theorems/63395bcf-48c1-4d85-93a3-0626074a1f1f
-- title:
--   Maximum of a random walk started at $0$: $\max\{0,S_1,\dots,S_k\}$
-- statement:
--   For steps $y_1,\dots,y_k$ with partial sums $S_j=y_1+\cdots+y_j$, the **maximum of the walk started at $0$** is
--
--   $$\max\{0,S_1,\dots,S_k\}.$$
--
--   By the Lindley recursion, the waiting time of the patient in slot $k+1$ is this maximum for the walk whose steps are the slot steps $B_{\tau(i)}-x_{\tau(i)}$ taken backwards from slot $k$ (eq. (4) of the paper).
--
--   **Formalization Note** The steps are indexed by `Fin k` and summed in the given (forward) order; the empty partial sum $S_0=0$ supplies the $0$.
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, eq. (4), p. 10

import Mathlib

namespace SVFAppt

/-- **Maximum of a random walk started at 0: `max{0, S1, …, Sk}`.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, eq. (4), p. 10: "Wk+1 = max{0, S1, . . . , Sk}",
with `Sj` the partial sums of the steps of the walk.

For steps `y 0, …, y (k−1)`, `walkMax y = max{0, S_1, …, S_k}` where `S_j = y 0 + ⋯ + y (j−1)`.
The index `j = 0` contributes the empty sum `0`.

**Formalization Note** The steps are summed in the given (forward) order. In (4) the steps of
`W_{k+1}` are the slot steps taken backwards from slot `k`; the milestone `eq_3_waiting_max`
states that link with the reversed family. -/
noncomputable def walkMax {k : ℕ} (y : Fin k → ℝ) : ℝ :=
  (Finset.range (k + 1)).sup' ⟨0, by simp⟩
    (fun j => ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < j), y i)

end SVFAppt


