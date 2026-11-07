-- Prove2me | Definitions.Def_LDPSelect_bellman
-- name    : LDPSelect_bellman
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:19.626095+00:00
-- url     : https://prove2.me/theorems/c156b442-29f0-4f1b-8480-303fdc75f609
-- title:
--   The interactive Bellman value over position and accepted set
-- statement:
--   For a downward-closed $\mathcal F$, values with laws $P_1,\dots,P_n$ and privacy level $a$, let $V_i(A)$ be the value from position $i$ with accepted set $A$:
--
--   $$V_{n+1}(A)=0,\qquad V_i(A)=\begin{cases}V_{i+1}(A\cup\{i\})+F_a\big(X_i,\ V_{i+1}(A)-V_{i+1}(A\cup\{i\})\big), & A\cup\{i\}\in\mathcal F,\\ V_{i+1}(A), & \text{otherwise}.\end{cases}$$
--
--   At a feasible user the decision is "take $X_i$ and move to $A\cup\{i\}$" against "take the continuation $V_{i+1}(A)$", and the one-stage value (1) prices one private report; the threshold is the rejection value minus the acceptance value.
--
--   **Formalization Note** Positions are $0,\dots,n-1$ in Lean, and the value is $0$ from position $n$ on.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §6, p.10 (pdf p.11); A.8, p.21 (pdf p.22); display (1), p.5 (pdf p.6)

import Mathlib
import Definitions.Def_LDPSelect_Family
import Definitions.Def_LDPSelect_Fa

open MeasureTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-!
# The interactive Bellman value

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), §6, p.10 and A.8, p.21: "An optimal interactive policy can be taken to depend only on the
position and the accepted set"; "interactive Bellman value", p.7; display (1), p.5.

**Formalization Note.** Positions are `0, …, n`, and `bellman a P F i A` is the value from position `i`
with accepted set `A`. The recursion takes the rejection value minus the acceptance value as the
threshold `s` of (1). Its value is `0` from position `n` on.
-/

/-- `V_n(A) = 0`; `V_i(A) = V_{i+1}(A)` if `A ∪ {i} ∉ F`; otherwise
`V_i(A) = V_{i+1}(A ∪ {i}) + F_a(X_i, V_{i+1}(A) − V_{i+1}(A ∪ {i}))`. -/
noncomputable def bellman {n : ℕ} (a : ℝ) (P : Fin n → Measure ℝ≥0) (F : Family n) :
    ℕ → Finset (Fin n) → ℝ
  | i, A =>
    open Classical in
    if h : i < n then
      if A ∪ {⟨i, h⟩} ∈ F then
        bellman a P F (i + 1) (A ∪ {⟨i, h⟩}) +
          Fa a (P ⟨i, h⟩) (bellman a P F (i + 1) A - bellman a P F (i + 1) (A ∪ {⟨i, h⟩}))
      else
        bellman a P F (i + 1) A
    else 0
termination_by i => n - i

end LDPSelect


