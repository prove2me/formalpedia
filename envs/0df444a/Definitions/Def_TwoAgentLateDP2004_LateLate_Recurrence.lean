-- Prove2me | Definitions.Def_TwoAgentLateDP2004_LateLate_Recurrence
-- name    : TwoAgentLateDP2004_LateLate_Recurrence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:46:34.860005+00:00
-- url     : https://prove2.me/theorems/2b82c70f-f88e-4991-b50c-c6af55747307
-- title:
--   The independent real-valued recurrence C and its signed-index extension
-- statement:
--   For EDD-numbered input jobs and nonnegative budgets, the table takes values in $\mathbb R\cup\{+\infty\}$. Its empty-prefix row is $C(0,h,k)=0$. For the next job, write $v=C(i-1,h,k)+p_i$ and $e=v$ if $v\le d_i$, otherwise $e=+\infty$. Then
--   $$C(i,h,k)=\begin{cases}\min(e,C(i-1,h-1,k))&i\text{ owned by A},\\\min(e,C(i-1,h,k-1))&i\text{ owned by B}.\end{cases}$$
--   A decremented zero budget gives $+\infty$; addition absorbs $+\infty$. The signed-index extension gives $+\infty$ whenever any index is negative. This is a recursive computation from the inputs, independent of any optimality specification.
--   **Formalization Note** Completing the unspecified zero row uses the source's at-most budgets. Rows beyond $n$ repeat the final row and occur in no theorem. The finite values are real, without an integrality restriction.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici (2004), Scheduling Problems with Two Competing Agents, Operations Research 52(2):229–242, https://doi.org/10.1287/opre.1030.0092, §7, Boundary Conditions / Recursion Relation, p.236 (PDF p.8), unnumbered displays

import Mathlib
import Definitions.Def_TwoAgentLateDP2004_LateLate_Model

namespace TwoAgentLateDP2004.LateLate

/-- Independent recurrence, §7 Boundary Conditions / Recursion Relation, p.236.
Complete the unspecified zero row by zero for all at-most budgets.
A zero budget is tested before decrementing; missing predecessors are +∞.
Rows beyond n repeat the final row and are never used by the statements. -/
noncomputable def C {n : ℕ} (I : Input n) : ℕ → ℕ → ℕ → WithTop ℝ
  | 0, _, _ => 0
  | i + 1, h, k =>
    if hi : i < n then
      let v := C I i h k + (I.p ⟨i, hi⟩ : WithTop ℝ)
      let early := if v ≤ (I.d ⟨i, hi⟩ : WithTop ℝ) then v else ⊤
      let omitted :=  if I.owner ⟨i, hi⟩ then
        if h = 0 then ⊤ else C I i (h - 1) k
        else if k = 0 then ⊤ else C I i h (k - 1)
      min early omitted
    else C I i h k

/-- The printed signed-index convention, including negative Q. -/
noncomputable def signedC {n : ℕ} (I : Input n) (i h k : ℤ) : WithTop ℝ :=
  if i < 0 ∨ h < 0 ∨ k < 0 then ⊤ else C I i.toNat h.toNat k.toNat

end TwoAgentLateDP2004.LateLate


