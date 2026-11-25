-- Prove2me | Definitions.Def_DetDLP_D4UnrollBudget
-- name    : DetDLP_D4UnrollBudget
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:29:23.31257+00:00
-- url     : https://prove2.me/theorems/eeb9886b-1177-49a7-b593-a3b20e2a7952
-- title:
--   Adaptive 64-child worklist and binary rank budget
-- statement:
--   A work item records absolute depth and edge count. A choice enqueues the 64 children in their original order, with edge counts depending on the chosen digit. The depth budget is computed using the final integer square-root width.

import Definitions.Def_DetDLP_D3StoppedSchedule
import Definitions.Def_DetDLP_D4RankCode
set_option autoImplicit false
namespace DetDLP.D4UnrollBudget
open AppendixD4 D3Stopped D4RankCode
/-- A work item records its absolute depth and its internal edge count. An active rank
choice puts all sixty-four children on the worklist; their masses may depend on the digit. -/
inductive Work {α : Type} (S D K : ℕ) : List (ℕ × ℕ) → D4RankCode.Tree α → Prop where
  | done (z : α) : Work S D K [] (.leaf z)
  | stop {d M rest t} (h : D ≤ d ∨ M ≤ threshold S) (tail : Work S D K rest t) :
      Work S D K ((d,M)::rest) t
  | step {d M : ℕ} {rest} {n : ℕ} {f : Fin n → D4RankCode.Tree α} (hd : d < D) (hm : threshold S < M)
      (count : (n:ℝ) ≤ (2^(shift S d+1)*points M (shift S d):ℕ)*
        Real.exp ((K:ℝ)*M/Real.sqrt (width S d)))
      (child : Fin n → Fin 64 → ℕ) (mass : ∀ i, ∑ g, child i g = 2*M)
      (tail : ∀ i, Work S D K ((List.ofFn fun g => (d+1,child i g)) ++ rest) (f i)) :
      Work S D K ((d,M)::rest) (.choice n f)
/-- Uniform integer budget. The additive term pays for the grid, the interpolation index,
and binary rounding. The mass term shares one denominator across all expanded nodes. -/
def budget (S D K : ℕ) :=
  8*(D3Stopped.level S+1)*64^D + (2*K*(2^D-1)*S) / max 1 (width S D).sqrt
end DetDLP.D4UnrollBudget


