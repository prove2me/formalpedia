-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Supplement_BlockPivot
-- name    : RankingQueryCost_Joint_Supplement_BlockPivot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:48:27.199489+00:00
-- url     : https://prove2.me/theorems/1ae6eeaf-40f8-4cc1-af56-7e1ea0ec016c
-- title:
--   Fresh pivoting restricted to a public block
-- statement:
--   Fix a public block $U$ of $m$ objects, a legal earlier cached state, a fixed-support comparison world, terminal width $b$, and depth cap $L$. Run the published fresh-uniform-pivot transitions starting with the single block $U$, preserving the earlier ledger. Stop each block at size at most $b$ or depth $L$.
--
--   $$D_U^2(r_U,\pi)=\sum_{i\in U}(r_U(i)-\pi(i))^2,\qquad e=|E\cap\tbinom U2|.$$
--
--   Here $r_U$ is the true local order. Outputs concatenate terminal buckets in their inherited order. A completion may permute each bucket and may depend on the entire realized state and fresh seed. Identifier completion uses public labels. Fresh independent uniform permutations provide uniform pivots. Depth $n$ removes the depth cap because each split removes one pivot. Requests include cached reads; only new ledger identities count toward acquisition.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §3.3, Lemmas 3.5 and 3.7, pp. 9–13, PDF pp. 10–14

import Definitions.Def_RankingQueryCost_Joint_Pivot

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint.Supplement

/-- The base fresh-pivot execution started on one public block, retaining its entire
earlier ledger and public history. n steps suffice since each split removes a pivot.
Use depth n for no depth truncation, and bfs=true for the depth-truncated version. -/
def blockExecution {n : ℕ} (U : Finset (Fin n)) (b L : ℕ)
    (select : BlockSelector n) (bfs : Bool) (W : ComparisonWorld n)
    (S : InteractionState n) (seed : PivotSeed n) : PivotState n :=
  (List.range n).foldl (fun P j => pivotStep b L select bfs W 0 seed j P)
    ⟨[(U, 0)], S, []⟩

/-- Local true ranks within U; only coordinates in U enter blockError. -/
def localRank {n : ℕ} (U : Finset (Fin n)) (r : Rank n) (i : Fin n) : ℝ :=
  ((U.filter fun j => r j < r i).card : ℝ)

def blockError {n : ℕ} (U : Finset (Fin n)) (r : Rank n) (output : List (Fin n)) : ℝ :=
  ∑ i ∈ U, (localRank U r i - (output.idxOf i : ℝ)) ^ 2

def internalFaults {n : ℕ} (U : Finset (Fin n)) (W : ComparisonWorld n) : ℕ :=
  (W.initial.filter fun e => e.1.1 ∈ U ∧ e.1.2 ∈ U).card

/-- Completion may depend on all fresh choices and the realized state. The only
constraint is to permute each terminal bucket internally, preserving bucket order. -/
abbrev BucketCompletion (n : ℕ) := PivotSeed n → PivotState n → Finset (Fin n) → List (Fin n)

def ValidCompletion {n : ℕ} (finish : BucketCompletion n) : Prop :=
  ∀ seed P U, (finish seed P U).Perm (U.sort (· ≤ ·))

def completedOutput {n : ℕ} (finish : BucketCompletion n) (seed : PivotSeed n)
    (P : PivotState n) : List (Fin n) :=
  P.slots.flatMap fun Ud => finish seed P Ud.1

def identifierOutput {n : ℕ} (P : PivotState n) : List (Fin n) :=
  P.slots.flatMap fun Ud => Ud.1.sort (· ≤ ·)

end RankingQueryCost.Joint.Supplement


