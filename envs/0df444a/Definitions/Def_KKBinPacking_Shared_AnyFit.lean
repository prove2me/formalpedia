-- Prove2me | Definitions.Def_KKBinPacking_Shared_AnyFit
-- name    : KKBinPacking_Shared_AnyFit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:17:40.601218+00:00
-- url     : https://prove2.me/theorems/3caf8a82-8ff8-4c12-996f-7ac9a8588a1c
-- title:
--   Inserting pieces using a new bin only when necessary
-- statement:
--   Let $P$ be a multiset of bins and $S$ a multiset of pieces. **Inserting the pieces of $S$ into $P$, starting a new bin only when necessary**, is the following nondeterministic process. While pieces remain, choose any remaining piece $p$. If $p$ fits into some existing bin $b$ (the load of $b$ plus $p$ is at most $1$), put $p$ into any such bin; otherwise open a new bin containing only $p$. The relation $\mathrm{AnyFit}(P, S, Q)$ holds when some execution of this process ends with the bins $Q$.
--
--   This is the insertion step of Lemma 3, of Step 7 of ALGORITHM 1 and of Step 4 of ALGORITHM 2.
--
--   **Formalization Note** The relation is inductive, with three rules: nothing left to insert; insert a piece of $S$ into an existing bin where it fits; open a new bin for a piece of $S$ only if it fits into no existing bin. The order of insertion and the choice of bin are unrestricted, so every theorem about the process holds for every such execution (in particular for First Fit).
--
--   It serves both missions of the series: `01-linear-grouping` (Lemma 3, p. 314; ALGORITHM 1, Step 7, p. 316) and `02-geometric-grouping` (Lemma 3, p. 314; ALGORITHM 2, Step 4, p. 316). It is reviewed once for both.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 314, Lemma 3 ("inserts the small pieces, starting a new bin only when necessary"); p. 316, ALGORITHM 1, Step 7; p. 316, ALGORITHM 2, Step 4

import Mathlib

namespace KKBinPacking.Shared

/-- Insertion of pieces "using a new bin only when necessary" (Lemma 3, p. 314; ALGORITHM 1,
Step 7, and ALGORITHM 2, Step 4, p. 316). `AnyFit P S Q` means: starting from the bins `P` and inserting the pieces of
`S` one at a time, in any order, each piece into any existing bin where it fits, and into a
new bin only when it fits in no existing bin, can end with the bins `Q`. -/
inductive AnyFit : Multiset (Multiset ℝ) → Multiset ℝ → Multiset (Multiset ℝ) → Prop
  /-- Nothing left to insert. -/
  | done (P : Multiset (Multiset ℝ)) : AnyFit P 0 P
  /-- Insert a piece `p` of `S` into an existing bin `b` where it fits. -/
  | intoBin (P : Multiset (Multiset ℝ)) (S : Multiset ℝ) (Q : Multiset (Multiset ℝ))
      (p : ℝ) (b : Multiset ℝ) :
      p ∈ S → b ∈ P → b.sum + p ≤ 1 →
      AnyFit ((P.erase b) + {p ::ₘ b}) (S.erase p) Q → AnyFit P S Q
  /-- Open a new bin for a piece `p` of `S` that fits in no existing bin. -/
  | newBin (P : Multiset (Multiset ℝ)) (S : Multiset ℝ) (Q : Multiset (Multiset ℝ)) (p : ℝ) :
      p ∈ S → (∀ b ∈ P, 1 < b.sum + p) →
      AnyFit (P + {{p}}) (S.erase p) Q → AnyFit P S Q

end KKBinPacking.Shared


