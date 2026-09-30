-- Prove2me | Definitions.Def_KKBinPacking_LinearGrouping_Algorithm1
-- name    : KKBinPacking_LinearGrouping_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:18:38.466451+00:00
-- url     : https://prove2.me/theorems/f42408ee-2aa4-4102-8492-d7804039e4f7
-- title:
--   ALGORITHM 1 as a relation on runs
-- statement:
--   ALGORITHM 1 takes an instance $I$ and a real $\varepsilon > 0$ and proceeds as follows.
--
--   1. Discard all pieces of size $\le \max(1/n, \varepsilon/2)$, where $n = n(I)$; call the rest $J$.
--   2. Apply linear grouping to $J$ with $k = \lceil n(J)\varepsilon^2\rceil$; call the outputs $K$ (the rounded groups $G_2', \dots, G_q'$) and $K'$ (the first group $G_1$).
--   3. Put each piece of $K'$ into a bin of its own.
--   4. Apply the Fractional Bin-Packing subroutine to $K$ with tolerance $h = 1$: it returns a basic feasible solution $x$ of the linear program of $K$ with $\mathbf 1\cdot x \le LIN(K) + 1$.
--   5. Construct from $x$ a packing of $K$ with at most $\mathbf 1\cdot x + (m(K)+1)/2$ bins.
--   6. By reducing piece sizes, turn the packing of $K$ together with the bins of Step 3 into a packing of $J$.
--   7. Insert the pieces discarded in Step 1, using a new bin only when necessary.
--
--   A **trace** of ALGORITHM 1 records the objects $x$, the packing of $K$, the packing of $J$, and the final packing $P$ that one run produces, together with the properties the text requires of each. $\mathrm{Alg1Run}(\varepsilon, I, P)$ holds when some trace ends with $P$.
--
--   **Formalization Note** The text leaves several choices open, and the relation quantifies over all of them: the subroutine's output is any basic feasible solution of cost at most $LIN(K) + 1$ (the contract stated in §5, p. 315; the ellipsoid method of §6 is not modelled); Step 5 yields any packing of $K$ within the stated bound (the rounding of Corollary 1 is one of them); Step 6 yields any packing of $J$ matched bin by bin to the bins of Step 5 and Step 3 with every piece no larger than its counterpart (`Multiset.Rel`); Step 7 is any any-fit insertion. In Step 1, $1/n$ with $n = 0$ is $0$ in Lean, which only concerns the empty instance. The names $K$, $K'$ are the paper's; linear grouping's own outputs are called $J$, $J'$ on p. 314. Running time is not modelled.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, pp. 315–316, §5, the Fractional Bin-Packing subroutine contract and ALGORITHM 1 (Steps 1–7)

import Mathlib
import Definitions.Def_KKBinPacking_LinearGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_LinearGrouping_LinGroup
open KKBinPacking.Shared

namespace KKBinPacking.LinearGrouping

/-- The discard threshold `max(1/n, ε/2)` of ALGORITHM 1, Step 1 (p. 315), with `n = n(I)`. -/
noncomputable def alg1Threshold (ε : ℝ) (I : Multiset ℝ) : ℝ :=
  max (1 / (numPieces I : ℝ)) (ε / 2)

/-- Step 1: the instance `J` of the pieces of size `> max(1/n, ε/2)`. -/
noncomputable def alg1J (ε : ℝ) (I : Multiset ℝ) : Multiset ℝ :=
  I.filter (fun x => alg1Threshold ε I < x)

/-- Step 1: the discarded pieces, of size `≤ max(1/n, ε/2)`; reinserted at Step 7. -/
noncomputable def alg1Discarded (ε : ℝ) (I : Multiset ℝ) : Multiset ℝ :=
  I.filter (fun x => x ≤ alg1Threshold ε I)

/-- Step 2: the grouping parameter `k = ⌈n(J) ε²⌉`. -/
noncomputable def alg1k (ε : ℝ) (I : Multiset ℝ) : ℕ :=
  ⌈(numPieces (alg1J ε I) : ℝ) * ε ^ 2⌉₊

/-- Step 2: `K`, the rounded groups after the first, from linear grouping of `J` with `k`. -/
noncomputable def alg1K (ε : ℝ) (I : Multiset ℝ) : Multiset ℝ :=
  (linGroup (alg1k ε I) (alg1J ε I)).1

/-- Step 2: `K'`, the first group (the `k` largest pieces of `J`). -/
noncomputable def alg1K' (ε : ℝ) (I : Multiset ℝ) : Multiset ℝ :=
  (linGroup (alg1k ε I) (alg1J ε I)).2

/-- One possible run of ALGORITHM 1 (pp. 315–316) on `I` with parameter `ε`, recording every
choice the text leaves open.
* `x` (Step 4): any basic feasible solution of the LP of `K` of cost `≤ LIN(K) + 1`, the
  contract of the Fractional Bin-Packing subroutine with tolerance `h = 1`.
* `PK` (Step 5): any packing of `K` with at most `1·x + (m(K)+1)/2` bins.
* `PJ` (Step 6): a packing of `J` obtained from the bins of `PK` together with one bin per piece
  of `K'` (Step 3) by reducing piece sizes, bin by bin.
* `P` (Step 7): the result of inserting the pieces discarded at Step 1 into `PJ`, using a new bin
  only when necessary. -/
structure Alg1Trace (ε : ℝ) (I : Multiset ℝ) where
  x : Multiset ℝ →₀ ℝ
  PK : Multiset (Multiset ℝ)
  PJ : Multiset (Multiset ℝ)
  P : Multiset (Multiset ℝ)
  x_basic : IsBasicFeasible (alg1K ε I) x
  x_cost : lpCost x ≤ LIN (alg1K ε I) + 1
  PK_packing : IsPacking (alg1K ε I) PK
  PK_card : (Multiset.card PK : ℝ) ≤ lpCost x + ((numSizes (alg1K ε I) : ℝ) + 1) / 2
  PJ_join : PJ.join = alg1J ε I
  PJ_reduce : Multiset.Rel (fun b b' => Multiset.Rel (· ≤ ·) b b') PJ
    (PK + (alg1K' ε I).map (fun p => ({p} : Multiset ℝ)))
  P_insert : AnyFit PJ (alg1Discarded ε I) P

/-- `Alg1Run ε I P`: ALGORITHM 1 with parameter `ε` may output the packing `P` on `I`. -/
def Alg1Run (ε : ℝ) (I : Multiset ℝ) (P : Multiset (Multiset ℝ)) : Prop :=
  ∃ tr : Alg1Trace ε I, tr.P = P

end KKBinPacking.LinearGrouping


