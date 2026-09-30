-- Prove2me | Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
-- name    : KKBinPacking_GeometricGrouping_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T17:09:09.98792+00:00
-- url     : https://prove2.me/theorems/4945db3f-2288-4a16-bffa-fbeda86922be
-- title:
--   ALGORITHM 2 as a relation between an input instance and the packings it may output
-- statement:
--   ALGORITHM 2 takes an instance $I$, a positive integer $k$ and a positive real $g$:
--
--   1. Eliminate all pieces of size $\le g$; call the remaining instance $I_1$.
--   2. While $SIZE$ of the current instance exceeds $1 + \frac{1}{1-1/k}\ln\frac1g$: perform geometric grouping with parameter $k$ on the current instance, giving $J$ and $J'$; pack $J'$ in at most $2k\,[2 + \ln\frac1g]$ bins; let $x$ be a basic feasible solution of the linear program of $J$ of cost at most $LIN(J)+1$; for each configuration $j$ with $x_j \ge 1$ create $\lfloor x_j\rfloor$ bins with configuration $j$, and delete the pieces so packed.
--   3. Pack the remaining pieces in at most $2 + \frac{2}{1-1/k}\ln\frac1g$ bins.
--   4. Insert the pieces eliminated at Step 1, using a new bin only when necessary.
--
--   A **trace** of the algorithm records the number $t$ of executions of the loop body, the instance at the start of each execution, and every choice the text leaves open. $\mathrm{Alg2Run}(k, g, I, P)$ holds when some trace outputs the packing $P$. The analysis quantities are $X_i = \sum_{x_j \ge 1}\lfloor x_j\rfloor$, the number of bins created from the solution $x$ of the $i$-th execution, and $Y_i$, the number of bins used for $J'_i$.
--
--   **Formalization Note** Executions of the loop body are numbered $0, \dots, t-1$; `inst i` is the paper's $I_{i+1}$, and `inst 0` is the instance after Step 1 (the paper's "$I_1 = I$" refers to that instance). The trace quantifies over: any packing of $J'_i$ within the stated bin count; any basic feasible solution with cost at most $LIN(J_i)+1$ (the contract of the Fractional Bin-Packing subroutine with $h=1$, p. 315; the ellipsoid method of §6 is not modelled); which real pieces fill the principal bins; any Step 3 packing within its bin count; any run of the Step 4 insertion. "Delete the pieces so packed": each principal bin holds real pieces of $J_i$ whose rounded sizes fit inside its configuration, the bins are matched one to one with the $\lfloor x_j\rfloor$ copies of each configuration $j$, and every available slot is filled (for each size $s$, the number of placed pieces of rounded size $s$ is the minimum of the number of such pieces in $J_i$ and the number of slots of size $s$). The next instance consists of the real pieces of $J_i$ that were not placed ($J'_i$ has been packed separately). The paper's "For each $k$ such that $x_j \ge 1$" is read as "for each $j$". A trace has a finite $t$ by definition; that a trace exists is a separate statement of this mission.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 316, §5, ALGORITHM 2 (left column bottom, right column top) and "Analysis of ALGORITHM 2" (definitions of t, I_i, J_i, J'_i, X_i, Y_i); p. 315, §5, contract of the Fractional Bin-Packing procedure

import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping

/-- The threshold `1 + (1/(1 − 1/k)) ln(1/g)` of the while loop of ALGORITHM 2, Step 2
(p. 316). Only used with `k ≥ 2` and `0 < g`. -/
noncomputable def alg2Threshold (k : ℕ) (g : ℝ) : ℝ :=
  1 + (1 / (1 - 1 / (k : ℝ))) * Real.log (1 / g)

/-- The principal bins prescribed by a solution `x` (ALGORITHM 2, Step 2, p. 316): for each
configuration `c` with `x_c ≥ 1`, `⌊x_c⌋` copies of `c` (for `x_c < 1` the floor is `0`). -/
noncomputable def principalConfigs (x : Multiset ℝ →₀ ℝ) : Multiset (Multiset ℝ) :=
  ∑ c ∈ x.support, Multiset.replicate ⌊x c⌋₊ c

/-- `X`, the number of principal bins created from `x`: `∑_{x_j ≥ 1} ⌊x_j⌋`. -/
noncomputable def principalCount (x : Multiset ℝ →₀ ℝ) : ℕ :=
  ∑ c ∈ x.support, ⌊x c⌋₊

/-- The packing held after Step 3 of ALGORITHM 2: for every executed iteration `i < t`, its
principal bins (their real pieces) and its packing of `J'_i`, together with the Step 3
packing `P3` of the remaining pieces. -/
def alg2Step3Bins (t : ℕ) (Bp : ℕ → Multiset (Multiset (ℝ × ℝ)))
    (PJ' : ℕ → Multiset (Multiset ℝ)) (P3 : Multiset (Multiset ℝ)) : Multiset (Multiset ℝ) :=
  (∑ i ∈ Finset.range t, ((Bp i).map (Multiset.map Prod.fst) + PJ' i)) + P3

/-- One possible run of ALGORITHM 2 (p. 316) with parameters `k` (a positive integer) and `g`
(a positive real) on the input instance `I`, recording every choice the text leaves open.
Iterations of the while loop are numbered `0, …, t − 1` (the paper's `1, …, t`).
* `inst i` is the instance at the beginning of iteration `i` (the paper's `I_{i+1}`);
  `inst 0` is `I` after Step 1 (all pieces of size `≤ g` eliminated), and `inst t` is what
  remains when the loop exits.
* In iteration `i`, geometric grouping with parameter `k` turns `inst i` into `J_i` (the
  rounded pieces, as the pairs `geomPairs k (inst i)` of real piece and rounded size) and
  `J'_i`. `PJ' i` is any packing of `J'_i` with at most `2k[2 + ln(1/g)]` bins.
* `x i` is any basic feasible solution of the LP of `J_i` of cost `≤ LIN(J_i) + 1`: the
  contract of the Fractional Bin-Packing subroutine with tolerance `h = 1` (p. 315).
* `Bp i` are the principal bins: they are matched one to one with the `⌊x_j⌋` copies of each
  configuration `j`, each bin holds real pieces of `J_i`'s pairs whose rounded sizes fit
  inside its configuration, and every available slot is filled: for each size `s`, the number
  of placed pieces of rounded size `s` is the minimum of the number of such pieces in `J_i`
  and the number of slots of type `s`. The pieces so packed are deleted, and
  `inst (i+1)` consists of the real pieces of `J_i` not placed (`J'_i` is removed too).
* `P3` is any packing of `inst t` with at most `2 + (2/(1 − 1/k)) ln(1/g)` bins (Step 3).
* `P` results from inserting the pieces eliminated at Step 1 into all bins produced so far,
  using a new bin only when necessary (Step 4). -/
structure Alg2Trace (k : ℕ) (g : ℝ) (I : Multiset ℝ) where
  t : ℕ
  inst : ℕ → Multiset ℝ
  PJ' : ℕ → Multiset (Multiset ℝ)
  x : ℕ → (Multiset ℝ →₀ ℝ)
  Bp : ℕ → Multiset (Multiset (ℝ × ℝ))
  P3 : Multiset (Multiset ℝ)
  P : Multiset (Multiset ℝ)
  inst_zero : inst 0 = I.filter (fun p => g < p)
  loop_run : ∀ i < t, alg2Threshold k g < SIZE (inst i)
  loop_exit : SIZE (inst t) ≤ alg2Threshold k g
  PJ'_packing : ∀ i < t, IsPacking (geomJ' k (inst i)) (PJ' i)
  PJ'_card : ∀ i < t, (Multiset.card (PJ' i) : ℝ) ≤ 2 * (k : ℝ) * (2 + Real.log (1 / g))
  x_basic : ∀ i < t, IsBasicFeasible (geomJ k (inst i)) (x i)
  x_cost : ∀ i < t, lpCost (x i) ≤ LIN (geomJ k (inst i)) + 1
  Bp_sub : ∀ i < t, (Bp i).join ≤ geomPairs k (inst i)
  Bp_config : ∀ i < t,
    Multiset.Rel (fun (b : Multiset (ℝ × ℝ)) (c : Multiset ℝ) => b.map Prod.snd ≤ c)
      (Bp i) (principalConfigs (x i))
  Bp_max : ∀ i < t, ∀ s : ℝ,
    ((Bp i).join.map Prod.snd).count s =
      min ((geomJ k (inst i)).count s) ((principalConfigs (x i)).join.count s)
  inst_succ : ∀ i < t, inst (i + 1) = (geomPairs k (inst i) - (Bp i).join).map Prod.fst
  P3_packing : IsPacking (inst t) P3
  P3_card : (Multiset.card P3 : ℝ) ≤ 2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g)
  P_insert : AnyFit (alg2Step3Bins t Bp PJ' P3) (I.filter (fun p => p ≤ g)) P

/-- `Alg2Run k g I P`: ALGORITHM 2 with parameters `k` and `g` may output the packing `P` on
the input instance `I`. -/
def Alg2Run (k : ℕ) (g : ℝ) (I : Multiset ℝ) (P : Multiset (Multiset ℝ)) : Prop :=
  ∃ tr : Alg2Trace k g I, tr.P = P

end KKBinPacking.GeometricGrouping


