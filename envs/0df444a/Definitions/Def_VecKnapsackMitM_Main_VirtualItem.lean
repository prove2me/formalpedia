-- Prove2me | Definitions.Def_VecKnapsackMitM_Main_VirtualItem
-- name    : VecKnapsackMitM_Main_VirtualItem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:33:34.471184+00:00
-- url     : https://prove2.me/theorems/991d4fa0-b940-484d-a24b-98bfcafdafbc
-- title:
--   Virtual items as pointer records in memory (§4.1)
-- statement:
--   Virtual items, implemented as in §4.1: a record at an address $a\ge1$ with $R[a]=v.p$, $R[a+1+t]=v.\bar w_{t+1}$ ($t<d$), $N[a]=v.\mathrm{item}$ ($0$ for $\emptyset$, $i+1$ for $\{i\}$), and $N[a+1]$, $N[a+2]$ the pointers $v.\mathrm{left}$, $v.\mathrm{right}$ ($0$ is NULL).
--
--   * `walk s fuel a`: depth-first traversal of the pointer structure from $a$, returning the item codes met and the visited addresses, or `none` when the fuel runs out (in particular on a pointer cycle) or address $0$ is visited as a record.
--   * `IsVItem I s a S`: with fuel $2n+1$ the traversal succeeds, each distinct reachable record contributes its item once, those items are distinct valid items of $I$ forming exactly $S$, and the number of distinct reachable records is $\max\{2|S|-1,1\}$. `VItemRoot` checks these invariants and the cached profit and weights at one root; `IsVItem` requires them also at every reachable record, whose children are themselves virtual items. Then $p(v)$, $\bar w(v)$ read off the record are those of $\mathrm{set}(v)=S$.
--   * `NodesWithin s n d a lo F`: every record reached from $a$ lies in the address window $[lo,F)$.
--   * `listAt s b`: the list stored at $b$, i.e. $N[b+1],\dots,N[b+N[b]]$; outputs "sets of virtual items" are such lists, and a list's length bounds the size of the set.
--
--   A fresh all-zero record at an address $a\ge1$ is a valid $v_\emptyset$.
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; §4.1, printed pp. 13–15 (PDF 14–16)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecKnapsackMitM_Main_Instance

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-! Virtual items in memory (Bringmann, Kulik, Węgrzycki 2026, §4.1, "Implementation", printed
pp. 14–15, PDF 15–16). A virtual item is a record at an address `a ≥ 1` of the real RAM:
* `R[a]` is `v.p`, and `R[a + 1 + t]` is `v.w̄_{t+1}` for `t < d`;
* `N[a]` is `v.item`: `0` for `∅`, `i + 1` for the item `{i}`;
* `N[a + 1]`, `N[a + 2]` are `v.left`, `v.right`: `0` is `NULL`, otherwise an address.
Lists are stored as `N[b] = m` (length) followed by the `m` addresses `N[b + 1], …, N[b + m]`. -/

/-- Depth-first traversal of the pointer structure from address `a` with `fuel` levels: the
item codes met (`N[u] - 1` for every visited `u` with `N[u] ≠ 0`) and the visited addresses, in
traversal order; `none` if the fuel runs out (in particular on a pointer cycle) or the null
address `0` is visited as a record. -/
def walk (s : State) : ℕ → ℕ → Option (List ℕ × List ℕ)
  | 0, _ => none
  | f + 1, a =>
    if a = 0 then none else
    let own : List ℕ := if s.N a = 0 then [] else [s.N a - 1]
    let sl : Option (List ℕ × List ℕ) :=
      if s.N (a + 1) = 0 then some ([], []) else walk s f (s.N (a + 1))
    let sr : Option (List ℕ × List ℕ) :=
      if s.N (a + 2) = 0 then some ([], []) else walk s f (s.N (a + 2))
    match sl, sr with
    | some (c₁, m₁), some (c₂, m₂) => some (own ++ c₁ ++ c₂, a :: (m₁ ++ m₂))
    | _, _ => none

/-- The invariants at one root, using the *set* of reachable records as on PDF 15.
The traversal may revisit an address; each reachable record contributes its item once.
Every stored summary at this root agrees with its represented set. -/
def VItemRoot {d n : ℕ} (I : Items d n) (s : State) (a : ℕ)
    (S : Finset (Fin n)) : Prop :=
  ∃ visits nodes : List ℕ, walk s (2 * n + 1) a = some (visits, nodes) ∧
    let reachable := nodes.toFinset
    let codes := reachable.toList.filterMap fun u => if s.N u = 0 then none else some (s.N u - 1)
    codes.Nodup ∧ (∀ c ∈ codes, c < n) ∧ (∀ i : Fin n, i ∈ S ↔ i.val ∈ codes) ∧
    reachable.card = max (2 * S.card - 1) 1 ∧
    s.R a = I.profit S ∧ ∀ t : Fin d, s.R (a + 1 + t) = I.weight S t

/-- A virtual item has the §4.1 invariants at its root and at every reachable record:
its children are themselves virtual items, including correct cached profits and weights.
Fuel `2n+1` excludes cycles and covers every acyclic structure with at most `max(2n-1,1)`
reachable records. -/
def IsVItem {d n : ℕ} (I : Items d n) (s : State) (a : ℕ) (S : Finset (Fin n)) : Prop :=
  VItemRoot I s a S ∧
  ∀ visits nodes, walk s (2 * n + 1) a = some (visits, nodes) →
    ∀ u ∈ nodes, ∃ T : Finset (Fin n), VItemRoot I s u T

/-- Every record reachable from `a` (with the traversal of `IsVItem`) lies in the address
window `[lo, F)`: it occupies cells `u, …, u + d + 2` with `lo ≤ u` and `u + d + 2 < F`. -/
def NodesWithin (s : State) (n d a lo F : ℕ) : Prop :=
  ∃ codes nodes : List ℕ, walk s (2 * n + 1) a = some (codes, nodes) ∧
    ∀ u ∈ nodes, lo ≤ u ∧ u + d + 3 ≤ F

/-- The list stored at address `b`: `N[b + 1], …, N[b + N[b]]`. -/
def listAt (s : State) (b : ℕ) : List ℕ :=
  (List.range (s.N b)).map fun j => s.N (b + 1 + j)

end VecKnapsackMitM.Main


