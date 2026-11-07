-- Prove2me | Definitions.Def_AKSZigZag_RegisterAssignment
-- name    : AKSZigZag_RegisterAssignment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:17:57.339976+00:00
-- url     : https://prove2.me/theorems/5eaf85dc-02a2-43a8-b6a1-ef8bcc14bec6
-- title:
--   Register assignment to the tree: $X_t$, $Y_t$, node intervals, cherries, partitions $P_{t1},P_{t2}$
-- statement:
--   Fix a parameter $A$, with $n$ and $A$ powers of $2$. For $t=1,\dots,\log_2 n$ and $i=1,\dots,t$ set
--   $$
--   X_t(i)=\lfloor c\,n\,2^{-t}A^{\,i-t}\rfloor,\qquad Y_t(i)=\sum_{j=1}^{i}X_t(j),\qquad c=\frac1{2A},
--   $$
--   with $Y_t(i)=0$ for $i\le0$.
--
--   At time $t$ the registers sit on the nodes of a binary tree of depth $t$. Node $j$ of level $i$ ($1\le j\le2^i$) owns the block of $s=n2^{-i}$ registers starting after $(j-1)s$. Within that block (offset by $(j-1)s$) it holds the following intervals:
--   1. for $0\le i\le t-1$ and $j$ odd: $[Y_t(i)+1,\,Y_t(i+1)]$ and $[s-Y_t(i+1)+1,\,s]$;
--   2. for $0\le i\le t-1$ and $j$ even: $[1,\,Y_t(i+1)]$ and $[s-Y_t(i+1)+1,\,s-Y_t(i)]$;
--   3. on level $t$: the single interval $[Y_t(t)+1,\,s]$ for $j$ odd, and $[1,\,s-Y_t(t)]$ for $j$ even.
--
--   At $t=0$ the root holds all of $[1,n]$.
--
--   A **cherry** is the set of registers of a node and its two children; the children of a level-$t$ node hold nothing. The partition **$P_{t1}$** consists of the cherries whose parent lies on an even level. The partition **$P_{t2}$** consists of the cherries whose parent lies on an odd level, together with the registers of the root as a part of their own.
--
--   The **distance** of two nodes is the length of the tree path between them; it is $0$ for the same node. The module also lists the nonempty intervals at time $t$, each tagged with its node; these are the intervals of §8.
--
--   **Formalization Note** Registers are `Fin n` (register $r$ is the paper's $r+1$), and interval endpoints are computed in $\mathbb Z$, so no truncated subtraction occurs. $X_t(i)$ is the natural-number quotient $nA^i/(2A^{t+1}2^t)$, which equals the floor; a verification file proves this. The partitions follow §6's tree description. The explicit formulas of §7 are not used: as printed, $T_t(-1)=[1,Y_t(0)]\cup[n-Y_t(0)+1,n]$ is empty because $Y_t(0)=0$, and the index ranges there omit the level-$t$ nodes.
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §5, pp.5–6 (X_t, Y_t, intervals J1, J2, J), §6, p.6 (cherries, P_t1, P_t2), §8, p.7 (intervals, distance on the tree)

import Mathlib

namespace AKSZigZag

/-- `X_t(i) = ⌊c n 2^{-t} A^{i-t}⌋` with `c = 1/(2A)` (AKS, STOC 1983, §5, p.5), for
`1 ≤ i ≤ t`; `0` otherwise.

**Formalization Note.** `c n 2^{-t} A^{i-t} = n A^i / (2 A^{t+1} 2^t)` is a nonnegative rational,
so its floor is the natural-number quotient used here (for `A ≥ 1`). -/
def X (A n t i : ℕ) : ℕ :=
  if 1 ≤ i ∧ i ≤ t then n * A ^ i / (2 * A ^ (t + 1) * 2 ^ t) else 0

/-- `Y_t(i) = Σ_{j=1}^{i} X_t(j)`, and `Y_t(i) = 0` for `i ≤ 0` (AKS, STOC 1983, §5, p.5). -/
def Y (A n t i : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 i, X A n t j

/-- The interval `[a, b]` of the paper's 1-based registers, as a set of 0-based registers
`Fin n` (register `r` is the paper's `r + 1`); empty when `b < a`. -/
def seg (n : ℕ) (a b : ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun r : Fin n => a ≤ (r.val : ℤ) + 1 ∧ (r.val : ℤ) + 1 ≤ b

/-- **The intervals of the node `(i, j)` at time `t`** (AKS, STOC 1983, §5, pp.5–6), `j`
1-based, `1 ≤ j ≤ 2^i`, with `s = n2^{-i}` and base `(j-1)s`:
* level `0 ≤ i ≤ t-1`, `j` odd: `J1 = base + [Y_t(i)+1, Y_t(i+1)]`, `J2 = base + [s-Y_t(i+1)+1, s]`;
* level `0 ≤ i ≤ t-1`, `j` even: `J1 = base + [1, Y_t(i+1)]`, `J2 = base + [s-Y_t(i+1)+1, s-Y_t(i)]`;
* level `t`, `j` odd: `J = base + [Y_t(t)+1, s]`; `j` even: `J = base + [1, s-Y_t(t)]`;
* no intervals for other `(i, j)` (in particular for level `t+1`).

At `t = 0` this gives the single interval `[1, n]` on the root.

**Formalization Note.** Endpoints are computed in `ℤ`, so no truncated subtraction occurs; an
interval with `b < a` is empty. `n` is a power of 2 in every use, so `n / 2^i` is exact. -/
def nodePieces (A n t i j : ℕ) : List (Finset (Fin n)) :=
  let s : ℤ := ((n / 2 ^ i : ℕ) : ℤ)
  let base : ℤ := ((j : ℤ) - 1) * s
  let Yi : ℤ := (Y A n t i : ℤ)
  let Yi1 : ℤ := (Y A n t (i + 1) : ℤ)
  if 1 ≤ j ∧ j ≤ 2 ^ i then
    if i < t then
      if j % 2 = 1 then [seg n (base + Yi + 1) (base + Yi1), seg n (base + s - Yi1 + 1) (base + s)]
      else [seg n (base + 1) (base + Yi1), seg n (base + s - Yi1 + 1) (base + s - Yi)]
    else if i = t then
      if j % 2 = 1 then [seg n (base + Yi + 1) (base + s)] else [seg n (base + 1) (base + s - Yi)]
    else []
  else []

/-- The registers assigned to the node `(i, j)` at time `t` (the union of its intervals). -/
def nodeRegs (A n t i j : ℕ) : Finset (Fin n) :=
  (nodePieces A n t i j).foldr (· ∪ ·) ∅

/-- The nodes of the tree at time `t`: `(i, j)` with `0 ≤ i ≤ t`, `1 ≤ j ≤ 2^i`. -/
def nodes (t : ℕ) : List (ℕ × ℕ) :=
  (List.range (t + 1)).flatMap fun i => (List.range (2 ^ i)).map fun j => (i, j + 1)

/-- **The intervals at time `t`** (AKS, STOC 1983, §8, p.7: "The name 'interval' and the letters
J,K will stand for any one of the intervals defined in Section 5"), each tagged with the node
`(level, index)` holding it. Empty intervals are dropped. -/
def intervals (A n t : ℕ) : List (ℕ × ℕ × Finset (Fin n)) :=
  (nodes t).flatMap fun ij =>
    ((nodePieces A n t ij.1 ij.2).filter fun J => J.Nonempty).map fun J => (ij.1, ij.2, J)

/-- **Cherry** (AKS, STOC 1983, §6, p.6): "the set of registers assigned to a node and its two
(possibly empty) children-nodes". The children of `(i, j)` are `(i+1, 2j-1)` and `(i+1, 2j)`
(the two halves of its block); at level `t` they hold no registers. -/
def cherry (A n t i j : ℕ) : Finset (Fin n) :=
  nodeRegs A n t i j ∪ nodeRegs A n t (i + 1) (2 * j - 1) ∪ nodeRegs A n t (i + 1) (2 * j)

/-- **The partition `P_t1`** (AKS, STOC 1983, §6, p.6): the cherries whose parent node is on an
even level `0, 2, 4, … ≤ t`. -/
def partition1 (A n t : ℕ) : List (Finset (Fin n)) :=
  ((List.range (t + 1)).filter fun i => i % 2 = 0).flatMap fun i =>
    (List.range (2 ^ i)).map fun j => cherry A n t i (j + 1)

/-- **The partition `P_t2`** (AKS, STOC 1983, §6, p.6): the cherries whose parent node is on an
odd level `1, 3, … ≤ t`, together with the registers of the root, which "has no parent, form a
part themselves".

**Formalization Note.** The partitions follow §6's tree description, not the explicit formulas
of §7: as printed, §7's `T_t(-1) = [1, Y_t(0)] ∪ [n-Y_t(0)+1, n]` is empty (`Y_t(0) = 0`) and its
index ranges omit the level-`t` nodes. -/
def partition2 (A n t : ℕ) : List (Finset (Fin n)) :=
  nodeRegs A n t 0 1 ::
    ((List.range (t + 1)).filter fun i => i % 2 = 1).flatMap fun i =>
      (List.range (2 ^ i)).map fun j => cherry A n t i (j + 1)

/-- The index (0-based) of the ancestor at level `l ≤ i` of the node `(i, j)` (`j` 1-based). -/
def ancestorIdx (i j l : ℕ) : ℕ := (j - 1) / 2 ^ (i - l)

/-- The level of the lowest common ancestor of the nodes `(i, j)` and `(i', j')`. -/
def lcaLevel (i j i' j' : ℕ) : ℕ :=
  Nat.findGreatest (fun l => ancestorIdx i j l = ancestorIdx i' j' l) (min i i')

/-- **Distance on the tree** between the nodes `(i, j)` and `(i', j')` (AKS, STOC 1983, §8, p.7):
the length of the path through their lowest common ancestor; `0` for the same node. -/
def treeDist (i j i' j' : ℕ) : ℕ := i + i' - 2 * lcaLevel i j i' j'

end AKSZigZag


