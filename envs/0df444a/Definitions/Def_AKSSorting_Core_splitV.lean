-- Prove2me | Definitions.Def_AKSSorting_Core_splitV
-- name    : AKSSorting_Core_splitV
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:54:08.382405+00:00
-- url     : https://prove2.me/theorems/4f1f0c19-7182-4d4c-ba72-d169d29f9f03
-- title:
--   The splitting chains V(C, k) of Lemma 1
-- statement:
--   Let the registers $\mathcal R$ carry a fixed linear order, and call the least register of a nonempty set its **first element**. Let $C$ be a chain on level $i$ and $0\le j<i$. For $0\le k\le i$ define the function $V(C,k)$ on level $k$ as follows, for a node $t$ with $l(t)=k$:
--
--   1. if $k<j$: $V(C,k)(t)=\emptyset$;
--   2. if $k=j$: $V(C,j)(t)$ consists of the first element of $C(t_0)$ and the first element of $C(t_1)$, where $t_0=\langle t,0,\dots,0\rangle$ and $t_1=\langle t,1,0,\dots,0\rangle$ have length $i$;
--   3. if $j<k<i$: $V(C,k)(t)$ consists of the first element of $C(\langle t,1,0,\dots,0\rangle)$ (length $i$);
--   4. if $k=i$:
--   $$ V(C,i)(t)=C(t)\setminus\bigcup\{\,\cup V(C,k)\ :\ j\le k<i\,\}. $$
--
--   Thus one register of every leaf set is moved up to an ancestor on a level between $j$ and $i-1$, two of them to each node of level $j$, and the rest stay on level $i$. This splitting is used in the definition of the AKS algorithm.
--
--   **Formalization Note** Level $k$ is `Fin (2^k)` as in the chain definition; $\langle t,0,\dots,0\rangle$ is $t\cdot 2^{i-k}$ and $\langle t,1,0,\dots,0\rangle$ is $t\cdot 2^{i-k}+2^{i-k-1}$. "First element" is `Finset.min'` for the linear order on the register type, returned as a singleton (empty for an empty set). The paper's first sentence says "for all $k$, $0\le k<i$", then defines $V(C,i)$ as well; the definition covers $0\le k\le i$, and returns $\emptyset$ for $k>i$, which the lemma never uses.
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), pp. 3-4, Lemma 1

import Mathlib
import Definitions.Def_AKSSorting_Core_IsChain

namespace AKSSorting.Core

variable {R : Type} [LinearOrder R]

/-- The "first element" of a set of registers, as a set: `{min s}` for the fixed linear order on
the registers ℛ (p. 3: "we will suppose that the set ℛ is ordered in an arbitrary but fixed
way"), and `∅` when `s` is empty. -/
def firstElem (s : Finset R) : Finset R :=
  if h : s.Nonempty then {s.min' h} else ∅

theorem zeroExt_lt {i k : ℕ} (hk : k ≤ i) (t : Fin (2 ^ k)) : t.val * 2 ^ (i - k) < 2 ^ i := by
  have h1 : t.val * 2 ^ (i - k) < 2 ^ k * 2 ^ (i - k) :=
    Nat.mul_lt_mul_of_pos_right t.isLt (Nat.two_pow_pos _)
  rwa [← pow_add, Nat.add_sub_cancel' hk] at h1

theorem oneZeroExt_lt {i k : ℕ} (hk : k < i) (t : Fin (2 ^ k)) :
    t.val * 2 ^ (i - k) + 2 ^ (i - k - 1) < 2 ^ i := by
  obtain ⟨m, hm⟩ : ∃ m, i - k = m + 1 := ⟨i - k - 1, by omega⟩
  have hi : 2 ^ i = 2 ^ k * 2 ^ (m + 1) := by rw [← pow_add]; congr 1; omega
  rw [hm, Nat.add_sub_cancel, hi, pow_succ]
  have ht : t.val + 1 ≤ 2 ^ k := t.isLt
  have hp : 0 < 2 ^ m := Nat.two_pow_pos m
  nlinarith

/-- The level-`i` node `⟨t, 0, …, 0⟩` below the level-`k` node `t` (`k ≤ i`). -/
def zeroExt {i k : ℕ} (hk : k ≤ i) (t : Fin (2 ^ k)) : Fin (2 ^ i) :=
  ⟨t.val * 2 ^ (i - k), zeroExt_lt hk t⟩

/-- The level-`i` node `⟨t, 1, 0, …, 0⟩` below the level-`k` node `t` (`k < i`). -/
def oneZeroExt {i k : ℕ} (hk : k < i) (t : Fin (2 ^ k)) : Fin (2 ^ i) :=
  ⟨t.val * 2 ^ (i - k) + 2 ^ (i - k - 1), oneZeroExt_lt hk t⟩

/-- `V(C, k)` for `k < i` (Lemma 1, p. 4): for `l(t) = k`,
* `k < j`: `V(C, k)(t) = ∅`;
* `k = j`: the first element of `C(⟨t,0,…,0⟩)` together with the first element of
  `C(⟨t,1,0,…,0⟩)`;
* `j < k < i`: the first element of `C(⟨t,1,0,…,0⟩)`. -/
def splitVLow {i : ℕ} (C : Fin (2 ^ i) → Finset R) (j k : ℕ) (t : Fin (2 ^ k)) : Finset R :=
  if hk : k < i then
    if k < j then ∅
    else if k = j then firstElem (C (zeroExt hk.le t)) ∪ firstElem (C (oneZeroExt hk t))
    else firstElem (C (oneZeroExt hk t))
  else ∅

/-- The chains `V(C, k)`, `0 ≤ k ≤ i`, of Lemma 1 (Ajtai–Komlós–Szemerédi 1983, p. 4), for a
chain `C` on level `i` and a level `j`. For `k < i` it is `splitVLow`; for `k = i`,
`V(C, i)(t) = C(t) − ⋃{∪V(C, k) | j ≤ k < i}`. (For `k > i`, outside the lemma's range, the
value is `∅`.) -/
def splitV {i : ℕ} (C : Fin (2 ^ i) → Finset R) (j k : ℕ) (t : Fin (2 ^ k)) : Finset R :=
  if k < i then splitVLow C j k t
  else if h : k = i then
    C (Fin.cast (by rw [h]) t) \ (Finset.Ico j i).biUnion fun k' => chainUnion (splitVLow C j k')
  else ∅

end AKSSorting.Core


