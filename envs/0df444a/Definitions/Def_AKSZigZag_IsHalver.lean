-- Prove2me | Definitions.Def_AKSZigZag_IsHalver
-- name    : AKSZigZag_IsHalver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:09.081506+00:00
-- url     : https://prove2.me/theorems/ad7b61db-4458-438d-ab70-5abdd7832afd
-- title:
--   $\varepsilon$-halved configurations and $\varepsilon$-halver networks
-- statement:
--   Let $m$ registers hold the elements $1,\dots,m$, one per register. The arrangement is **$\varepsilon$-halved** if:
--   1. for every $k\le\lfloor m/2\rfloor$, at most $\varepsilon k$ of the elements $1,\dots,k$ lie in the upper half $\{\lfloor m/2\rfloor+1,\dots,m\}$ of the registers;
--   2. for every $k>\lfloor m/2\rfloor$, at most $\varepsilon(m-k+1)$ of the elements $k,\dots,m$ lie in the lower half $\{1,\dots,\lfloor m/2\rfloor\}$.
--
--   So the two halves contain few wrong elements, and these are mostly the elements near the median. A comparator network on $m$ registers is an **$\varepsilon$-halver** if its output is $\varepsilon$-halved for every input permutation.
--
--   Halvers are the basic building block of the construction: recursive halving gives $\varepsilon$-nearsorts (§4), which drive the zig-zag algorithm.
--
--   **Formalization Note** A configuration is a function `y : Fin m → Fin m` from registers to contents, both numbered from $0$. The reading is value-centric: the counted objects are elements, located by the register holding them, as in the paper's proof on p.5 ("more than $\varepsilon k$ of the elements of $S=(1,\dots,k)$ end up in registers of $B$").
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §3, p.4 (definition of ε-halved and ε-halver)

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork

namespace AKSZigZag

open AKSSorting.Core

/-- **ε-halved** (AKS, STOC 1983, §3, p.4): "A permutation π = (π1,π2,...,πm) of (1,2,...,m) is
said to be ε-halved if for any initial segment S = (1,...,k), k ≤ ⌊m/2⌋, πi > ⌊m/2⌋ occurs for at
most ε|S| numbers i ∈ S, and for any endsegment S = (k,...,m), k > ⌊m/2⌋, πi ≤ ⌊m/2⌋ occurs for at
most ε|S| numbers i ∈ S."

The configuration is given as `y : Fin m → Fin m`, register ↦ content (a bijection in every
use). Counting registers is counting the elements they hold:
1. for every `k ≤ ⌊m/2⌋`, at most `εk` of the elements `0, …, k-1` (the paper's `1, …, k`) sit in
   registers `≥ ⌊m/2⌋` (the paper's upper half `⌊m/2⌋+1, …, m`);
2. for every `k` with `⌊m/2⌋ ≤ k < m`, at most `ε(m-k)` of the elements `k, …, m-1` (the paper's
   end segment `k+1, …, m`) sit in registers `< ⌊m/2⌋`.

**Formalization Note.** 0-based registers and contents. The reading is *value-centric*: `i`
ranges over elements and `πᵢ` is the register holding `i`, as the paper's proof uses it ("more
than εk of the elements of S = (1,...,k) end up in registers of B", §3, p.5). -/
def IsHalved {m : ℕ} (ε : ℝ) (y : Fin m → Fin m) : Prop :=
  (∀ k : ℕ, k ≤ m / 2 →
      (((Finset.univ.filter fun i : Fin m => m / 2 ≤ i.val ∧ (y i).val < k).card : ℕ) : ℝ)
        ≤ ε * k) ∧
    (∀ k : ℕ, m / 2 ≤ k → k < m →
      (((Finset.univ.filter fun i : Fin m => i.val < m / 2 ∧ k ≤ (y i).val).card : ℕ) : ℝ)
        ≤ ε * (m - k : ℕ))

/-- **ε-halver network** (AKS, STOC 1983, §3, p.4): "A procedure is called an ε-halver (of m
elements) if it accepts permutations of 1,...,m as inputs, and produces ε-halved permutations of
1,...,m as outputs." A comparator network on `Fin m` is an ε-halver when its output on every
permutation of the contents `Fin m` is ε-halved. -/
def IsHalver {m : ℕ} (ε : ℝ) (N : ComparatorNetwork m) : Prop :=
  ∀ x : Fin m → Fin m, Function.Bijective x → IsHalved ε (N.eval x)

end AKSZigZag


