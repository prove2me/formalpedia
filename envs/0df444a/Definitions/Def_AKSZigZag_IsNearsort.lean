-- Prove2me | Definitions.Def_AKSZigZag_IsNearsort
-- name    : AKSZigZag_IsNearsort
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:17.668359+00:00
-- url     : https://prove2.me/theorems/8f322061-5072-438c-ae66-21f1564a6eaa
-- title:
--   $\varepsilon$-nearsorted configurations and $\varepsilon$-nearsort networks
-- statement:
--   For a set $S$ of positions in $\{1,\dots,m\}$ and $\varepsilon>0$, the **blown-up set** is
--   $$
--   S^{\varepsilon}=\{\,j\in[m] : |j-i|\le\varepsilon m\ \text{for some } i\in S\,\}.
--   $$
--   Let $m$ registers hold the elements $1,\dots,m$. For a set $S$ of elements, $|S-\pi S^{\varepsilon}|$ is the number of elements of $S$ whose register lies outside $S^{\varepsilon}$. The arrangement is **$\varepsilon$-nearsorted** if
--   $$
--   |S-\pi S^{\varepsilon}|<\varepsilon|S|
--   $$
--   for every initial segment $S=\{1,\dots,k\}$ and every end segment $S=\{k,\dots,m\}$, $1\le k\le m$. A comparator network on $m$ registers is an **$\varepsilon$-nearsort** if its output is $\varepsilon$-nearsorted for every input permutation.
--
--   The relative bound for initial and end segments is what lets repeated nearsorts make the errors decay exponentially in the zig-zag algorithm.
--
--   **Formalization Note** Registers and contents are `Fin m`, numbered from $0$. The reading is value-centric, the same convention as for $\varepsilon$-halved. The paper's strict inequality is kept.
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §4, p.5 (blown-up set S^ε, ε-nearsorted, ε-nearsort)

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork

namespace AKSZigZag

open AKSSorting.Core

/-- The **blown-up set** `S^ε = {j ∈ [m] | |j-i| ≤ εm for some i ∈ S}` (AKS, STOC 1983, §4,
p.5), for `S ⊆ Fin m` (0-based; the shift does not change `|j - i|`). -/
noncomputable def blowUp {m : ℕ} (ε : ℝ) (S : Finset (Fin m)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j : Fin m => ∃ i ∈ S, |(j.val : ℝ) - i.val| ≤ ε * m

/-- The number `|S - πS^ε|` of elements of `S` whose register lies outside `S^ε`, for the
configuration `y : Fin m → Fin m` (register ↦ content). -/
noncomputable def strayCount {m : ℕ} (ε : ℝ) (y : Fin m → Fin m) (S : Finset (Fin m)) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : Fin m => y p ∈ S ∧ p ∉ blowUp ε S).card

/-- **ε-nearsorted** (AKS, STOC 1983, §4, p.5): "We say that a permutation π = (π1,...,πm) of
(1,...,m) is ε-nearsorted if (i) |S-πS^ε| < ε|S| holds for all initial segments S = (1,...,k)
and endsegments S = (k,...,m), (1 ≤ k ≤ m)."

For the configuration `y` (register ↦ content), `|S - πS^ε|` is the number of elements of `S`
held by registers outside `S^ε`:
1. for every `1 ≤ k ≤ m`, fewer than `εk` of the elements `0, …, k-1` lie outside
   `{0, …, k-1}^ε`;
2. for every `0 ≤ k < m`, fewer than `ε(m-k)` of the elements `k, …, m-1` lie outside
   `{k, …, m-1}^ε`.

**Formalization Note.** 0-based registers and contents (`k` in clause 2 is the paper's `k - 1`).
The reading is value-centric, the same convention as `IsHalved`: `S` is a set of elements and
`S^ε` a set of registers. The paper's strict `<` is kept. -/
def IsNearsorted {m : ℕ} (ε : ℝ) (y : Fin m → Fin m) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k ≤ m →
      (strayCount ε y (Finset.univ.filter fun v : Fin m => v.val < k) : ℝ) < ε * k) ∧
    (∀ k : ℕ, k < m →
      (strayCount ε y (Finset.univ.filter fun v : Fin m => k ≤ v.val) : ℝ) < ε * (m - k : ℕ))

/-- **ε-nearsort network** (AKS, STOC 1983, §4, p.5): "A procedure is called an ε-nearsort (of m
elements) if it accepts permutations of 1,...,m as inputs, and produces ε-nearsorted permutations
of 1,...,m as outputs." -/
def IsNearsort {m : ℕ} (ε : ℝ) (N : ComparatorNetwork m) : Prop :=
  ∀ x : Fin m → Fin m, Function.Bijective x → IsNearsorted ε (N.eval x)

end AKSZigZag


