-- Prove2me | Definitions.Def_HypercliqueFalse_Supplement_apDetection
-- name    : HypercliqueFalse_Supplement_apDetection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:31:49.108508+00:00
-- url     : https://prove2.me/theorems/7175283b-a91d-48ad-ac20-9f99d27d27f3
-- title:
--   Nontrivial $k$-AP detection in $A \subseteq \{0,\dots,N\}$ (word RAM decision problem)
-- statement:
--   Fix $k \in \mathbb N$. **Nontrivial $k$-AP detection** is the following decision problem. An instance of size $N$ is a set $A \subseteq \{0, 1, \dots, N\}$ (both endpoints allowed). It is a *yes*-instance exactly when $A$ contains a **nontrivial $k$-term arithmetic progression**: there are $a, d \in \mathbb N$ with $d \ge 1$ such that
--   $$
--   a,\ a+d,\ a+2d,\ \dots,\ a+(k-1)d \in A .
--   $$
--   The input given to the machine is the $0$-$1$ indicator array of $A$: after the cell holding $N$, the $N+1$ cells hold $\mathbf 1[i \in A]$ for $i = 0, 1, \dots, N$ in increasing order.
--
--   This is the problem of Theorem 1.2 of the paper, and the problem of the $k$-AP Hypothesis of Dudek, Fischer, Gokaj, Jin, Künnemann, Mao and Redžić; the size parameter is the universe bound $N$, not $|A|$.
--
--   **Formalization Note** The problem is a `TrulySubcubicAPSP.Problem` of the published word RAM, with instance index $N$ and instances `Finset (Fin (N + 1))`. The progression predicate is the published `HypercliqueCircuits.Circuits.Supplement.HasProgression` (definition 13fb0705), which asks for $a, d \in \mathbb N$, $0 < d$, with $a + j d \in A$ for all $j < k$. A progression with negative difference is the same set read backwards, so "nontrivial" ($d \ne 0$) is the same as $d > 0$. There is no output condition: detection is the verdict.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Theorem 1.2, p.2 (PDF 3); Section 1.1, statement of the k-AP Hypothesis, p.2

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Progression

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse.Supplement

/-- **Nontrivial `k`-AP detection in `A ⊆ {0, …, N}`**, as a decision problem of the published word
RAM. Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256
6bd5cf5d…7730), Theorem 1.2, p.2: "a nontrivial k-AP in a given set A ⊆ {0, . . . , N} can be
detected".

An instance of size `N` is a set `A ⊆ {0, …, N}`, i.e. `A : Finset (Fin (N + 1))` (both endpoints
allowed). The input is the `N + 1` indicator words of `A` (cell `i` holds `1` if `i ∈ A` and `0`
otherwise, `i = 0, …, N` in increasing order), after the cell holding `N`. The program must accept
exactly when `A` contains a nontrivial `k`-term arithmetic progression, i.e. (published predicate
`HasProgression`) there are `a, d ∈ ℕ` with `d > 0` and `a + j·d ∈ A` for every `j < k`.

**Formalization Note.** The size parameter is the universe bound `N`, not `|A|`. Nontrivial means
common difference `d ≠ 0`; by reversing the order of a progression with negative difference this
is the same as `d > 0`. There is no output condition: detection is the verdict. -/
def apDetection (k : ℕ) : Problem where
  Instance N := Finset (Fin (N + 1))
  input A := List.ofFn fun i : Fin (_ + 1) => if i ∈ A then (1 : ℤ) else 0
  yes A := HypercliqueCircuits.Circuits.Supplement.HasProgression k A

end HypercliqueFalse.Supplement


