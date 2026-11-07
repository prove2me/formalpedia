-- Prove2me | Definitions.Def_HypercliqueFalse_hypercliqueDetection
-- name    : HypercliqueFalse_hypercliqueDetection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:32:07.341259+00:00
-- url     : https://prove2.me/theorems/d9b3d0f6-5487-499c-8724-9b52244f38f0
-- title:
--   $k$-hyperclique detection in $h$-uniform hypergraphs (word RAM decision problem)
-- statement:
--   The decision problem **$k$-hyperclique detection in $h$-uniform hypergraphs**, on the published word RAM. An instance of size $n$ is an $h$-uniform hypergraph $G$ on $[n]$. The machine receives $n$ in cell $0$ and then the whole $0$-$1$ indicator array of the hyperedges of $G$ over $[n]^h$, that is $n^h$ cells; it must accept if and only if $G$ contains a $k$-hyperclique.
--
--   This is the problem of Theorem 1.1, "a $k$-clique in an $h$-uniform hypergraph with $n$ vertices can be detected".
--
--   **Formalization Note** Cell $1 + i$, for $i < n^h$, holds the indicator entry at the tuple $y$ with $i = \sum_{t} y_t\, n^{t}$ (Mathlib's `finFunctionFinEquiv`, coordinate $0$ least significant). There is no output condition: detection is the verdict.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Theorem 1.1, p.1; Section 2, p.4

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_HypercliqueFalse_IsHyperclique
import Definitions.Def_HypercliqueFalse_edgeIndicator

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse

/-- **`k`-hyperclique detection in `h`-uniform hypergraphs**, as a decision problem of the published
word RAM. Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256
6bd5cf5d…7730), Theorem 1.1, p.1: "a k-clique in an h-uniform hypergraph with n vertices can be
detected"; Section 2, p.4 for hypergraphs and hypercliques.

An instance of size `n` is an `h`-uniform hypergraph `G` on `Fin n`. The input is the whole 0-1
indicator array of `G` over `[n]^h` (`n ^ h` cells, after the cell holding `n`), and the program
must accept exactly when `G` contains a `k`-hyperclique.

**Formalization Note.** Cell `i < n ^ h` of the input holds the indicator entry at the tuple
`finFunctionFinEquiv.symm i` (mixed radix, coordinate `0` least significant). There is no output
condition: detection is the verdict. -/
def hypercliqueDetection (k h : ℕ) : Problem where
  Instance n := Hypergraph n h
  input G := List.ofFn fun i : Fin (_ ^ h) => edgeIndicator G (finFunctionFinEquiv.symm i)
  yes G := ∃ s, IsHyperclique G k s

end HypercliqueFalse


