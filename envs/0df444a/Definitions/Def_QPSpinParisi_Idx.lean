-- Prove2me | Definitions.Def_QPSpinParisi_Idx
-- name    : QPSpinParisi_Idx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:31.719491+00:00
-- url     : https://prove2.me/theorems/936671fb-b522-472f-b40d-4f0a84e4a5f8
-- title:
--   The index $(\bar i,\bar a)$ of a coefficient $\alpha[\bar i,\bar a]$
-- statement:
--   The coefficients of the Hamiltonian are indexed by an increasing tuple $\bar i=(i_1<\dots<i_p)$ of sites, with $p\ge2$, together with a string $\bar a\in\{1,2,3\}^p$ of Pauli labels. Equivalently, an index is a subset $S\subseteq[n]$ with $|S|\ge2$ and a map $S\to\{1,2,3\}$. Consequently $p\le n$ always.
--
--   **Formalization Note** The labels are `Fin 3`, the source's $\{1,2,3\}$ shifted by one. The type is empty for $n<2$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3 (PDF p.3)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The index of one Gaussian coefficient `α[ī, ā]` of (2.1) (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3, PDF p.3): an increasing
tuple `ī ∈ I^n_p` with `p ≥ 2`, together with `ā ∈ {1,2,3}^p`.

**Formalization Note** An increasing `p`-tuple is the `p`-subset `S` of its entries, and `ā` is a map
`S → Fin 3` (`Fin 3` is `{1,2,3}` shifted by one). Then `p = S.card ≤ n`, so the sum over `p` in `H_n` stops at
`p = n`, as in (3.1) and (3.5). The type is empty for `n < 2`. -/
abbrev Idx (n : ℕ) : Type :=
  Σ S : {S : Finset (Fin n) // 2 ≤ S.card}, (↥S.1 → Fin 3)

end QPSpinParisi


