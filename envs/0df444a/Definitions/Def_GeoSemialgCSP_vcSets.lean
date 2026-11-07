-- Prove2me | Definitions.Def_GeoSemialgCSP_vcSets
-- name    : GeoSemialgCSP_vcSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:01.739963+00:00
-- url     : https://prove2.me/theorems/a4c5d1bc-f3ac-4fa0-9d14-701cd0e06ccc
-- title:
--   VC-dimension of a family of sets
-- statement:
--   Let $\mathcal B$ be a family of subsets of a set $U$. A finite $A\subseteq U$ is **shattered** by $\mathcal B$ if every subset of $A$ has the form $B\cap A$ with $B\in\mathcal B$. The **VC-dimension** $\mathrm{VCdim}(\mathcal B)$ is the largest size of a shattered set, and $\infty$ if shattered sets are arbitrarily large.
--
--   **Formalization Note** The published `UnderstandingML.vcDim` of the indicator functions of the members of $\mathcal B$, valued in $\mathbb N\cup\{\infty\}$; the empty family has VC-dimension $0$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 'VC-dimension', p.8 (PDF p.9)

import Mathlib
import Definitions.Def_UnderstandingML_VC

namespace GeoSemialgCSP

open Classical in
/-- **VC-dimension of a family of sets.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 "VC-dimension", printed p.8 (PDF p.9):
a finite `A ⊆ U` is shattered by `𝓑` if every subset of `A` has the form `B ∩ A` with `B ∈ 𝓑`;
`VCdim(𝓑)` is the largest size of a shattered set.

**Formalization Note.** The published `UnderstandingML.vcDim` of the indicator functions of the
members of `𝓑`, valued in `ℕ∞` (`⊤` if shattered sets are unbounded; `0` for `𝓑 = ∅`). -/
noncomputable def vcSets {U : Type*} (𝓑 : Set (Set U)) : ℕ∞ :=
  UnderstandingML.vcDim ((fun (B : Set U) (x : U) => decide (x ∈ B)) '' 𝓑)

end GeoSemialgCSP


