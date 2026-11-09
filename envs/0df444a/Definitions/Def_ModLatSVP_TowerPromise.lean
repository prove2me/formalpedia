-- Prove2me | Definitions.Def_ModLatSVP_TowerPromise
-- name    : ModLatSVP_TowerPromise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:28.394729+00:00
-- url     : https://prove2.me/theorems/9e4d81fc-4047-4e25-989c-843aca0cea5f
-- title:
--   The promise of Theorem 1.1 — bounded rank, bounded root discriminant, a subfield chain exists
-- statement:
--   Fix integers $n_0,d_0\ge1$, $s_0\ge2$ and a rational $C_0\ge1$. A number field $K$ and a lattice dimension $N$ satisfy the **module promise** if
--
--   1. $K$ is totally real or CM;
--   2. the module is nonzero and has rank at most $n_0$: $1\le N\le n_0[K:\mathbb Q]$;
--   3. $\mathrm{rd}(K)\le C_0$, i.e. $|\Delta_K|\le C_0^{[K:\mathbb Q]}$.
--
--   They satisfy the **tower promise** if moreover $K$ has a subfield chain with relative degrees at most $s_0$ ending in degree at most $d_0$; the chain itself is not given.
--
--   These are the hypotheses of Theorems 3.4 and 3.5 without the supplied chain, and the hypotheses of Corollary 3.7, the formal version of Theorem 1.1.
--
--   **Formalization Note** The module rank is $N/[K:\mathbb Q]$ because $\mathbb Q^N$ is a $K$-vector space.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 1.1, p.2 (PDF p.2); Theorem 3.4, p.20; Corollary 3.7, p.23

import Mathlib
import Definitions.Def_ModLatSVP_IsChain

open NumberField

namespace ModLatSVP

/-- The standing hypotheses of Theorem 3.4, p.20, on the field and the module, chain aside. Kim, Lee,
Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027
submission (manuscript sha256 e7151fad…): `K` is totally real or CM, `rd(K) ≤ C₀`, and the module
`ℤ^N` is "nonzero" and of rank at most `n₀`.

**Formalization Note.** `rd(K) ≤ C₀` is written `|∆_K| ≤ C₀^{[K:ℚ]}` (no real roots). The module rank
is `N / [K : ℚ]` because `ℚ^N` is a `K`-vector space, so "rank at most `n₀`" is `N ≤ n₀ · [K : ℚ]`;
"nonzero" is `1 ≤ N`. -/
def ModulePromise (K : Type*) [Field K] [NumberField K] (n₀ : ℕ) (C₀ : ℚ) (N : ℕ) : Prop :=
  (IsTotallyReal K ∨ IsCMField K) ∧ 1 ≤ N ∧ N ≤ n₀ * Module.finrank ℚ K ∧
  |(discr K : ℝ)| ≤ (C₀ : ℝ) ^ Module.finrank ℚ K

/-- The promise of Theorem 1.1, p.2, in its formal version Corollary 3.7, p.23: the hypotheses of
Theorem 3.4 with "the supplied subfield chain … replaced by the promise that such a chain exists". -/
def TowerPromise (K : Type*) [Field K] [NumberField K] (n₀ d₀ s₀ : ℕ) (C₀ : ℚ) (N : ℕ) : Prop :=
  ModulePromise K n₀ C₀ N ∧ ∃ (h : ℕ) (F : ℕ → IntermediateField ℚ K), IsChain K s₀ d₀ F h

end ModLatSVP


