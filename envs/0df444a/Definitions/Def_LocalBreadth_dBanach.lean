-- Prove2me | Definitions.Def_LocalBreadth_dBanach
-- name    : LocalBreadth_dBanach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:58.145227+00:00
-- url     : https://prove2.me/theorems/a4844398-50f5-4acd-90c3-7a39f347f70d
-- title:
--   Lower Banach density in dimension one
-- statement:
--   For $A,B\subseteq\mathbb Z$ with $B$ infinite, the **lower Banach density** of $A$ in $B$ is
--   $$d_{\mathrm{banach}}(A,B)=\liminf_{|R\cap B|\to\infty}\frac{|A\cap B\cap R|}{|B\cap R|},$$
--   where $R$ ranges over all finite intervals of $\mathbb Z$. The denominator counts points of $B$, not integers, and the intervals may lie anywhere. A guarantee $d_{\mathrm{banach}}(O,K)\ge\alpha$ says that every interval holding many points of $K$ holds an $(\alpha-o(1))$ fraction of generated strings.
--
--   **Formalization Note** The liminf is written as the supremum over $s$ of the infimum over intervals with at least $s$ points of $B$. The extra guard $|B\cap R|\ge1$ matters only at $s=0$. For infinite $B$ the index sets are nonempty and the ratios lie in $[0,1]$.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Definition 1.3, p.3

import Mathlib

namespace LocalBreadth

/-- **Lower Banach density** in dimension one. Kleinberg, Wei, STOC 2027 submission (manuscript
sha256 f924cbfc…), Definition 1.3, p.3:
`d_banach(A, B) = liminf_{|R ∩ B| → ∞} |A ∩ B ∩ R| / |B ∩ R|`, over finite boxes `R`.

**Formalization Note.** A box of `ℤ` is `Set.Icc R.1 R.2`. The liminf is the supremum over `s` of
the infimum over boxes with at least `s` points of `B`; the guard `1 ≤ |B ∩ R|` only matters at
`s = 0`. For infinite `B` every such family of boxes is nonempty and the ratios lie in `[0, 1]`, so
the real infimum and supremum are genuine. All cardinalities are of subsets of an `Icc`. -/
noncomputable def dBanach (A B : Set ℤ) : ℝ :=
  ⨆ s : ℕ, ⨅ R : {R : ℤ × ℤ //
      s ≤ (B ∩ Set.Icc R.1 R.2).ncard ∧ 1 ≤ (B ∩ Set.Icc R.1 R.2).ncard},
    ((A ∩ B ∩ Set.Icc R.1.1 R.1.2).ncard : ℝ) / ((B ∩ Set.Icc R.1.1 R.1.2).ncard : ℝ)

end LocalBreadth


