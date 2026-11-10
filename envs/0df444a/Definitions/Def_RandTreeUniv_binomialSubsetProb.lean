-- Prove2me | Definitions.Def_RandTreeUniv_binomialSubsetProb
-- name    : RandTreeUniv_binomialSubsetProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:16.526584+00:00
-- url     : https://prove2.me/theorems/17aa44b1-09a9-4ce5-9687-74c61e3efc7a
-- title:
--   Probability that the $p$-random subset $X_p$ has a property
-- statement:
--   Let $X$ be a finite set and $p\in[0,1]$. The random subset $X_p$ retains each element of $X$ independently with probability $p$, so a fixed subset $Y\subseteq X$ occurs with probability $p^{|Y|}(1-p)^{|X\setminus Y|}$. For a property $E$ of subsets,
--
--   $$
--   \mathbb P(X_p\text{ has }E)=\sum_{Y\subseteq X,\ E(Y)}p^{|Y|}(1-p)^{|X\setminus Y|}.
--   $$
--
--   When $X$ is the edge set of $K_n$, $X_p$ is the binomial random graph $G(n,p)$.
--
--   **Formalization Note** The formula is used only for $p\in[0,1]$; theorems using it assume this.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §2.6, p.13 (PDF 14)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `P(X_p` has property `E)`, where `X_p` is "a random subset of `X` where each element is
retained with probability `p` independently of the others" (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §2.6, p.13 (PDF 14)): the
subset `Y` has probability `p^{|Y|} (1 - p)^{|X \ Y|}`.

**Formalization Note** `X` is a finite type; `p` is meant to lie in `[0, 1]` (the theorems that
use this assume it). -/
noncomputable def binomialSubsetProb {X : Type*} [Fintype X] (p : ℝ) (E : Finset X → Prop) : ℝ :=
  ∑ Y : Finset X, if E Y then p ^ Y.card * (1 - p) ^ (Yᶜ).card else 0

end RandTreeUniv


