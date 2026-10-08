-- Prove2me | Definitions.Def_BartlettNN_FatNet_combos
-- name    : BartlettNN_FatNet_combos
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:25:13.461631+00:00
-- url     : https://prove2.me/theorems/df65c6f6-2d0b-48b3-b1de-d24cf6c9a0a5
-- title:
--   The class H of two-layer networks with ℓ1-bounded output weights (Theorem 17)
-- statement:
--   Let $F$ be a class of real-valued functions on a set $X$ (the hidden units) and $A\ge0$. The class of two-layer networks with hidden units from $F$ and output weights of total absolute value at most $A$ is
--
--   $$
--   H=\Big\{\sum_{i=1}^N w_i f_i:\ N\in\mathbb N,\ f_i\in F,\ \sum_{i=1}^N|w_i|\le A\Big\}.
--   $$
--
--   The number $N$ of hidden units is unrestricted; only the $\ell_1$ norm of the output weights is bounded. This is the class whose fat-shattering dimension Theorem 17 bounds.
--
--   **Formalization Note** `combos F A` is the set of functions $x\mapsto\sum_{i<N}w_i f_i(x)$ for some $N\in\mathbb N$, weights $w:\{0,\dots,N-1\}\to\mathbb R$ and members $f_i\in F$ with $\sum_i|w_i|\le A$. Allowing $N=0$ adds only the zero function, which for nonempty $F$ (Theorem 17 assumes $F\neq\emptyset$) is in $H$ anyway (take all $w_i=0$); for $F=\emptyset$ the class is $\{0\}$. The definition accepts any real $A$; Theorem 17 assumes $A\ge 0$ (for $A<0$ the class is empty).
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 532, Theorem 17 (definition of H)

import Mathlib

namespace BartlettNN.FatNet

/-- Bartlett (1998), Theorem 17, p. 532: the class of two-layer networks with hidden units
from `F` and output weights of `ℓ1` norm at most `A`,
`H = {∑_{i=1}^N w_i f_i : N ∈ ℕ, f_i ∈ F, ∑_{i=1}^N |w_i| ≤ A}`.
(`N = 0` gives the zero function; for nonempty `F`, as Theorem 17 assumes, it is in `H` anyway
with all `w_i = 0`. For `F = ∅` the class is `{0}`.) -/
def combos {X : Type*} (F : Set (X → ℝ)) (A : ℝ) : Set (X → ℝ) :=
  {h | ∃ (N : ℕ) (w : Fin N → ℝ) (f : Fin N → X → ℝ), (∀ i, f i ∈ F) ∧ ∑ i, |w i| ≤ A ∧
    h = fun x => ∑ i, w i * f i x}

end BartlettNN.FatNet


