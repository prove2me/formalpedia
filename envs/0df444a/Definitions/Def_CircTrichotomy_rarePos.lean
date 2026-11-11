-- Prove2me | Definitions.Def_CircTrichotomy_rarePos
-- name    : CircTrichotomy_rarePos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:10.319391+00:00
-- url     : https://prove2.me/theorems/355d0d8c-b5e7-43dc-893b-1136c2b2d6b7
-- title:
--   Rare positions $R^t_k(w)$
-- statement:
--   For $k,t\ge1$ and a word $w$, a letter $a$ is **rare** in the residue class $i$ if $|\pi_{i,k}(w)|_a<t$. The **rare positions** of $w$ are
--   $$R^t_k(w)=\bigcup_{i\in[0,k-1]}\ \bigcup_{a\in\mathrm{cont}^{<t}_{i,k}(w)}P_{a,i,k}(w),\qquad P_{a,i,k}(w)=\{j: w_j=a,\ j\equiv_k i\},$$
--   the positions whose letter occurs fewer than $t$ times in their residue class modulo $k$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), (30)–(32), p.21

import Mathlib
import Definitions.Def_CircTrichotomy_piMod

set_option autoImplicit false

namespace CircTrichotomy

/-- **Rare positions `R^t_k(w)`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), (30)–(32), p.21): "The set of occurrences of letter a in
positions of w that are in residue class i mod k is denoted by P_{a,i,k}(w) = {j ∈ [0, n − 1] :
a_j = a, j ≡_k i}. The letters in cont^{<t}_{i,k}(w) are the rare letters in the residue class i.
The set of rare positions in modular class i is R^t_{i,k}(w) = ⋃_{a ∈ cont^{<t}_{i,k}(w)}
P_{a,i,k}(w). Finally, the set of rare positions in w is R^t_k(w) = ⋃_{i ∈ [0,k−1]} R^t_{i,k}(w)."

A position `j` is rare iff for some `i < k` with `j ≡ i (mod k)` its letter `a = w_j` occurs fewer
than `t` times among the positions `≡ i (mod k)` (`|π_{i,k}(w)|_a < t`). -/
def rarePos {α : Type} (t k : ℕ) (w : List α) : Set ℕ :=
  {j | ∃ i < k, ∃ a : α, cntMod k i a w < t ∧ w[j]? = some a ∧ j % k = i}

end CircTrichotomy


