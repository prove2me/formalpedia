-- Prove2me | Definitions.Def_CapacityGames_SetFunction
-- name    : CapacityGames_SetFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:04.743466+00:00
-- url     : https://prove2.me/theorems/67b394ec-abd1-44a3-9ea9-a14a2832f632
-- title:
--   Submodularity (6) of a set function and its contributing elements $N^*(f)$, $N^*_{-i}(f)$
-- statement:
--   Let $N$ be a finite set (the suppliers) and $f$ a real-valued function on the subsets of $N$. This module defines three notions of §4 of the paper, stated for an arbitrary set function so that they apply to the optimal supply chain profit $\Pi^*_{\mathcal C}$.
--
--   1. **Submodularity in the local form (6).** $f$ satisfies (6) if for every $S\subseteq N$ and all $i,j\in S$ with $i\ne j$,
--   $$f(S)-f(S\setminus\{i\})\le f(S\setminus\{j\})-f(S\setminus\{i,j\}).$$
--   Assumption 3 of the paper is this property for $f=\Pi^*_{\mathcal C}$.
--   2. **Contributing elements.** $N^*(f)=\{j\in N: f(N)>f(N\setminus\{j\})\}$, the elements whose removal strictly lowers $f(N)$.
--   3. **Contributing elements when $i$ is absent.** $N^*_{-i}(f)=\{j\in N: f(N\setminus\{i\})>f(N\setminus\{i,j\})\}$.
--
--   For $f=\Pi^*_{\mathcal C}$ these are the paper's $N^*(\mathcal C)$ and $N^*_{-i}(\mathcal C)$; Lemmas 1 and 2 are statements about them.
--
--   **Formalization Note** Subsets are finite sets of a finite type; $S\setminus\{i,j\}$ is obtained by removing $i$ and then $j$.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, §4, p.10 (definitions of N*(C), N*_{-i}(C); inequality (6); Assumption 3)

import Mathlib

namespace CapacityGames

/-- **Submodularity in the local form (6)**, Anderson–Chen–Shao, *Capacity Games with Supply
Function Competition*, arXiv:1905.11084v1, §4, (6), p.10: a set function `f` on the subsets of
the finite supplier set `N` satisfies, for every `S ⊆ N` and all `i, j ∈ S` with `i ≠ j`,
`f(S) − f(S ∖ {i}) ≤ f(S ∖ {j}) − f(S ∖ {i, j})`.

Assumption 3 (p.10) is this property for `f = Π*_C`.

**Formalization Note.** Subsets of `N` are `Finset N`; `S ∖ {i}` is `S.erase i` and
`S ∖ {i, j}` is `(S.erase i).erase j`. The property is stated for an arbitrary real-valued set
function so that Lemmas 1 and 2 can be stated for every such function. -/
def LocalSubmodular {N : Type*} [DecidableEq N] (f : Finset N → ℝ) : Prop :=
  ∀ S : Finset N, ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
    f S - f (S.erase i) ≤ f (S.erase j) - f ((S.erase i).erase j)

/-- **Contributing suppliers** of a set function, arXiv:1905.11084v1, §4, p.10:
`N*(f) = {j ∈ N : f(N) > f(N ∖ {j})}`. For `f = Π*_C` this is the paper's `N*(𝒞)`. -/
noncomputable def contribSet {N : Type*} [Fintype N] [DecidableEq N] (f : Finset N → ℝ) :
    Finset N :=
  Finset.univ.filter fun j => f (Finset.univ.erase j) < f Finset.univ

/-- **Contributing suppliers when `i` is absent**, arXiv:1905.11084v1, §4, p.10:
`N*_{−i}(f) = {j ∈ N : f(N ∖ {i}) > f(N ∖ {i, j})}`. For `f = Π*_C` this is the paper's
`N*_{−i}(𝒞)`. -/
noncomputable def contribSetExcept {N : Type*} [Fintype N] [DecidableEq N]
    (f : Finset N → ℝ) (i : N) :
    Finset N :=
  Finset.univ.filter fun j => f ((Finset.univ.erase i).erase j) < f (Finset.univ.erase i)

end CapacityGames


