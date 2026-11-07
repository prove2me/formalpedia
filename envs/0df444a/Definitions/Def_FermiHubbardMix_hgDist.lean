-- Prove2me | Definitions.Def_FermiHubbardMix_hgDist
-- name    : FermiHubbardMix_hgDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:27.104658+00:00
-- url     : https://prove2.me/theorems/603d7e17-0d16-49ee-a91f-798372f79779
-- title:
--   Hypergraph distance $\mathrm{dist}(i,j)$ and balls $\mathfrak B(X,r)$
-- statement:
--   Let $E$ be a family of subsets (hyperedges) of a finite set $\Lambda$. For distinct $i,j\in\Lambda$, $\mathrm{dist}(i,j)$ is the minimum integer $k\ge1$ for which there are $Z_1,\dots,Z_k\in E$ with
--   $$
--   i\in Z_1,\qquad j\in Z_k,\qquad Z_p\cap Z_{p+1}\neq\emptyset\quad(1\le p<k);
--   $$
--   $\mathrm{dist}(i,i)=0$, and $\mathrm{dist}(i,j)=\infty$ if no such chain exists. For $X,Y\subseteq\Lambda$, $\mathrm{dist}(X,Y)=\min_{i\in X,\,j\in Y}\mathrm{dist}(i,j)$, which is $\infty$ if either set is empty, and the **ball** of radius $r\ge0$ is
--   $$
--   \mathfrak B(X,r)=\{i\in\Lambda:\mathrm{dist}(i,X)\le r\}.
--   $$
--   In the fermionic part of the paper $E$ is the support family $E_H$ of the Hamiltonian; the balls are the supports in the quasi-locality estimates.
--
--   **Formalization Note** Distances take values in $\mathbb N\cup\{\infty\}$ (`ℕ∞`).
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition 4.2, p.16

import Mathlib
open scoped BigOperators
noncomputable section

namespace FermiHubbardMix

/-- A chain `Z_1, …, Z_k` (`k ≥ 1`) of hyperedges of `E` from `i` to `j`: `i ∈ Z_1`, `j ∈ Z_k` and
`Z_p ∩ Z_{p+1} ≠ ∅` for `1 ≤ p < k` (arXiv:2604.08408, held version sha256 055b8f8f…,
Definition 4.2, p.16). -/
def IsHyperChain {Λ : Type*} [DecidableEq Λ] (E : Set (Finset Λ)) (i j : Λ) (l : List (Finset Λ)) : Prop :=
  (∀ Z ∈ l, Z ∈ E) ∧ (∃ h : l ≠ [], i ∈ l.head h ∧ j ∈ l.getLast h) ∧
    l.IsChain (fun A B => (A ∩ B).Nonempty)

/-- **Definition 4.2 (Interaction hypergraph and induced distance)** (arXiv:2604.08408, held
version sha256 055b8f8f…, p.16). For distinct `i, j`, `dist(i, j)` is the minimum `k ≥ 1` such that a
chain of `k` hyperedges of `E` joins `i` to `j`; `dist(i, i) = 0`, and `dist(i, j) = ∞` if no chain
exists.

**Formalization Note** The value lies in `ℕ∞`; the infimum of the empty set is `⊤ = ∞`, as in the
paper. -/
def hgDist {Λ : Type*} [DecidableEq Λ] (E : Set (Finset Λ)) (i j : Λ) : ℕ∞ :=
  if i = j then 0 else ⨅ (l : List (Finset Λ)) (_ : IsHyperChain E i j l), (l.length : ℕ∞)

/-- `dist(X, Y) = min_{i ∈ X, j ∈ Y} dist(i, j)`, and `∞` if either set is empty
(arXiv:2604.08408, held version sha256 055b8f8f…, Definition 4.2, p.16). -/
def hgDistSet {Λ : Type*} [DecidableEq Λ] (E : Set (Finset Λ)) (X Y : Set Λ) : ℕ∞ :=
  ⨅ i ∈ X, ⨅ j ∈ Y, hgDist E i j

/-- The ball `𝔅(X, r) = {i ∈ Λ : dist(i, X) ≤ r}` (arXiv:2604.08408, held version sha256
055b8f8f…, Definition 4.2, p.16). -/
def hgBall {Λ : Type*} [DecidableEq Λ] (E : Set (Finset Λ)) (X : Set Λ) (r : ℕ) : Set Λ :=
  {i | hgDistSet E {i} X ≤ r}

end FermiHubbardMix


