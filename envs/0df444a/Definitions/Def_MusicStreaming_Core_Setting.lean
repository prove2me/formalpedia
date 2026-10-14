-- Prove2me | Definitions.Def_MusicStreaming_Core_Setting
-- name    : MusicStreaming_Core_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:06:50.446726+00:00
-- url     : https://prove2.me/theorems/c164c8e8-90ba-4063-9661-49b6732c0dfb
-- title:
--   §2 and §4, pp. 7–14 — streaming problems, the lists $L^j$, the streaming game $v$ and the allocation set $A(N,M,t)$
-- statement:
--   Let $N=\{1,\dots,n\}$ be a set of artists. A **streaming problem** records, for each user $j$ of a finite user set $M$ and each artist $i\in N$, the number $t_{ij}\in\mathbb N$ of times user $j$ played content of artist $i$ during a period. Every user in $M$ is assumed to have played at least one artist (the paper's standing assumption, recalled on p. 19).
--
--   1. The **list** of user $j$ is the set of artists that user played,
--   $$L^j=\{i\in N: t_{ij}>0\}.$$
--   2. The **streaming game** is the TU game on the artists in which a coalition $S\subseteq N$ is worth the number of users (each paying $1$) who played only artists in $S$:
--   $$v(S)=\bigl|\{j\in M: L^j\subseteq S\}\bigr|.$$
--   Because every list is nonempty, $v(\emptyset)=0$.
--   3. The **allocation set** collects the ways of splitting each user's payment of $1$ among the artists that user played and adding up over users:
--   $$A(N,M,t)=\Bigl\{x\in\mathbb R^N:\ x=\sum_{j\in M}x^j,\ \text{where for each } j\in M:\ x^j_i=0\ (i\notin L^j),\ x^j_i\ge 0\ (i\in L^j),\ \sum_{i\in N}x^j_i=1\Bigr\}.$$
--
--   These are the objects of Theorem 2, which identifies the core of $v$ with $A(N,M,t)$.
--
--   **Formalization Note** Artists are `Fin n` (the paper's artist $i$ is index $i-1$). Users are named by natural numbers, and a problem is a finitely supported map `t : ℕ →₀ (Fin n → ℕ)` with `t j i` $=t_{ij}$; the user set $M$ is the support of `t`, so every user in $M$ has a nonzero column, which is exactly the assumption $L^j\neq\emptyset$. Streams are natural numbers. The paper's "$\subset$" is read as "$\subseteq$". In `allocSet` the family $(x^j)_{j\in M}$ is a function `y : ℕ → Fin n → ℝ` whose values at users outside $M$ are never read. The same objects are restated in the sibling missions of this series (draft items cannot import each other).
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, pp. 7–8 (§2: streaming problems, L^j) and pp. 13–14 (§4: the game v and the set A(N, M, t))

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Core

variable {n : ℕ}

/-- The streaming game `v(S) = |{j ∈ M : L^j ⊆ S}|` on coalitions `S` of artists (p. 13): the
number of users (each paying `1`) who played only artists in `S`. -/
def game (t : MusicStreaming.Axioms.Problem n) (S : Finset (Fin n)) : ℝ :=
  ((t.support.filter (fun j => MusicStreaming.Axioms.listened t j ⊆ S)).card : ℝ)

/-- The allocation set `A(N, M, t)` (p. 14): the vectors `x = ∑_{j ∈ M} x^j` where, for each user
`j ∈ M`, `x^j` is a nonnegative vector supported on `L^j` with total `1`. The family `(x^j)` is
`y : ℕ → Fin n → ℝ`; its values at users outside `M` are never read. -/
def allocSet (t : MusicStreaming.Axioms.Problem n) : Set (Fin n → ℝ) :=
  {x | ∃ y : ℕ → Fin n → ℝ,
    (∀ j ∈ t.support, (∀ i, i ∉ MusicStreaming.Axioms.listened t j → y j i = 0) ∧
      (∀ i ∈ MusicStreaming.Axioms.listened t j, 0 ≤ y j i) ∧ ∑ i, y j i = 1) ∧
    x = ∑ j ∈ t.support, y j}

end MusicStreaming.Core


