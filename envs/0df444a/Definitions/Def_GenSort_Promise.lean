-- Prove2me | Definitions.Def_GenSort_Promise
-- name    : GenSort_Promise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:22.856237+00:00
-- url     : https://prove2.me/theorems/d3021bcd-20be-48e5-b43b-f305a8391352
-- title:
--   Hamiltonian-path promise: consecutive elements of $\pi$ are adjacent in $G$
-- statement:
--   Let $G$ be a simple graph on the vertex set $[n]$ and let $\pi$ be a hidden total ordering of the vertices, written as the list $\pi(1), \dots, \pi(n)$. The **Hamiltonian-path promise** says that consecutive elements of the hidden order are joined by an edge:
--   $$
--   (\pi(i), \pi(i+1)) \in E \qquad \text{for every } i \in [n-1],
--   $$
--   equivalently, $G$ contains the Hamiltonian path given by $\pi$. It guarantees that the instance is sortable: every comparison between consecutive elements is allowed.
--
--   **Formalization Note** The vertex set is `Fin n` and $\pi$ is a permutation of it, $\pi(i)$ being the vertex at position $i$ counted from $0$; so $u \prec_\pi v$ means $\pi^{-1}(u) < \pi^{-1}(v)$, and the paper's pairs $(\pi(i), \pi(i+1))$, $i \in [n-1]$, are the pairs at positions $i, i+1$ with $i + 1 < n$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §1, p.1 (PDF p.3) and Theorem 1.1, p.2 (PDF p.4)

import Mathlib

namespace GenSort

/-- **The Hamiltonian-path promise.** Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §1, p.1 and Theorem 1.1, p.2 (PDF pp.3–4): the
hidden ordering `π` of the vertex set satisfies `(π(i), π(i + 1)) ∈ E` for every `i ∈ [n − 1]`,
i.e. `G` contains the Hamiltonian path given by `π`.

**Formalization Note.** The vertex set `[n]` is `Fin n`. `π : Equiv.Perm (Fin n)` lists the
vertices in increasing hidden order: `π i` is the vertex at (0-based) position `i`, so
`u ≺_π v` iff `π.symm u < π.symm v`. The paper's 1-based pair `π(i), π(i + 1)`, `i ∈ [n − 1]`,
is `π ⟨i, _⟩, π ⟨i + 1, _⟩` for `i + 1 < n`. -/
def Promise {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < n), G.Adj (π ⟨i, Nat.lt_of_succ_lt h⟩) (π ⟨i + 1, h⟩)

end GenSort


