-- Prove2me | Definitions.Def_SharpConsist_embedX
-- name    : SharpConsist_embedX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:33.313524+00:00
-- url     : https://prove2.me/theorems/f13212fc-4727-407e-a510-716426aa1179
-- title:
--   The current set $X$ inside $X\cup\{r\}$, and the restricted oracle
-- statement:
--   The lower bound uses a stream $1,2,\dots,n,r$: the current (old) elements $X=\{1,\dots,n\}$ arrive first and the critical element $r$ arrives last. The ground set after the final arrival is $X\cup\{r\}$.
--
--   The map $S\mapsto S$ views a subset of $X$ as a subset of $X\cup\{r\}$, and the **restricted oracle** of an objective $f$ on $X\cup\{r\}$ is $S\mapsto f(S)$ for $S\subseteq X$: the only answers a value query can return before $r$ arrives.
--
--   **Formalization Note.** $X\cup\{r\}$ is `Fin (n+1)`, an old element $i$ is `Fin.castSucc i` for `i : Fin n` (0-based), and $r$ is `Fin.last n`.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), Theorem 5.1, p.12

import Mathlib

namespace SharpConsist

/-- The current set `X = {1, …, n}` inside the final ground set `X ∪ {r}`. Fu–Zhang–Tao,
arXiv:2609.09986 (held version, sha256 874ec76c…), §5, Theorem 5.1, p.12 (arrival order
`1, 2, …, n, r`).

**Formalization Note.** The ground set after the final arrival is `Fin (n+1)`; the old elements
`1, …, n` are `Fin.castSucc i` for `i : Fin n` (0-based) and the final element `r` is `Fin.last n`.
`embedX S` is the image of `S ⊆ X` in `Fin (n+1)`. -/
def embedX {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.map Fin.castSuccEmb

/-- The value oracle of `f` restricted to subsets of the current set `X`: the only information a
query before the final arrival can return. -/
def restrictX {n : ℕ} (f : Finset (Fin (n + 1)) → ℝ) : Finset (Fin n) → ℝ :=
  fun S => f (embedX S)

end SharpConsist


