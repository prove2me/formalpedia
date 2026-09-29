-- Prove2me | Definitions.Def_Erdos77_diagonal_ramsey
-- name    : Erdos77_diagonal_ramsey
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T18:15:14.77458+00:00
-- url     : https://prove2.me/theorems/0575e252-a9f4-4ec8-9d5a-9573f97affb4
-- title:
--   Diagonal Ramsey number $R(k)$
-- statement:
--   For $k\in\mathbb N$, the **diagonal Ramsey number** $R(k)$ is the least natural number $n$ such that for every simple graph $G$ on the vertex set $\{0,1,\dots,n-1\}$, either $G$ contains a clique of exactly $k$ vertices, or the complement graph $G^{c}$ contains a clique of exactly $k$ vertices:
--
--   $$
--   R(k)=\min\{\,n\in\mathbb N : \forall G \text{ on } [n],\ \omega(G)\ge k \ \text{ or }\ \omega(G^{c})\ge k\,\}.
--   $$
--
--   Viewing the edges of $G$ as red and the edges of $G^{c}$ as blue, this is the least $n$ such that every red/blue colouring of the edges of $K_n$ contains a monochromatic $K_k$. This is the object in Erdős Problem 77 and in all milestones of this mission.
--
--   **Formalization Note** The minimum is Lean's `sInf` on $\mathbb N$, which returns $0$ on the empty set. By Ramsey's theorem (quantitatively, the Erdős–Szekeres milestone) the set is nonempty for every $k$, so the definition agrees with the usual Ramsey number. With this definition $R(0)=0$ and $R(1)=1$.
-- source:
--   Erdős Problems #77, https://www.erdosproblems.com/77 (definition of R(k) in the problem statement); cf. the Formal Conjectures file ErdosProblems/77.lean, which uses SimpleGraph.diagonalRamsey.

import Mathlib

namespace Erdos77

/-- The diagonal Ramsey number `R(k)`: the least `n` such that every graph `G` on `n`
vertices contains a `k`-clique or its complement contains a `k`-clique (equivalently, every
red/blue colouring of the edges of `K_n` has a monochromatic `K_k`). -/
noncomputable def diagonalRamsey (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique k s) ∨ (∃ s : Finset (Fin n), Gᶜ.IsNClique k s)}

end Erdos77


