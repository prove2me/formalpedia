-- Prove2me | Definitions.Def_BFFPyramidal_pyramidal
-- name    : BFFPyramidal_pyramidal
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-13T18:25:09.965213+00:00
-- url     : https://prove2.me/theorems/9ebff984-8a1a-425e-8293-1cc5c5a19d21
-- title:
--   Pyramidal groups
-- statement:
--   A finite group $G$ is **pyramidal** if it admits a chain of subgroups
--   $$ \{1\} = G_n \subseteq G_{n-1} \subseteq \cdots \subseteq G_1 \subseteq G_0 = G $$
--   in which each step has index equal to the *least* prime factor of the order of the preceding term:
--   $$ [G_{k-1} : G_k] = p\!\left(|G_{k-1}|\right), \qquad 1 \le k \le n, $$
--   where $p(m)$ denotes the least prime factor of $m$.
--
--   It is classical that a subgroup whose index is the smallest prime dividing the group order is normal; such a chain is therefore a composition series, so every pyramidal group is solvable, and every supersolvable group is pyramidal. Pyramidality is thus a chain condition lying between supersolvability and solvability. It is the hypothesis under which Berger, Felzenbaum and Fraenkel establish their multiplicity bound for coset partitions.
--
--   **Formalization note.** The chain is a function `c : ℕ → Subgroup G` together with a length $n$, with `c 0 = ⊤`, `c n = ⊥`, and the step condition imposed exactly for `k < n`; values of `c` beyond $n$ are unconstrained. Each step asserts both `c (k+1) ≤ c k` and that `Subgroup.relIndex (c (k+1)) (c k)` — the index of `c (k+1) ⊓ c k` in `c k` — equals `Nat.minFac (Nat.card (c k))`; the containment is what makes the relative index the ordinary index. Descent is not required to be strict: once the chain reaches $\bot$, `Nat.minFac 1 = 1` forces index $1$, so $\bot$ may repeat and $n$ is not determined by $G$. None of this changes the class of groups described. Normality of the steps is a consequence, not a hypothesis, and solvability is stated separately as `BFFPyramidal.isSolvable_of_isPyramidal`.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 139, eqs. (1)-(2)

import Mathlib

namespace BFFPyramidal

/-- A finite group `G` is **pyramidal** if it admits a chain of subgroups
`⊤ = c 0 ≥ c 1 ≥ ⋯ ≥ c n = ⊥` in which every step has relative index equal to the *least*
prime factor of the order of the preceding term:
`[c k : c (k+1)] = Nat.minFac |c k|` for every `k < n`.

This is conditions (1)–(2) of Berger–Felzenbaum–Fraenkel.

Three points about the formalization, none of which changes the class of groups described.
The chain is a total function on `ℕ`; only its values at indices `≤ n` are constrained, and the
step condition is imposed exactly for `k < n`. The containment `c (k+1) ≤ c k` is stated
alongside the index condition, and is what makes `Subgroup.relIndex (c (k+1)) (c k)` — the index
of `c (k+1) ⊓ c k` in `c k` — equal to the ordinary index `[c k : c (k+1)]`. Descent is not
required to be strict: once a chain reaches `⊥`, `Nat.minFac 1 = 1` forces index `1`, so `⊥` may
repeat, and `n` is therefore not determined by `G`.

It is classical that a subgroup whose index is the least prime dividing the order is normal, so
such a chain is a composition series and a pyramidal group is solvable; that consequence is *not*
part of this definition and is stated separately as `BFFPyramidal.isSolvable_of_isPyramidal`.
Every supersolvable group is pyramidal. -/
def IsPyramidal (G : Type*) [Group G] [Finite G] : Prop :=
  ∃ (n : ℕ) (c : ℕ → Subgroup G),
    c 0 = ⊤ ∧ c n = ⊥ ∧
    ∀ k < n, c (k + 1) ≤ c k ∧
      Subgroup.relIndex (c (k + 1)) (c k) = Nat.minFac (Nat.card (c k))

end BFFPyramidal


