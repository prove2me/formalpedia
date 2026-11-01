-- Prove2me | Definitions.Def_HousingImprove_HassePres
-- name    : HousingImprove_HassePres
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:58.97099+00:00
-- url     : https://prove2.me/theorems/a9f23a7a-6ebb-4775-ba18-b17fee24d89e
-- title:
--   Hasse-diagram presentation of a housing market and its length $|H|$
-- statement:
--   For each agent $a$ of a housing market $H$ on the agents $\{0,\dots,n-1\}$, the **Hasse diagram** $H_a$ of $\prec_a$ is the directed graph on the vertex set $A(a)$ with an arc $(b,c)$ if and only if $b\prec_a c$ and no agent $c'$ satisfies $b\prec_a c'\prec_a c$. A **presentation** $I$ of $H$ lists, for each agent $a$, the vertices of $H_a$ and, for each vertex $b$, its out-neighbours and its in-neighbours in $H_a$, each list without repetitions.
--
--   The **length** of the description is
--   $$|H|=\sum_{a\in N}|H_a|,$$
--   where $|H_a|$ is the number of vertices plus the number of arcs of $H_a$.
--
--   This is the input format and the size measure of the running-time statements.
--
--   **Formalization Note** `Represents I H` states that every list of `I` is duplicate-free, that the vertex list of $a$ is $A(a)$, that $c$ is in the out-list of $b$ exactly when $b$ is acceptable to $a$ and $c$ covers $b$ in $\prec_a$, and that the in-lists are the out-lists reversed. `HassePres.size` counts vertices and out-list entries.
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, Appendix A, p.30 (Hasse diagrams H_a and |H| = Σ_a |H_a|)

import Mathlib
import Definitions.Def_HousingImprove_Market

namespace HousingImprove

/-- The **input format** of a housing market on the agents `Fin n` (Schlotter, Biró, Fleiner,
arXiv:2110.06875v3, Appendix A, p.30): for each agent `a`, the Hasse diagram `H_a` of `≺_a` as a list
`verts a` of its vertices and, for each vertex `b`, the list `up a b` of its out-neighbours and the
list `down a b` of its in-neighbours.

**Formalization Note.** A list cell holds an agent; a program reaches `up a b` and `down a b` by
following a pointer from a cell of `H_a`'s lists or by a scan of `verts a` (the charging discipline
of `Prog`). Entries for `b ∉ A(a)` are empty under `Represents`. -/
structure HassePres (n : ℕ) where
  /-- The vertex set `A(a)` of `H_a`. -/
  verts : Fin n → List (Fin n)
  /-- `up a b`: the out-neighbours of `b` in `H_a` (the houses covering `b` in `≺_a`). -/
  up : Fin n → Fin n → List (Fin n)
  /-- `down a b`: the in-neighbours of `b` in `H_a` (the houses covered by `b` in `≺_a`). -/
  down : Fin n → Fin n → List (Fin n)

/-- `I` **represents** the market `H` (p.30): "The vertex set of `H_a` is the set `A(a)` of agents
whose house is acceptable for `a`, and it contains an arc `(b, c)` if and only if `b ≺_a c` and there
is no agent `c'` with `b ≺_a c' ≺_a c`." Every list is duplicate-free, and `down` is `up` reversed. -/
def Represents {n : ℕ} (I : HassePres n) (H : Market (Fin n)) : Prop :=
  ∀ a : Fin n,
    (I.verts a).Nodup ∧
    (∀ b, b ∈ I.verts a ↔ H.Acceptable a b) ∧
    (∀ b c, c ∈ I.up a b ↔
      (H.Acceptable a b ∧ H.lt a b c ∧ ¬ ∃ c', H.lt a b c' ∧ H.lt a c' c)) ∧
    (∀ b c, b ∈ I.down a c ↔ c ∈ I.up a b) ∧
    (∀ b, (I.up a b).Nodup) ∧
    (∀ c, (I.down a c).Nodup)

/-- The **length** `|H| = Σ_{a ∈ N} |H_a|` of the description (p.30), with `|H_a|` the number of
vertices plus the number of arcs of `H_a`.

**Formalization Note.** `|H_a|` counts vertices and arcs: the bound `O(|N| + Σ_a |H_a|) = O(|H|)`
on p.30 needs the vertices. Arcs are counted through the `up` lists of the vertices. -/
def HassePres.size {n : ℕ} (I : HassePres n) : ℕ :=
  ∑ a : Fin n, ((I.verts a).length + ((I.verts a).map fun b => (I.up a b).length).sum)

end HousingImprove


