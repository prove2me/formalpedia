-- Prove2me | Definitions.Def_HalfIndMatch_greedyOut
-- name    : HalfIndMatch_greedyOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:12.962517+00:00
-- url     : https://prove2.me/theorems/a333f238-f2e6-434f-8ecc-d4608617e2bd
-- title:
--   The Greedy algorithm (Algorithm 3.1) with vertex order $\sigma$ and choice rule
-- statement:
--   Fix an ordering of the vertices. **Greedy** inspects the vertices in this order in rounds $t=1,\dots,n$, revealing the adjacencies of the $t$-th vertex $v_t$ to the earlier vertices. It maintains an induced matching $M_t$ and a buffer $B_t$ of inspected, unmatched vertices with no neighbour in $V(M_t)$, starting from $M_0=B_0=\emptyset$. In round $t$:
--
--   1. if $v_t$ has no neighbour in $V(M_{t-1})\cup B_{t-1}$, then $M_t=M_{t-1}$ and $B_t=B_{t-1}\cup\{v_t\}$;
--   2. if $v_t$ has no neighbour in $V(M_{t-1})$ but has a neighbour in $B_{t-1}$, it chooses some $u_t\in N(v_t)\cap B_{t-1}$ and sets $M_t=M_{t-1}\cup\{\{u_t,v_t\}\}$ and $B_t=B_{t-1}\setminus N(v_t)$;
--   3. otherwise $M_t=M_{t-1}$ and $B_t=B_{t-1}$.
--
--   The output is $M_n$.
--
--   **Formalization Note** The order is a permutation $\sigma$ of `Fin n`; round $t$ inspects $\sigma(t-1)$. The paper's "arbitrary" $u_t$ is given by a choice rule `pick : ℕ → Finset (Fin n) → Fin n`: $u_t$ is `pick t` of the candidate set $N(v_t)\cap B_{t-1}$ when that is a candidate, and the least candidate otherwise, so every run is defined and every sequence of choices arises from some rule. The module declares `greedyChoice`, `greedyStep`, `greedyRun` (the pair $(M_t,B_t)$) and `greedyOut` ($M_n$).
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), §2.1, p.9 (PDF p.11) and Algorithm 3.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_HalfIndMatch_IsInducedMatching

open scoped Classical

namespace HalfIndMatch

/-- The vertex `u_t` chosen by Greedy in round `t` from a nonempty candidate set
`cand = N(t) ∩ B_{t−1}`: the value `pick t cand` of the choice rule if it lies in `cand`, and the
least candidate otherwise. As `pick` ranges over all functions, every choice sequence of the
paper's "choose an arbitrary `u_t`" is realized. -/
noncomputable def greedyChoice {n : ℕ} (pick : ℕ → Finset (Fin n) → Fin n) (t : ℕ)
    (cand : Finset (Fin n)) (h : cand.Nonempty) : Fin n :=
  if pick t cand ∈ cand then pick t cand else cand.min' h

/-- One round of Greedy (Algorithm 3.1, lines 4–11): the state is `(M_{t−1}, B_{t−1})` and `v` is
the vertex inspected in round `t`.
* If `v` has no neighbour in `V(M_{t−1})` and none in `B_{t−1}`: `M_t = M_{t−1}`,
  `B_t = B_{t−1} ∪ {v}`.
* If `v` has no neighbour in `V(M_{t−1})` but one in `B_{t−1}`: `u_t` is chosen from
  `N(v) ∩ B_{t−1}`, `M_t = M_{t−1} ∪ {{u_t, v}}` and `B_t = B_{t−1} \ N(v)`.
* Otherwise `M_t = M_{t−1}`, `B_t = B_{t−1}`. -/
noncomputable def greedyStep {n : ℕ} (G : SimpleGraph (Fin n)) (pick : ℕ → Finset (Fin n) → Fin n)
    (t : ℕ) (v : Fin n) (st : Finset (Sym2 (Fin n)) × Finset (Fin n)) :
    Finset (Sym2 (Fin n)) × Finset (Fin n) :=
  if ∀ w ∈ vset st.1, ¬ G.Adj v w then
    if h : (st.2.filter fun w => G.Adj v w).Nonempty then
      (insert s(greedyChoice pick t (st.2.filter fun w => G.Adj v w) h, v) st.1,
        st.2.filter fun w => ¬ G.Adj v w)
    else (st.1, insert v st.2)
  else st

/-- The state `(M_t, B_t)` of Greedy after round `t`, for the vertex order `σ` (round `t`, for
`1 ≤ t ≤ n`, inspects `σ ⟨t − 1, _⟩`) and the choice rule `pick`. `M_0 = B_0 = ∅`; rounds after
`n` change nothing. -/
noncomputable def greedyRun {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (pick : ℕ → Finset (Fin n) → Fin n) : ℕ → Finset (Sym2 (Fin n)) × Finset (Fin n)
  | 0 => (∅, ∅)
  | t + 1 =>
    if h : t < n then greedyStep G pick (t + 1) (σ ⟨t, h⟩) (greedyRun G σ pick t)
    else greedyRun G σ pick t

/-- The output `M_n` of the **Greedy** algorithm for building an induced matching, run on `G`
with vertex order `σ` and choice rule `pick`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), §2.1, p.9
(PDF p.11) and Algorithm 3.1, p.12 (PDF p.14).

**Formalization Note** The paper fixes "an arbitrary ordering 1, …, n of the vertices"; here the
order is a permutation `σ` of `Fin n`, and round `t` inspects `σ ⟨t − 1, _⟩`. The paper chooses
"an arbitrary `u_t ∈ N(t) ∩ B_{t−1}`"; here the choice is `pick t (N(t) ∩ B_{t−1})` when that is
a candidate, else the least candidate (`greedyChoice`), so the run is total and every sequence of
choices arises from some `pick`. The edge added is `s(u_t, v)`. `B_t = B_{t−1} \ N(t)` is computed
as the members of `B_{t−1}` not adjacent to the inspected vertex, as printed. Only adjacencies
between the inspected vertex and earlier vertices are consulted. -/
noncomputable def greedyOut {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (pick : ℕ → Finset (Fin n) → Fin n) : Finset (Sym2 (Fin n)) :=
  (greedyRun G σ pick n).1

end HalfIndMatch


