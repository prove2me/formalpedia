-- Prove2me | Definitions.Def_EulerSparsify_NestedConst
-- name    : EulerSparsify_NestedConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:39:06.459341+00:00
-- url     : https://prove2.me/theorems/bcc77bfe-01da-452c-a43a-d2ca1eddc86d
-- title:
--   $c$ is a constant for which Proposition 4.3 holds
-- statement:
--   For a real $c$, the property says:
--
--   1. every finite weighted graph $G=(V,E,w)$ with positive weights, $n=|V|$ and $m=|E|$ has a $(c\cdot n/m)$-nested ER partitioning (Definition 2.1); and
--   2. there is one Turing machine that, in time polynomial in the binary input length, computes such a partitioning from every input graph with positive rational weights.
--
--   Proposition 4.3 states that some universal constant $c_{\mathrm{ner}}>0$ has this property, and Lemma 5.10 is stated for every such constant (its Algorithm 5.1 uses $c_{\mathrm{ner}}$ in line 3).
--
--   **Formalization Note** Graphs may have parallel edges (as $\mathrm{und}(\vec G)$ of a directed graph with antiparallel edges does) and self-loops. For $m=0$ the quotient $n/m$ is $0$ and the empty family is a $0$-nested partitioning.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Proposition 4.3, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_EulerSparsify_IsNestedER
import Definitions.Def_EulerSparsify_RatDigraph
import Definitions.Def_EulerSparsify_encNestedList

namespace EulerSparsify

/-- **"c is a constant for which Proposition 4.3 holds"** (Proposition 4.3, p.13, PDF p.15).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Proposition 4.3: "There is an algorithm that given any weighted graph G = (V, E, w), with
n = |V|, m = |E|, computes in polynomial time a c_ner · n/m-nested ER partitioning for a universal
constant c_ner."

`NestedConst c` says:
1. every finite weighted graph `G` with positive weights, `n` vertices and `m` edges has a
   `(c · n/m)`-nested ER partitioning (Definition 2.1); and
2. one Turing machine computes, in time polynomial in the binary input length, such a partitioning
   from every rational-weighted input graph with positive weights.

Proposition 4.3 is `∃ c > 0, NestedConst c`; Lemma 5.10 assumes `NestedConst c_ner`.

**Formalization Note.** Graphs may have parallel edges (as `und(⃗G)` of a directed graph with
antiparallel edges does) and self-loops. For `m = 0`, `n/m = 0` in Lean and the empty family is a
`0`-nested partitioning, so nothing is lost. The machine's output is a list of members
`(U_i, E_i, F_i, j_i)` (`encNestedList`), read with `NestedFamily.ofList`. -/
def NestedConst (c : ℝ) : Prop :=
  (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : DiGraph V E),
      (∀ e, 0 < G.w e) →
        ∃ P : NestedFamily V E, IsNestedER G (c * Fintype.card V / Fintype.card E) P) ∧
  ∃ alg : RatDigraph → List (List ℕ × List ℕ × List ℕ × ℤ),
    Nonempty (Turing.TM2ComputableInPolyTime encRatDigraph encNestedList alg) ∧
    ∀ (I : RatDigraph) (hI : I.WellFormed), (∀ x ∈ I.2, 0 < x.2.2) →
      IsNestedER (I.toDiGraph hI) (c * I.1 / I.2.length)
        (NestedFamily.ofList Fin.val Fin.val (alg I))

end EulerSparsify


