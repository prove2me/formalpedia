-- Prove2me | Definitions.Def_PPRInstOpt_UnknownN_QueryModel
-- name    : PPRInstOpt_UnknownN_QueryModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:14:19.690715+00:00
-- url     : https://prove2.me/theorems/19b03f01-fe3f-44d2-ae83-52e100676770
-- title:
--   Randomized adaptive query algorithms without knowledge of n, good algorithms, expected cost
-- statement:
--   A **query algorithm** is given direct access to $s$ and $t$ only. It sees vertices under discovery names: $s$ is $0$, $t$ is announced as $0$ (if $t=s$) or $1$, and every vertex returned for the first time by a neighbour query gets the next unused name. At each step, as an arbitrary measurable function of its random tape and the transcript, it either stops and outputs a real $\hat\pi$, or asks one of $\mathrm{outdeg}(v)$, $\mathrm{indeg}(v)$, $\mathrm{out}(v,i)$, $\mathrm{in}(v,i)$ for a name $v$; an unused name or an index past the end is answered `none`. There is no Jump query and no access to $n$.
--
--   Its **cost** on an instance is $1+{}$the number of queries ($\top$ if it never stops), and
--   $$\mathrm{expCost}(A;G,s,t)=\mathbb E_\omega\big[1+Q_A(\omega)\big].$$
--   $A$ is **good** if on every valid instance ($G$ a valid graph on any finite vertex type, $\pi(s,t)>0$) it stops with $|\hat\pi-\pi(s,t)|\le\varepsilon_r\pi(s,t)$ with probability at least $2/3$. `triExpTime` is $\mathbb E[\text{time of TriPPR}]$.
--
--   **Formalization Note** Computation is free for competitors (they are computationally unbounded); only queries are counted, plus one for the output step.
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 2-3, 5, §1.1, §1.4

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_TriPPR

/-!
# Competitors: randomized adaptive algorithms in the adjacency-list query model without `n`

§1.1 (pp. 2–3) and §1.4 (p. 5). The algorithm is given direct access to `s` and `t` only and
reaches other vertices by following in- and out-edges of vertices already visited; there is no
`Jump` query and no knowledge of `n`.

Encoding. Vertices are shown to the algorithm under discovery names: `s` is `0`, `t` is the name
announced in the first transcript entry (`0` if `t = s`, else `1`), and each vertex returned by a
neighbour query for the first time gets the next unused name. A query naming an unused name, or an
index past the end of a list (indices from `0`), is answered `none`. The algorithm is any function
of its random tape and the transcript (computationally unbounded, adaptive); the tape has the law
`tapeLaw`, independent of the instance. Its cost on an instance is `1 +` the number of queries
(the `+1` is the output step); a run that never stops has cost `⊤` and does not succeed.
-/

open MeasureTheory
open scoped ENNReal

namespace PPRInstOpt.UnknownN

/-- A query on a named vertex: `outdeg(v)`, `indeg(v)`, `out(v, i)`, `in(v, i)`. -/
inductive Query where
  | outdeg (v : ℕ)
  | indeg (v : ℕ)
  | outNbr (v i : ℕ)
  | inNbr (v i : ℕ)

/-- An answer: a degree, a vertex name, or `none`. -/
inductive Answer where
  | num (k : ℕ)
  | vertex (name : ℕ)
  | none

/-- A randomized adaptive query algorithm: `next ω h` is the next query after transcript `h`
(`none` = stop), `output ω h` the estimate it outputs when it stops. Both are measurable in the
tape, so that its success probability and expected cost are defined. -/
structure QueryAlg where
  next : Tape → List Answer → Option Query
  output : Tape → List Answer → ℝ
  measurableSet_next : ∀ (h : List Answer) (q : Option Query), MeasurableSet {ω | next ω h = q}
  measurable_output : ∀ h : List Answer, Measurable (fun ω => output ω h)

variable {V : Type} [DecidableEq V]

/-- The name of a returned vertex `y`, extending the list of named vertices if `y` is new. -/
def nameOf (names : List V) (y : V) : List V × Answer :=
  if y ∈ names then (names, Answer.vertex (names.findIdx (fun z => decide (z = y))))
  else (names ++ [y], Answer.vertex names.length)

/-- The oracle's answer to a query, given the vertices named so far. -/
def answer (G : Digraph V) (names : List V) : Query → List V × Answer
  | .outdeg v => match names[v]? with
    | some x => (names, Answer.num (G.dout x))
    | none => (names, Answer.none)
  | .indeg v => match names[v]? with
    | some x => (names, Answer.num (G.din x))
    | none => (names, Answer.none)
  | .outNbr v i => match names[v]? with
    | some x => match (G.outList x)[i]? with
      | some y => nameOf names y
      | none => (names, Answer.none)
    | none => (names, Answer.none)
  | .inNbr v i => match names[v]? with
    | some x => match (G.inList x)[i]? with
      | some y => nameOf names y
      | none => (names, Answer.none)
    | none => (names, Answer.none)

/-- The start of a run: `s` named `0`, `t` named next unless `t = s`; the transcript announces
`t`'s name. -/
def compInit (s t : V) : List V × List Answer :=
  if t = s then ([s], [Answer.vertex 0]) else ([s, t], [Answer.vertex 1])

/-- One step of the run: ask the next query (if any) and append its answer. -/
def compStep (A : QueryAlg) (G : Digraph V) (ω : Tape) (st : List V × List Answer) :
    List V × List Answer :=
  match A.next ω st.2 with
  | none => st
  | some q => let a := answer G st.1 q; (a.1, st.2 ++ [a.2])

/-- The named vertices and the transcript after `k` steps. -/
def compState (A : QueryAlg) (G : Digraph V) (s t : V) (ω : Tape) (k : ℕ) :
    List V × List Answer :=
  (compStep A G ω)^[k] (compInit s t)

/-- The run has stopped after exactly `k` queries. -/
def compStopsAt (A : QueryAlg) (G : Digraph V) (s t : V) (ω : Tape) (k : ℕ) : Prop :=
  A.next ω (compState A G s t ω k).2 = none

/-- The number of queries of the run (`⊤` if it never stops). -/
noncomputable def queryCount (A : QueryAlg) (G : Digraph V) (s t : V) (ω : Tape) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : compStopsAt A G s t ω k), (k : ℕ∞)

/-- The output of a stopping run. -/
noncomputable def compOutput (A : QueryAlg) (G : Digraph V) (s t : V) (ω : Tape) : ℝ :=
  A.output ω (compState A G s t ω (sInf {k | compStopsAt A G s t ω k})).2

variable [Fintype V]

/-- The run stops with an output within relative error `εr` of `π(s, t)`. -/
def compSucceeds (A : QueryAlg) (α εr : ℝ) (G : Digraph V) (s t : V) (ω : Tape) : Prop :=
  (∃ k, compStopsAt A G s t ω k) ∧
    |compOutput A G s t ω - ppr α G s t| ≤ εr * ppr α G s t

end PPRInstOpt.UnknownN

namespace PPRInstOpt.UnknownN

/-- A good algorithm (§1.1, p. 2): on every valid instance — every finite simple digraph with
positive out-degrees, every `s, t` with `π(s, t) > 0` — it outputs `\hat π` with
`|\hat π - π(s, t)| ≤ εr π(s, t)` with probability at least `2/3`. -/
def IsGood (A : QueryAlg) (α εr : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) (s t : V), 0 < ppr α G s t →
    (2 / 3 : ℝ≥0∞) ≤ tapeLaw {ω | compSucceeds A α εr G s t ω}

/-- The expected cost `E[1 + #queries]` of `A` on the instance `(G, s, t)`. -/
noncomputable def expCost (A : QueryAlg) {V : Type} [DecidableEq V] (G : Digraph V) (s t : V) :
    ℝ≥0∞ :=
  ∫⁻ ω, (1 + ((queryCount A G s t ω : ℕ∞) : ℝ≥0∞)) ∂tapeLaw

/-- The expected running time `E[time of TriPPR]` on the instance `(G, s, t)`. -/
noncomputable def triExpTime {V : Type} [DecidableEq V] (α εr : ℝ) (G : Digraph V) (s t : V) :
    ℝ≥0∞ :=
  ∫⁻ ω, ((triTime G.oracle α εr s t ω : ℕ∞) : ℝ≥0∞) ∂tapeLaw

end PPRInstOpt.UnknownN


