-- Prove2me | Definitions.Def_NetBilinear_Supplement_Algorithm1
-- name    : NetBilinear_Supplement_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:44:04.145438+00:00
-- url     : https://prove2.me/theorems/b59e82a6-23c7-530a-b174-2fb396f92519
-- title:
--   Algorithm 1: deriving an EC&R assignment from a forest structure, as a nondeterministic labelling procedure
-- statement:
--   Algorithm 1 takes a network $G=(V,A)$, forest node sets $\tilde{\mathcal I}^j$ ($j\in M$), connection nodes $\tilde{\mathcal I}$, connection arcs $\tilde{\mathcal J}$, a class $l$ with base term $y_{j'}x_{i'}$, and a sign $\sigma$. Its **members** are the replicas $(v,j)$ of the nodes $v\in\tilde{\mathcal I}^j$, the connection nodes $v\in\tilde{\mathcal I}$ and the connection arcs $a\in\tilde{\mathcal J}$. A node in several of these sets gives distinct members. The algorithm labels members with signs; $\neg$ denotes the opposite sign.
--
--   1. **Start (lines 1–7).** Set $l(i')=\sigma$, and let $k$ be an endpoint of $i'$ in $\tilde{\mathcal I}^{j'}\cup\tilde{\mathcal I}$, or the arc $i'$ itself if $i'\in\tilde{\mathcal J}$. If $k=h(i')\in\tilde{\mathcal I}^{j'}$, $k=t(i')\in\tilde{\mathcal I}$ or $k=i'\in\tilde{\mathcal J}$, set $l(k)=\sigma$; if $k=t(i')\in\tilde{\mathcal I}^{j'}$ or $k=h(i')\in\tilde{\mathcal I}$, set $l(k)=\neg\sigma$. Then $D=\{k\}$.
--   2. **Loop (lines 8–46).** While $D\neq\emptyset$, select any $i\in D$ and give every unlabeled member $k$ that $i$ reaches a label, adding it to $D$:
--      - $i=(v,j)$: adjacent $(w,j)$ get $l(i)$, adjacent $w\in\tilde{\mathcal I}$ get $\neg l(i)$, an incident arc $k\in\tilde{\mathcal J}$ gets $l(i)$ if $v=t(k)$ and $\neg l(i)$ otherwise;
--      - $i=v\in\tilde{\mathcal I}$: the replicas $(v,j)$ get $l(i)$, adjacent $(w,j)$ get $\neg l(i)$, adjacent $w\in\tilde{\mathcal I}$ get $l(i)$, an incident arc $k$ gets $\neg l(i)$ if $v=t(k)$ and $l(i)$ otherwise;
--      - $i=a\in\tilde{\mathcal J}$: $(t(a),j)$ gets $l(i)$ and $(h(a),j)$ gets $\neg l(i)$ (every $j$), $t(a)\in\tilde{\mathcal I}$ gets $\neg l(i)$ and $h(a)\in\tilde{\mathcal I}$ gets $l(i)$.
--
--      Then remove $i$ from $D$.
--   3. **Output (lines 47–59).** $\mathcal I_j=\{v^{l(v,j)} : v\in\tilde{\mathcal I}^j\}$, $\bar{\mathcal I}=\{v^{l(v)} : v\in\tilde{\mathcal I}\}$, $\mathcal J=\{a\in\tilde{\mathcal J} : l(a)=+\}$ and $\bar{\mathcal J}=\{a\in\tilde{\mathcal J} : l(a)=-\}$.
--
--   A state $st$ (labelling and set $D$) is a **final state of Algorithm 1** when some run from a start state reaches it and $D=\emptyset$ there.
--
--   Theorem 3 states that the output of every final state is an EC&R assignment.
--
--   **Formalization Note** Line 9 ("select $i\in D$") is a free choice, so runs are modelled by a step relation, and a final state is any state reachable from a start state with $D=\emptyset$. Theorem 3 quantifies over all of them. Line 23 ("$k\in\tilde{\mathcal I}^j$ such that $k=i$") is read as the replica of $i$, and lines 38 and 41 treat the two endpoints separately. Labels are `Option Sign`, with `none` for unlabeled members. In the output, a member that is still unlabeled contributes no row (Theorem 3 also states that no member stays unlabeled).
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, Algorithm 1, p.20

import Mathlib
import Definitions.Def_NetBilinear_Network

namespace NetBilinear.Supplement

/-- **The members labelled by Algorithm 1** (arXiv:2302.14151v2, Algorithm 1, p.20, line 1):
the node `v` of the forest node set `Ĩ_j` (its replica in the parallel network `G^j`,
`node v j`), the connection node `v ∈ Ĩ` (`conn v`), and the connection arc `a ∈ J̃`
(`arc a`). A node lying in several `Ĩ_j` and in `Ĩ` gives distinct members: they stand for
distinct weighted constraints (its flow-balance row times `y_j`, and times `1 − Σ_j y_j`). -/
inductive Member (V A M : Type*)
  | node (v : V) (j : M)
  | conn (v : V)
  | arc (a : A)
  deriving DecidableEq

/-- **A state of Algorithm 1**: the (partial) labelling `l` of the members and the set `D` of
members still to be processed (arXiv:2302.14151v2, Algorithm 1, p.20, line 1). -/
structure State (V A M : Type*) where
  /-- `l(i)`: `none` while the member is unlabeled. -/
  lab : Member V A M → Option Sign
  /-- The set `D`. -/
  D : Set (Member V A M)

variable {V A M : Type*}

/-- **Membership**: `node v j` is a member when `v ∈ Ĩ_j`, `conn v` when `v ∈ Ĩ`, `arc a` when
`a ∈ J̃`. -/
def IsMember (It : M → Finset V) (Ic : Finset V) (Jc : Finset A) : Member V A M → Prop
  | .node v j => v ∈ It j
  | .conn v => v ∈ Ic
  | .arc a => a ∈ Jc

open Classical in
/-- **The label a processed member `i` (with label `s`) gives to a member `k`**, lines 10–44 of
Algorithm 1 (arXiv:2302.14151v2, p.20); `none` when `k` is not among the members `i` labels.
Adjacency is adjacency in `Ḡ`; `¬` is `Sign.flip`.
* `i ∈ Ĩ_j` (lines 10–21): a node `k ∈ Ĩ_j` (same `j`) adjacent to `i` gets `l(i)`; a node
  `k̄ ∈ Ĩ` adjacent to `i` gets `¬l(i)`; an arc `k ∈ J̃` incident to `i` gets `l(i)` if
  `i = t(k)`, else `¬l(i)`.
* `i ∈ Ĩ` (lines 22–36): the replica `k ∈ Ĩ_j` of `i` itself ("k = i", any `j`) gets `l(i)`; a
  node `k ∈ Ĩ_j` (any `j`) adjacent to `i` gets `¬l(i)`; a node `k̄ ∈ Ĩ` adjacent to `i` gets
  `l(i)`; an arc `k ∈ J̃` incident to `i` gets `¬l(i)` if `i = t(k)`, else `l(i)`.
* `i ∈ J̃` (lines 37–44): `t(i) ∈ Ĩ_j` gets `l(i)` and `h(i) ∈ Ĩ_j` gets `¬l(i)` (any `j`, each
  separately); `t(i) ∈ Ĩ` gets `¬l(i)` and `h(i) ∈ Ĩ` gets `l(i)`. -/
noncomputable def assign (G : Network V A) (It : M → Finset V) (Ic : Finset V) (Jc : Finset A) :
    Member V A M → Sign → Member V A M → Option Sign
  | .node v j, s, .node w j₂ =>
      if j₂ = j ∧ w ∈ It j ∧ G.underlying.Adj v w then some s else none
  | .node v _, s, .conn w => if w ∈ Ic ∧ G.underlying.Adj v w then some s.flip else none
  | .node v _, s, .arc a =>
      if a ∈ Jc ∧ G.tail a = v then some s
      else if a ∈ Jc ∧ G.head a = v then some s.flip else none
  | .conn v, s, .node w j =>
      if w ∈ It j ∧ w = v then some s
      else if w ∈ It j ∧ G.underlying.Adj v w then some s.flip else none
  | .conn v, s, .conn w => if w ∈ Ic ∧ G.underlying.Adj v w then some s else none
  | .conn v, s, .arc a =>
      if a ∈ Jc ∧ G.tail a = v then some s.flip
      else if a ∈ Jc ∧ G.head a = v then some s else none
  | .arc a, s, .node w j =>
      if w ∈ It j ∧ w = G.tail a then some s
      else if w ∈ It j ∧ w = G.head a then some s.flip else none
  | .arc a, s, .conn w =>
      if w ∈ Ic ∧ w = G.tail a then some s.flip
      else if w ∈ Ic ∧ w = G.head a then some s else none
  | .arc _, _, .arc _ => none

/-- **Lines 2–7 of Algorithm 1**: the first member `k` and its label `s`, for the class with
base term `y_{j'} x_{i'}` and sign `σ` (`l(i') = σ`, line 2). `k` is an endpoint of `i'` in
`Ĩ_{j'} ∪ Ĩ` or the arc `i'` itself when `i' ∈ J̃`:
* line 3–4: `k = h(i') ∈ Ĩ_{j'}`, `k = t(i') ∈ Ĩ` or `k = i' ∈ J̃` gets `l(i')`;
* line 5–6: `k = t(i') ∈ Ĩ_{j'}` or `k = h(i') ∈ Ĩ` gets `¬l(i')`. -/
def StartRule (G : Network V A) (It : M → Finset V) (Ic : Finset V) (Jc : Finset A) (i' : A)
    (j' : M) (σ : Sign) (k : Member V A M) (s : Sign) : Prop :=
  (k = .node (G.head i') j' ∧ G.head i' ∈ It j' ∧ s = σ) ∨
  (k = .conn (G.tail i') ∧ G.tail i' ∈ Ic ∧ s = σ) ∨
  (k = .arc i' ∧ i' ∈ Jc ∧ s = σ) ∨
  (k = .node (G.tail i') j' ∧ G.tail i' ∈ It j' ∧ s = σ.flip) ∨
  (k = .conn (G.head i') ∧ G.head i' ∈ Ic ∧ s = σ.flip)

/-- **The state after lines 1–7**: only `k` is labelled (with `s`), and `D = {k}`. -/
def InitState [DecidableEq V] [DecidableEq A] [DecidableEq M] (G : Network V A)
    (It : M → Finset V) (Ic : Finset V) (Jc : Finset A) (i' : A) (j' : M) (σ : Sign)
    (st : State V A M) : Prop :=
  ∃ k s, StartRule G It Ic Jc i' j' σ k s ∧
    st.lab = Function.update (fun _ => none) k (some s) ∧ st.D = {k}

/-- **One pass of the while loop, lines 9–45**: some `i ∈ D` is selected (line 9, a free
choice), every unlabeled member `k` that `i` labels (`assign`) receives its label and is added
to `D`, labelled members keep their labels, and `i` is removed from `D` (line 45). -/
def Step (G : Network V A) (It : M → Finset V) (Ic : Finset V) (Jc : Finset A)
    (st st' : State V A M) : Prop :=
  ∃ i ∈ st.D, ∃ s, st.lab i = some s ∧
    st'.lab = (fun k => match st.lab k with
      | some x => some x
      | none => assign G It Ic Jc i s k) ∧
    st'.D = (st.D \ {i}) ∪ {k | st.lab k = none ∧ (assign G It Ic Jc i s k).isSome}

/-- **Algorithm 1** (Khademnia & Davarnia, *Convexification of Bilinear Terms over Network
Polytopes*, arXiv:2302.14151v2, Algorithm 1, p.20, "Derive an EC&R assignment associated with a
forest structure"): `Algorithm1 G It Ic Jc i' j' σ st` says that `st` is the final state of a
run of lines 1–46, i.e. a state reached from an initial state (lines 1–7, `InitState`) by
finitely many passes of the while loop (`Step`) with `D = ∅` (the loop has terminated).

Inputs: the network `G`, the forest node sets `Ĩ_j = It j`, the connection node set
`Ĩ = Ic`, the connection arc set `J̃ = Jc`, the class `l` through `(i', j')` with
`A^l_{j'i'} = 1`, and the class sign `σ`.

**Formalization Note.** Line 9 ("select i ∈ D") is a free choice and line 2 may in principle
offer several `k`, so the algorithm is modelled as a nondeterministic procedure and `st`
ranges over the final states of all terminating runs. Line 1 labels the base arc `i'`
(written `{l}` in line 1) with `σ`; when `i' ∈ J̃` this is the label of the member `arc i'`
set in lines 3–4, otherwise that label is used only in lines 2–6. The output of lines 47–59 is
`alg1I`, `alg1Ibar`, `alg1J`, `alg1Jbar`. -/
def Algorithm1 [DecidableEq V] [DecidableEq A] [DecidableEq M] (G : Network V A)
    (It : M → Finset V) (Ic : Finset V) (Jc : Finset A) (i' : A) (j' : M) (σ : Sign)
    (st : State V A M) : Prop :=
  ∃ st₀, InitState G It Ic Jc i' j' σ st₀ ∧ Relation.ReflTransGen (Step G It Ic Jc) st₀ st ∧
    st.D = ∅

/-- **Lines 47–49**: `I_j = {i^{l(i)} : i ∈ Ĩ_j}` (the label of the replica of `i` in `G^j`). -/
def alg1I [DecidableEq V] (It : M → Finset V) (st : State V A M) (j : M) : Finset (V × Sign) :=
  (rowsWith .pos (It j) ∪ rowsWith .neg (It j)).filter fun p => st.lab (.node p.1 j) = some p.2

/-- **Lines 50–52**: `Ī = {i^{l(i)} : i ∈ Ĩ}`. -/
def alg1Ibar [DecidableEq V] (Ic : Finset V) (st : State V A M) : Finset (V × Sign) :=
  (rowsWith .pos Ic ∪ rowsWith .neg Ic).filter fun p => st.lab (.conn p.1) = some p.2

/-- **Lines 53–59, `J`**: the arcs `i ∈ J̃` with `l(i) = +`. -/
def alg1J (Jc : Finset A) (st : State V A M) : Finset A :=
  Jc.filter fun a => st.lab (.arc a) = some .pos

/-- **Lines 53–59, `J̄`**: the arcs `i ∈ J̃` with `l(i) = −`. -/
def alg1Jbar (Jc : Finset A) (st : State V A M) : Finset A :=
  Jc.filter fun a => st.lab (.arc a) = some .neg

end NetBilinear.Supplement


