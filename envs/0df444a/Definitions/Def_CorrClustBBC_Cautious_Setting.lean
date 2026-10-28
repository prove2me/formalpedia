-- Prove2me | Definitions.Def_CorrClustBBC_Cautious_Setting
-- name    : CorrClustBBC_Cautious_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:48.831126+00:00
-- url     : https://prove2.me/theorems/e1cd6ee3-091a-40c6-9641-82a7690199f4
-- title:
--   §2 and §4, pp. 91–99 — ±-labelled complete graphs, N⁺, mistakes, δ-good/δ-clean sets (Definition 1), erroneous-triangle packings, and Algorithm Cautious
-- statement:
--   This file fixes the objects of Bansal, Blum and Chawla's analysis of correlation clustering (§2 and §4).
--
--   **Labelled graph.** Let $V$ be a finite set of vertices. The complete graph on $V$ carries a label $e(u,v)\in\{+,-\}$ on every pair of distinct vertices. It is encoded by a simple graph $G$ on $V$: $u$ and $v$ are adjacent in $G$ exactly when $e(u,v)=+$, and every other pair of distinct vertices is labelled $-$.
--
--   **Current vertex set and positive neighbourhood.** Algorithm Cautious deletes the clusters it has produced, so its notions are taken in the graph induced on the set $R\subseteq V$ of vertices still present. For $v$ and $R$,
--   $$N^+_R(v)=\{v\}\cup\{u\in R : e(u,v)=+\}.$$
--   The vertex $v$ itself always belongs to $N^+_R(v)$. The paper's $N^+(v)$ is the case $R=V$.
--
--   **Good, bad and clean (Definition 1).** For a real $\delta$ and $C\subseteq R$, a vertex $v$ is *$\delta$-good* with respect to $C$ (in $R$) if
--   $$|N^+_R(v)\cap C|\ \ge\ (1-\delta)|C| \qquad\text{and}\qquad |N^+_R(v)\cap(R\setminus C)|\ \le\ \delta|C|,$$
--   and *$\delta$-bad* otherwise. The set $C$ is *$\delta$-clean* if every $v\in C$ is $\delta$-good with respect to $C$.
--
--   **Clusterings and mistakes.** A clustering is a partition $D$ of $V$; $D(v)$ denotes the cluster of $v$. More generally, for a "same cluster" relation $r$ on $V$, an unordered pair $\{u,v\}$ with $u\ne v$ is a *mistake* if $e(u,v)=+$ and $u,v$ are not together, or $e(u,v)=-$ and $u,v$ are together. The first kind is a *positive* mistake, the second a *negative* mistake. Then $m_r$ is the number of mistakes, and for a set $S$ the *external* mistakes with respect to $S$ are the mistakes with at least one endpoint in $S$. For a clustering $D$, $S(D)$ is the set of vertices whose cluster is a singleton; $D$ has *$\delta$-clean non-singleton clusters* if every cluster with at least two vertices is $\delta$-clean in $G$ (that is, with $R=V$).
--
--   **Erroneous triangles and fractional packings.** A triangle $\{a,b,c\}$ of three distinct vertices is *erroneous* if it has two positive edges and one negative edge. A *fractional packing* of erroneous triangles assigns a weight $w(T)\ge 0$ to every vertex set $T$, positive only on erroneous triangles, such that for every pair $u\ne v$
--   $$\sum_{T\ni u,v} w(T)\ \le\ 1 .$$
--   Its weight is $\sum_T w(T)$.
--
--   **Algorithm Cautious** (p. 97), with the standing constant $\delta=1/44$:
--   1. Pick an arbitrary remaining vertex $v$. (a) Let $A(v)=N^+_R(v)$. (b) *Removal step:* while some $x\in A(v)$ is $3\delta$-bad with respect to $A(v)$, delete such an $x$; call the result $A'$. (c) *Addition step:* add to $A'$ every vertex of $R$ that is $7\delta$-good with respect to $A'$, all at once; the result is $A(v)$.
--   2. If $A(v)\ne\emptyset$, delete it from $R$, record it as the next cluster and repeat. The run stops when no vertex is left, or when every remaining vertex, tried as $v$, has produced $\emptyset$; the remaining vertices $Z$ are then output as singletons.
--
--   Since step 1 picks an arbitrary vertex and step 1(b) removes an arbitrary bad vertex, the algorithm is nondeterministic. Its runs are described by a relation: a run from $R$ records the list of triples $(A'_i, A_i, R_i)$ — the removal result, the cluster, and the vertex set it was formed in — and the final singleton set $Z$. The output clustering puts $u\ne v$ together exactly when both lie in one recorded cluster $A_i$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The labelled complete graph is a `SimpleGraph V` with decidable adjacency on a `Fintype` with decidable equality; $V$ may be empty. Mistakes are counted over unordered pairs (`Sym2 V`, off the diagonal). Clusterings are `Setoid V`, and `classOf D v` is the cluster of $v$. Goodness compares real casts of cardinalities with real multiples of $\delta$, and $\delta=1/44$ is the real constant `δ44`. The removal step is the inductive relation `Removes` (every removal order), the addition step is `addStep`, a run is the inductive relation `Run` with constructors `nil`, `cluster` and `stop`, and the output clustering is `sameCluster`.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 91 (N⁺, N⁻), p. 92 (mistakes, m_C), p. 94 (erroneous triangles, fractional packing), pp. 94–95 (Definition 1), p. 97 (δ = 1/44, Algorithm Cautious, footnote 3 on p. 112), p. 99 (internal/external mistakes)

import Mathlib

namespace CorrClustBBC.Cautious

open Finset Classical

/-! Bansal, Blum, Chawla, *Correlation Clustering*, Machine Learning 56 (2004) 89–113.
The complete graph on `V` with edges labelled `+`/`−` is encoded by a simple graph `G`:
`G.Adj u v` means `e(u, v) = +`; every other pair of distinct vertices is labelled `−` (p. 91). -/

/-- The standing constant `δ = 1/44` of §4 (p. 97). -/
noncomputable abbrev δ44 : ℝ := 1 / 44

/-- `N⁺(v) = {v} ∪ {u : e(u, v) = +}` (p. 91), in the graph induced on the current vertex set `R`. -/
def posNbhd {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (v : V) : Finset V :=
  insert v (R.filter (G.Adj v))

/-- Definition 1 (pp. 94–95), relative to the current vertex set `R`: `v` is `δ`-good w.r.t. `C` if
`|N⁺(v) ∩ C| ≥ (1 − δ)|C|` and `|N⁺(v) ∩ (R \ C)| ≤ δ|C|`. -/
def IsGood {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (δ : ℝ) (C : Finset V) (v : V) : Prop :=
  (1 - δ) * ((C.card : ℕ) : ℝ) ≤ (((posNbhd G R v ∩ C).card : ℕ) : ℝ) ∧
    (((posNbhd G R v ∩ (R \ C)).card : ℕ) : ℝ) ≤ δ * ((C.card : ℕ) : ℝ)

/-- Definition 1 (p. 95): `C` is `δ`-clean if every `v ∈ C` is `δ`-good w.r.t. `C`. -/
def IsClean {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (δ : ℝ) (C : Finset V) : Prop :=
  ∀ v ∈ C, IsGood G R δ C v

/-- The pair `{u, v}` (`u ≠ v`) is a mistake of the same-cluster relation `r` (p. 92):
`e(u, v) = +` and `u, v` are separated, or `e(u, v) = −` and `u, v` are together. -/
def IsMistake {V : Type*} (G : SimpleGraph V) (r : V → V → Prop) (u v : V) : Prop :=
  u ≠ v ∧ ((G.Adj u v ∧ ¬ r u v) ∨ (¬ G.Adj u v ∧ r u v))

/-- `m_C`: the number of unordered pairs `{u, v}` that are mistakes of `r` (p. 92). -/
noncomputable def mistakes {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (r : V → V → Prop) : ℕ :=
  ((Finset.univ : Finset (Sym2 V)).filter
    (fun e => ∃ u v, e = s(u, v) ∧ IsMistake G r u v)).card

/-- The number of positive mistakes (p. 92): `+` pairs `{u, v}`, `u ≠ v`, separated by `r`. -/
noncomputable def posMistakes {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (r : V → V → Prop) : ℕ :=
  ((Finset.univ : Finset (Sym2 V)).filter
    (fun e => ∃ u v, e = s(u, v) ∧ u ≠ v ∧ G.Adj u v ∧ ¬ r u v)).card

/-- The number of negative mistakes (p. 92): `−` pairs `{u, v}`, `u ≠ v`, put together by `r`. -/
noncomputable def negMistakes {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (r : V → V → Prop) : ℕ :=
  ((Finset.univ : Finset (Sym2 V)).filter
    (fun e => ∃ u v, e = s(u, v) ∧ u ≠ v ∧ ¬ G.Adj u v ∧ r u v)).card

/-- External mistakes w.r.t. a vertex set `S` (p. 99): mistakes with at least one endpoint in `S`. -/
noncomputable def extMistakes {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (r : V → V → Prop) (S : Finset V) : ℕ :=
  ((Finset.univ : Finset (Sym2 V)).filter
    (fun e => ∃ u v, e = s(u, v) ∧ IsMistake G r u v ∧ (u ∈ S ∨ v ∈ S))).card

/-- The cluster of `v` in a clustering `D` (a partition of `V`, given as a setoid). -/
noncomputable def classOf {V : Type*} [Fintype V] (D : Setoid V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => D.r v u)

/-- The set `S` of vertices that form singleton clusters of `D`. -/
noncomputable def singletonsOf {V : Type*} [Fintype V] (D : Setoid V) : Finset V :=
  Finset.univ.filter (fun v => (classOf D v).card = 1)

/-- Every non-singleton cluster of `D` is `δ`-clean in `G` (the property of `OPT′`, p. 96). -/
def NonsingletonClean {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (δ : ℝ) (D : Setoid V) : Prop :=
  ∀ v, 2 ≤ (classOf D v).card → IsClean G Finset.univ δ (classOf D v)

/-- An erroneous triangle (p. 94): three distinct vertices with two positive edges `ab`, `ac`
and one negative edge `bc`. -/
def IsErroneous {V : Type*} [DecidableEq V] (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ a b c, T = {a, b, c} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj a b ∧ G.Adj a c ∧ ¬ G.Adj b c

/-- A fractional packing of erroneous triangles (p. 94): nonnegative weights on vertex sets,
positive only on erroneous triangles, such that the triangles containing any edge `{u, v}`
carry total weight at most `1`. Its weight is `∑ T, w T`. -/
def IsFracPacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : Finset V → ℝ) : Prop :=
  (∀ T, 0 ≤ w T) ∧ (∀ T, w T ≠ 0 → IsErroneous G T) ∧
    ∀ u v, u ≠ v → ∑ T ∈ Finset.univ.filter (fun T : Finset V => u ∈ T ∧ v ∈ T), w T ≤ 1

/-- Step 1(b) of Algorithm Cautious (p. 97), every removal order: `Removes G R A B` holds when
repeatedly deleting from `A` some vertex that is `3δ`-bad w.r.t. the current `A` (in the current
vertex set `R`) can end, with no `3δ`-bad vertex left, at `B`. -/
inductive Removes {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (R : Finset V) : Finset V → Finset V → Prop
  | done {A : Finset V} : (∀ x ∈ A, IsGood G R (3 * δ44) A x) → Removes G R A A
  | drop {A B : Finset V} {x : V} : x ∈ A → ¬ IsGood G R (3 * δ44) A x →
      Removes G R (A.erase x) B → Removes G R A B

/-- Step 1(c) of Algorithm Cautious (p. 97): `A(v) = A′ ∪ Y`, `Y` the vertices of the current
vertex set `R` that are `7δ`-good w.r.t. the removal result `A′`. -/
noncomputable def addStep {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (R A' : Finset V) : Finset V :=
  A' ∪ R.filter (fun y => IsGood G R (7 * δ44) A' y)

/-- The runs of Algorithm Cautious (p. 97). `Run G R L Z`: started on the vertex set `R`, the
algorithm produces the clusters recorded in `L` in order, each as `(A′ᵢ, Aᵢ, Rᵢ)` (removal
result, cluster, vertex set it was formed in), and ends with the singleton set `Z`.
* `nil`: no vertices are left.
* `cluster`: an arbitrary vertex `v ∈ R` is picked, `A(v) = N⁺(v)` is reduced by step 1(b) to `A′`,
  step 1(c) gives `A = addStep A′`, which is nonempty, and `A` is deleted (step 2).
* `stop`: every remaining vertex, picked as `v`, has an execution of steps 1(a)–(c) producing the
  empty set; the remaining vertices are output as singletons. -/
inductive Run {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V → List (Finset V × Finset V × Finset V) → Finset V → Prop
  | nil : Run G ∅ [] ∅
  | cluster {R A' A : Finset V} {L : List (Finset V × Finset V × Finset V)} {Z : Finset V}
      {v : V} : v ∈ R → Removes G R (posNbhd G R v) A' → A = addStep G R A' → A.Nonempty →
      Run G (R \ A) L Z → Run G R ((A', A, R) :: L) Z
  | stop {R : Finset V} : R.Nonempty →
      (∀ v ∈ R, ∃ A', Removes G R (posNbhd G R v) A' ∧ addStep G R A' = ∅) → Run G R [] R

/-- The clustering output by a run with cluster list `L`: `u, v` are together iff `u = v` or both
lie in the same produced cluster `Aᵢ` (every vertex of `Z` is a singleton). -/
def sameCluster {V : Type*} (L : List (Finset V × Finset V × Finset V)) (u v : V) : Prop :=
  u = v ∨ ∃ p ∈ L, u ∈ p.2.1 ∧ v ∈ p.2.1

end CorrClustBBC.Cautious


