-- Prove2me | Definitions.Def_OnlineColoringKYY_Supplement_cliqueFree
-- name    : OnlineColoringKYY_Supplement_cliqueFree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:08:54.336745+00:00
-- url     : https://prove2.me/theorems/c3569192-0d8d-4df7-b3c4-e9efb88b22e8
-- title:
--   Online object coloring (Algorithm 3), CliqueFree$(r)$ (Algorithm 4) and its restart on $L$ vertices (Corollary 6.5)
-- statement:
--   The building blocks of Part A of Section 6.
--
--   1. **Colors with disjoint palettes.** A color is a pair (address of the instance that issued it, local color). Distinct instances have distinct addresses, so they use disjoint sets of colors.
--   2. **The sequence of Lemma 6.4.** For an integer $A$, $n_2 = 2A^2$ and $n_r = 6A^2\cdot\{6r\,(n_{r-1})^{r-1}\}^{6A^2}$ for $r \ge 3$.
--   3. **Cliques.** $\mathrm{cliques}_r(S)$ is the set of $r$-element cliques contained in $S$; $S$ is $r$-clique-free iff it is empty.
--   4. **Arbitrary choices.** A resolver supplies the choices the paper leaves open: the color $c$ of Algorithm 3, step (1); the $(M+1)$-clique output by LOC$'(k)$ for $k \le M$; the clique $\mathrm{adj}(v) \in \mathcal C(v)$ of Section 6.7; the instance $I_{i,j}$ of Algorithm 6, line 5. It is valid if it always returns one of the offered options.
--   5. **Algorithm 3** (online object coloring, parameter $\mu \ge 1$). Keep sets $X_1, \dots, X_t$. When a set $A_i$ arrives: if some $c \le t$ has $|X_c \cap A_i| \ge |X_c|/(2\mu)$, give $A_i$ such a color $c$ and set $X_c \leftarrow X_c \cap A_i$; otherwise give it color $t+1$, set $X_{t+1} \leftarrow A_i \setminus (X_1 \cup \dots \cup X_t)$ and $t \leftarrow t+1$.
--   6. **Algorithm 4, CliqueFree$(r)$.** For $r = 2$ every vertex gets the same color. For $r \ge 3$, keep bins $B_1, B_2, \dots$, each colored by its own instance of CliqueFree$(r-1)$, and one instance of Algorithm 3 with $\mu = 3r\,(n_{r-1})^{r-1}$; let $J = n_r/(3r\,n_{r-1})$. For an arriving $v$, let $j$ be the smallest index with $|B_j| < n_{r-1}$ and $G[B_j \cup \{v\}]$ $(r-1)$-clique-free. If $B_j = \emptyset$ and exactly $J$ bins have size between $1$ and $n_{r-1}-1$, present $\mathrm{CLIQUE}(N_B(v))$, the $(r-2)$-cliques inside one bin all of whose vertices are adjacent to $v$, to Algorithm 3 and color $v$ with the color it assigns. Otherwise put $v$ into $B_j$ and color it with the instance of $B_j$.
--   7. **Corollary 6.5's algorithm.** CliqueFree$(A+1)$ on a stream of vertices: Algorithm 4 for $n_{A+1}$ vertices, restarted with a fresh palette after every $n_{A+1}$ vertices. In Section 6, $A = M$.
--
--   These are the subroutines of the LOC algorithm of Theorem 6.26.
--
--   **Formalization Note** Vertices are natural numbers and the graph is given as the adjacency of the arrived vertices. Bins are stored in order of creation, and only nonempty bins are stored, so "$B_j = \emptyset$" means that $j$ is a new bin. Values of the sequence at $r = 0, 1$ and of CliqueFree$(r)$ for $r < 2$ are never used.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 6.1, Lemma 6.3 and Algorithm 3, printed pp.22–23 (PDF pp.24–25); Lemma 6.4 and Algorithm 4, printed pp.24–25 (PDF pp.26–27); Corollary 6.5, printed p.26 (PDF p.28)

import Mathlib

set_option autoImplicit false

namespace OnlineColoringKYY.Supplement

open Classical

/-! Section 6.1–6.2 of Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios
Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256
3d1eeea6…): online object coloring (Algorithm 3), the recursive algorithm CliqueFree(r)
(Algorithm 4, Lemma 6.4) and its restarted version on `L` vertices (Corollary 6.5). -/

/-- A **color of the Section 6 algorithm**: the address of the (sub-)instance that issued it,
a list of natural numbers, together with that instance's own color.

**Formalization Note** Every sub-instance has a unique address (its parent's address followed by
a tag of exactly three numbers, distinct among the parent's children), so instances with distinct
addresses have disjoint palettes. This realizes the paper's repeated "we use disjoint colors for
different bins / instances" (pp.24, 30, 31, 33). The number of colors used is the cardinality of
the set of colors, which does not depend on how colors are named. -/
abbrev Color : Type := List ℕ × ℕ

/-- The sequence `n_2, n_3, …` of Lemma 6.4 (printed p.24 = PDF p.26) with parameter `A`:
`n_2 = 2A²` and `n_r = 6A² · {6r (n_{r−1})^{r−1}}^{6A²}` for `r ≥ 3`.

**Formalization Note** The values at `r = 0, 1` are not used and are set to `0`. -/
def nSeq (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 2 * A ^ 2
  | (q + 3) => 6 * A ^ 2 * (6 * (q + 3) * (nSeq A (q + 2)) ^ (q + 2)) ^ (6 * A ^ 2)

/-- `s` is a **clique** for the adjacency relation `Adj`: any two distinct elements are
adjacent. -/
def IsCliqueSet (Adj : ℕ → ℕ → Prop) (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Adj a b

/-- The set of `r`-cliques (cliques of exactly `r` vertices) of `Adj` contained in `S`. A set `S`
is `r`-clique-free iff this set is empty. -/
noncomputable def cliquesIn (Adj : ℕ → ℕ → Prop) (r : ℕ) (S : Finset ℕ) : Finset (Finset ℕ) :=
  S.powerset.filter (fun s => s.card = r ∧ IsCliqueSet Adj s)

/-- The **choices the paper leaves arbitrary** in Section 6, as functions of the address of the
instance making the choice, the arriving (or certificate) vertex, and the set of admissible
options:

* `objColor`: Algorithm 3, line 3 / step (1) on p.23: "we choose any such `c`";
* `clique`: Section 6.6, `k ≤ M` case (p.31): which `(M+1)`-clique is output as the certificate;
* `adj`: Section 6.7 (p.32): "`adj(v) ∈ 𝒞(v)` be an arbitrarily chosen clique";
* `inst`: Algorithm 6, line 5 (p.35): which non-terminated instance `I_{i,j}` colors `v`.

**Formalization Note** The theorem quantifies over every resolver that always returns an
admissible option (`Resolver.Valid`). The resolver is quantified after the input graph, so it may
depend on the whole input; this covers every online selection rule. -/
structure Resolver where
  objColor : List ℕ → ℕ → Finset ℕ → ℕ
  clique : List ℕ → ℕ → Finset (Finset ℕ) → Finset ℕ
  adj : List ℕ → ℕ → Finset (Finset ℕ) → Finset ℕ
  inst : List ℕ → ℕ → Finset (ℕ × ℕ) → ℕ × ℕ

/-- A resolver is **valid** if each choice is one of the options offered, whenever an option
exists. -/
def Resolver.Valid (R : Resolver) : Prop :=
  (∀ a v S, S.Nonempty → R.objColor a v S ∈ S) ∧
  (∀ a v S, S.Nonempty → R.clique a v S ∈ S) ∧
  (∀ a v S, S.Nonempty → R.adj a v S ∈ S) ∧
  (∀ a v S, S.Nonempty → R.inst a v S ∈ S)

/-- One step of **Algorithm 3** (online object coloring, proof of Lemma 6.3, printed p.23 = PDF
p.25) with parameter `μ ≥ 1`. The state is the list `X_1, …, X_t` (entry `c − 1` is `X_c`); the
arriving set is `Aset`; `pick` resolves "choose any such `c`". Returns the new list and the color
`c ∈ {1, 2, …}` assigned to `Aset`.

1. If some `c ∈ {1, …, t}` has `|X_c ∩ A_i| ≥ |X_c|/(2μ)`, assign the chosen such `c` and set
   `X_c ← X_c ∩ A_i`.
2. Otherwise assign `t + 1` and set `X_{t+1} ← A_i \ (X_1 ∪ ⋯ ∪ X_t)`. -/
noncomputable def objStep (μ : ℝ) (pick : Finset ℕ → ℕ) (X : List (Finset (Finset ℕ)))
    (Aset : Finset (Finset ℕ)) : List (Finset (Finset ℕ)) × ℕ :=
  let cands : Finset ℕ := (Finset.Icc 1 X.length).filter
    (fun c => (((X.getD (c - 1) ∅) ∩ Aset).card : ℝ) ≥ ((X.getD (c - 1) ∅).card : ℝ) / (2 * μ))
  if cands.Nonempty then
    let c := pick cands
    (X.set (c - 1) ((X.getD (c - 1) ∅) ∩ Aset), c)
  else
    (X ++ [Aset \ X.foldr (· ∪ ·) ∅], X.length + 1)

/-- The state of an instance of **CliqueFree(r)** (Algorithm 4): the nonempty bins
`B_1, B_2, …` in order of creation, each with the state of its CliqueFree(r − 1) instance, and the
list `X_1, …, X_t` of its online object coloring instance. -/
inductive CFState where
  | mk (bins : List (Finset ℕ × CFState)) (obj : List (Finset (Finset ℕ))) : CFState

instance : Inhabited CFState := ⟨CFState.mk [] []⟩

/-- One step of **Algorithm 4, CliqueFree(r)** (Kawarabayashi–Yoneda–Yoneda, STOC 2027 submission
(manuscript sha256 3d1eeea6…), Section 6.2, Lemma 6.4 and Algorithm 4, printed pp.24–25 = PDF
pp.26–27), with parameter `A` for the sequence `n_r = nSeq A r`. The arriving vertex is `v`, the
adjacency of the arrived vertices is `Adj`, the instance's address is `addr`. Returns the new
state and the color of `v`.

* `r = 2`: the graph has no edges; every vertex gets the same color.
* `r ≥ 3`: let `j` be the smallest index with `|B_j| < n_{r−1}` and `G[B_j ∪ {v}]`
  `(r−1)`-clique-free (an index past the existing bins is a new, empty bin). If `B_j = ∅` and
  exactly `J = n_r/(3r·n_{r−1})` bins are incomplete (`1 ≤ |B_ℓ| < n_{r−1}`), present
  `CLIQUE(N_B(v))`, the `(r−2)`-cliques inside one bin all of whose vertices are adjacent to `v`,
  to the object coloring instance with `μ = 3r·(n_{r−1})^{r−1}`, and color `v` with its color.
  Otherwise put `v` into `B_j` and color it with the CliqueFree(r − 1) instance of `B_j`.

**Formalization Note** Bins, object coloring and sub-instances get disjoint palettes through
their addresses (tags `[0, j, 0]` for bin `j`, `[1, 0, 0]` for object coloring). The values for
`r < 2` are not used. `J` is computed by natural-number division; the quotient is exact (p.25,
"note that `J` is an integer"). -/
noncomputable def cfStep (A : ℕ) (R : Resolver) (Adj : ℕ → ℕ → Prop) (v : ℕ) :
    ℕ → List ℕ → CFState → CFState × Color
  | 0, addr, s => (s, (addr, 0))
  | 1, addr, s => (s, (addr, 0))
  | 2, addr, s => (s, (addr, 0))
  | (q + 3), addr, CFState.mk bins obj =>
    let cap : ℕ := nSeq A (q + 2)
    let J : ℕ := nSeq A (q + 3) / (3 * (q + 3) * nSeq A (q + 2))
    let μ : ℝ := 3 * ((q + 3 : ℕ) : ℝ) * ((nSeq A (q + 2) : ℕ) : ℝ) ^ (q + 2)
    let ok : ℕ → Prop := fun j =>
      (bins.getD j (∅, default)).1.card < cap ∧
        cliquesIn Adj (q + 2) (insert v (bins.getD j (∅, default)).1) = ∅
    have hex : ∃ j, (j < bins.length ∧ ok j) ∨ j = bins.length := ⟨bins.length, Or.inr rfl⟩
    let j : ℕ := Nat.find hex
    let incomplete : ℕ := (bins.filter (fun b => 1 ≤ b.1.card ∧ b.1.card < cap)).length
    if j = bins.length ∧ incomplete = J then
      let Aset : Finset (Finset ℕ) := bins.foldr
        (fun b acc => acc ∪ cliquesIn Adj (q + 1) (b.1.filter (fun u => Adj v u))) ∅
      let res := objStep μ (R.objColor (addr ++ [1, 0, 0]) v) obj Aset
      (CFState.mk bins res.1, (addr ++ [1, 0, 0], res.2))
    else
      let b := bins.getD j (∅, default)
      let res := cfStep A R Adj v (q + 2) (addr ++ [0, j, 0]) b.2
      let bins' := if j < bins.length then bins.set j (insert v b.1, res.1)
        else bins ++ [({v}, res.1)]
      (CFState.mk bins' obj, res.2)

/-- One step of the **algorithm of Corollary 6.5** (printed p.26 = PDF p.28): CliqueFree(A + 1)
run on a stream of vertices by Algorithm 4 for `n_{A+1}` vertices, restarted with a fresh palette
after every `n_{A+1}` vertices. The state is the number of vertices processed so far and the
state of the current block's Algorithm 4 instance. In the paper `A = M`.

**Formalization Note** Block `b` (vertices `b·n_{A+1}`, …, `(b+1)·n_{A+1} − 1` of the stream) has
address tag `[7, b, 0]`. -/
noncomputable def c65Step (A : ℕ) (R : Resolver) (Adj : ℕ → ℕ → Prop) (v : ℕ) (addr : List ℕ) :
    ℕ × CFState → (ℕ × CFState) × Color
  | (cnt, s) =>
    let blk := cnt / nSeq A (A + 1)
    let s0 := if cnt % nSeq A (A + 1) = 0 then CFState.mk [] [] else s
    let res := cfStep A R Adj v (A + 1) (addr ++ [7, blk, 0]) s0
    ((cnt + 1, res.1), res.2)

end OnlineColoringKYY.Supplement


