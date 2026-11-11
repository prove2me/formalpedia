-- Prove2me | Definitions.Def_PMEdits_Main_Strings
-- name    : PMEdits_Main_Strings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:47:14.709353+00:00
-- url     : https://prove2.me/theorems/eaa6298b-8e81-424e-ae61-d36fd4d99f64
-- title:
--   Strings, fragments, $Q^\infty$, primitivity, alignments and their costs, edit distance, $\mathrm{Occ}_k$, suffix distances $d^\downarrow$ and breakpoint representations
-- statement:
--   Strings are lists of natural numbers indexed from $0$; $T[a..b)$ ($0\le a\le b\le|T|$) is the fragment spelling $T[a]\cdots T[b-1]$ (`frag`). For a nonempty $Q$ of length $q$, $Q^\infty[i]=Q[i\bmod q]$ for all $i\in\mathbb Z$ (`qinf`); $Q$ is **primitive** if $Q\ne U^e$ for every string $U$ and $e\ge2$. A string and $Q^\infty$ are both read as maps $\mathbb Z\to\mathbb N$, and fragments $X[a..b)$ by their integer endpoints (`spell`).
--
--   The **alignment graph** $\mathrm{AG}(X[x..x'),Y[y..y'))$ has vertex set $[x..x']\times[y..y']$ (positions of the underlying strings), deletion edges $(i,j)\to(i+1,j)$ and insertion edges $(i,j)\to(i,j+1)$ of cost $1$, and diagonal edges $(i,j)\to(i+1,j+1)$ of cost $0$ if $X[i]=Y[j]$ and $1$ otherwise. An **alignment** $A:X[x..x')\rightsquigarrow Y[y..y')$ is a path from $(x,y)$ to $(x',y')$, recorded as its list of vertices (`IsAlignment`); $\mathrm{cost}(A)$ is the sum of its edge costs, its **edits** being the edges of positive cost; `segCost` is the cost of the subpath between two vertex indices. $\mathrm{ed}(U,V)$ is the minimum cost of an alignment $U\rightsquigarrow V$ (unit-cost Levenshtein distance), and $\mathrm{ed}(X,{*}Q{*})$ the minimum of $\mathrm{ed}(X,Q^\infty[a..b))$ over $a\le b$.
--
--   $$\mathrm{Occ}_k(P,T)=\{s\in[0..|T|]:\exists e\in[s..|T|],\ \mathrm{ed}(P,T[s..e))\le k\}.$$
--   $d^\downarrow(p,t)$ is the distance in $\mathrm{AG}(P,T)$ from $(p,t)$ to the bottom row $\{|P|\}\times[0..|T|]$ (Definition 5.6), i.e. the minimum cost of an alignment $P[p..|P|)\rightsquigarrow T[t..e)$, $e\in[t..|T|]$.
--
--   Fragments $F=X[s..s')$, $G=Y[t..t')$ are **aligned** by $A$, $F\sim_A G$, if $(s,t)$ and $(s',t')$ are vertices of $A$; then $\mathrm{ed}_A(F,G)$ is the cost of the subpath between them (Definition 3.6). The **breakpoint representation** $\mathrm{bp}(A)$ (Definition 3.8) is the entry $((x,\varepsilon),(y,\varepsilon))$, then for every edit in path order with tail $(\bar x,\bar y)$ the entry $((\bar x,X[\bar x]),(\bar y,\varepsilon))$ (deletion), $((\bar x,\varepsilon),(\bar y,Y[\bar y]))$ (insertion) or $((\bar x,X[\bar x]),(\bar y,Y[\bar y]))$ (substitution), then $((x',\varepsilon),(y',\varepsilon))$; $\varepsilon$ is `none`.
--
--   $\lg z=\log_2\max(2,z)$. `prog a δ ℓ` is the progression $\{a+j\delta:j<\ell\}$; `DisjointProgRep δ L S` says the list $L$ of pairs $(a_i,\ell_i)$, all $\ell_i\ge1$, gives pairwise disjoint progressions of difference $\delta$ with union $S$; `ProgUnionRep` drops disjointness.
--
--   **Formalization Note.** The minima defining `ed`, `edStar` and `dDown` are `sInf` of nonempty sets of naturals. The value of `chars S` outside $[0..|S|)$ is never read by an edge of an alignment graph of a fragment of $S$.
-- source:
--   Kociumaka, Pattern Matching with Edits in Õ(n + k³ · n/m) Time, STOC 2027 submission (PDF sha256 98afea8f…), footnotes 1–2 and problem statement, p. 1 (PDF 4); §3.1–§3.4, pp. 13–16 (PDF 16–19), Definitions 3.1, 3.2, 3.4, 3.6, 3.8; Definition 5.6, p. 25 (PDF 28)

import Mathlib

set_option autoImplicit false

namespace PMEdits.Main

/-!
# Strings, fragments, alignment graphs, edit distance and `Occ_k`

Kociumaka, *Pattern Matching with Edits in Õ(n + k³ · n/m) Time* (STOC 2027 submission, PDF sha256
98afea8f…): problem statement and footnotes 1–2, p. 1 (PDF 4); §3.1–§3.4, pp. 13–17 (PDF 16–20):
Definitions 3.1, 3.2, 3.4, 3.6, 3.8.

**Formalization Note.**
* A string is a `List ℕ` (characters are natural numbers), indexed from `0`.
* Positions of fragments are integers. A string `S` and a bi-infinite string `Q∞` are both read as
  maps `ℤ → ℕ` (`chars S`, `qinf Q`); a fragment `S[a..b)` is given by its endpoints, and the
  alignment-graph edges only ever read positions inside the fragment, so the value of `chars S`
  outside `[0..|S|)` is never used.
* An alignment `F ⇝ G` (Definition 3.4) is a directed path in `AG(F, G)`, recorded as the list of
  its vertices in path order: it starts at `(x, y)`, ends at `(x', y')`, and each step is a
  deletion `(i, j) → (i+1, j)`, an insertion `(i, j) → (i, j+1)` or a diagonal
  `(i, j) → (i+1, j+1)` edge. Such a path stays in `[x..x'] × [y..y']`.
* `ed` is the minimum cost of an alignment (unit-cost Levenshtein distance), `ed(F, G) =
  dist_{AG(F,G)}((x, y), (x', y'))`; the minimum is over a nonempty set (§3.3).
* `lg z = log₂ (max 2 z)` (footnote 2 and §3.1).
-/

/-- `lg z := log₂(max(2, z))` (footnote 2, p. 1; §3.1). -/
noncomputable def lg (z : ℝ) : ℝ := Real.logb 2 (max 2 z)

/-- A string read as a map on integer positions: `chars S i = S[i]` for `i ∈ [0..|S|)`. -/
def chars (S : List ℕ) : ℤ → ℕ := fun i => S.getD i.toNat 0

/-- The bi-infinite string `Q∞`: `Q∞[i] = Q[i mod q]` for every `i ∈ ℤ` (Definition 3.1). -/
def qinf (Q : List ℕ) : ℤ → ℕ := fun i => Q.getD (i % (Q.length : ℤ)).toNat 0

/-- The string spelled by the fragment `X[a..b)` of a (bi-infinite) string `X : ℤ → ℕ`. -/
def spell (X : ℤ → ℕ) (a b : ℤ) : List ℕ :=
  (List.range (b - a).toNat).map (fun i => X (a + i))

/-- The fragment `T[a..b)` of a string, `0 ≤ a ≤ b ≤ |T|`, as the string it spells. -/
def frag (T : List ℕ) (a b : ℕ) : List ℕ := (T.drop a).take (b - a)

/-- `Q` is primitive: nonempty and `Q ≠ U^e` for every string `U` and every `e ≥ 2`
(Definition 3.1). -/
def Primitive (Q : List ℕ) : Prop :=
  Q ≠ [] ∧ ∀ (U : List ℕ) (e : ℕ), 2 ≤ e → Q ≠ (List.replicate e U).flatten

/-- One edge of an alignment graph: deletion `(i, j) → (i+1, j)`, insertion `(i, j) → (i, j+1)`
or diagonal `(i, j) → (i+1, j+1)` (Definition 3.4). -/
def IsStep (u v : ℤ × ℤ) : Prop :=
  v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1) ∨ v = (u.1 + 1, u.2 + 1)

/-- The cost of an edge `u → v` of `AG(X[..), Y[..))`: `1` for a deletion or an insertion; for a
diagonal edge `0` if `X[i] = Y[j]` and `1` otherwise (Definition 3.4). -/
def stepCost (X Y : ℤ → ℕ) (u v : ℤ × ℤ) : ℕ :=
  if v = (u.1 + 1, u.2 + 1) then (if X u.1 = Y u.2 then 0 else 1) else 1

/-- `A` is an alignment `X[x..x') ⇝ Y[y..y')`: a directed path of alignment-graph edges, listed by
its vertices in path order, from `(x, y)` to `(x', y')` (Definition 3.4). -/
def IsAlignment (x x' y y' : ℤ) (A : List (ℤ × ℤ)) : Prop :=
  A.head? = some (x, y) ∧ A.getLast? = some (x', y') ∧ List.IsChain IsStep A

/-- The edges of a path, as consecutive vertex pairs in path order. -/
def edges (A : List (ℤ × ℤ)) : List ((ℤ × ℤ) × (ℤ × ℤ)) := A.zip A.tail

/-- `cost(A)`: the total cost of the edges of the path `A`, i.e. its number of edits. -/
def alnCost (X Y : ℤ → ℕ) (A : List (ℤ × ℤ)) : ℕ :=
  ((edges A).map (fun e => stepCost X Y e.1 e.2)).sum

/-- The cost of the subpath of `A` from its vertex with index `i` to its vertex with index `i'`
(vertices numbered `0, 1, …` in path order): the sum of the costs of the edges with index in
`[i..i')`. -/
def segCost (X Y : ℤ → ℕ) (A : List (ℤ × ℤ)) (i i' : ℕ) : ℕ :=
  ∑ s ∈ Finset.Ico i i', stepCost X Y (A.getD s (0, 0)) (A.getD (s + 1) (0, 0))

/-- `ed(U, V)`: the minimum cost of an alignment `U ⇝ V` of the two strings, i.e. the distance
from `(0, 0)` to `(|U|, |V|)` in `AG(U, V)` (§3.3); unit-cost Levenshtein distance. -/
noncomputable def ed (U V : List ℕ) : ℕ :=
  sInf {c | ∃ A, IsAlignment 0 U.length 0 V.length A ∧ alnCost (chars U) (chars V) A = c}

/-- `ed(X, *Q*)`: the minimum of `ed(X, Q∞[a..b))` over all fragments `Q∞[a..b)`, `a ≤ b`, of `Q∞`
(§2.1, p. 5). -/
noncomputable def edStar (X Q : List ℕ) : ℕ :=
  sInf {c | ∃ a b : ℤ, a ≤ b ∧ c = ed X (spell (qinf Q) a b)}

/-- `Occ_k(P, T) := {s ∈ [0..|T|] : min_{e ∈ [s..|T|]} ed(P, T[s..e)) ≤ k}` (p. 1). -/
def Occ (k : ℕ) (P T : List ℕ) : Set ℕ :=
  {s | s ≤ T.length ∧ ∃ e, s ≤ e ∧ e ≤ T.length ∧ ed P (frag T s e) ≤ k}

/-- `d↓(p, t)`: the shortest-path distance in `AG(P, T)` from the vertex `(p, t)` to the bottom row
`{|P|} × [0..|T|]` (Definition 5.6); a path to `(|P|, e)` is an alignment
`P[p..|P|) ⇝ T[t..e)`. -/
noncomputable def dDown (P T : List ℕ) (p t : ℤ) : ℕ :=
  sInf {c | ∃ (e : ℤ) (A : List (ℤ × ℤ)), t ≤ e ∧ e ≤ T.length ∧
    IsAlignment p P.length t e A ∧ alnCost (chars P) (chars T) A = c}

/-- `F ∼_A G` for `F = X[s..s')`, `G = Y[t..t')`: both `(s, t)` and `(s', t')` are vertices of `A`
(Definition 3.6). -/
def Aligned (A : List (ℤ × ℤ)) (s s' t t' : ℤ) : Prop := (s, t) ∈ A ∧ (s', t') ∈ A

/-- `ed_A(F, G) := cost(A[(s, t)..(s', t')])` for aligned `F = X[s..s')`, `G = Y[t..t')`
(Definition 3.6): the cost of the subpath between the two vertices (the vertices of a path are
pairwise distinct, so their indices are well defined). -/
def edA (X Y : ℤ → ℕ) (A : List (ℤ × ℤ)) (s s' t t' : ℤ) : ℕ :=
  segCost X Y A (A.idxOf (s, t)) (A.idxOf (s', t'))

/-- An entry of a breakpoint representation: `((x̄, a), (ȳ, b))` where `a, b` are a character or
`ε` (`none`). -/
abbrev BPEntry := (ℤ × Option ℕ) × (ℤ × Option ℕ)

/-- The entry of the breakpoint of an edit `u → v` of `A : X[..) ⇝ Y[..)` (Definition 3.8):
`((x̄, X[x̄]), (ȳ, ε))` for a deletion, `((x̄, ε), (ȳ, Y[ȳ]))` for an insertion and
`((x̄, X[x̄]), (ȳ, Y[ȳ]))` for a substitution, where `(x̄, ȳ) = u`. -/
def bpEntry (X Y : ℤ → ℕ) (u v : ℤ × ℤ) : BPEntry :=
  if v = (u.1 + 1, u.2) then ((u.1, some (X u.1)), (u.2, none))
  else if v = (u.1, u.2 + 1) then ((u.1, none), (u.2, some (Y u.2)))
  else ((u.1, some (X u.1)), (u.2, some (Y u.2)))

/-- The breakpoint representation `bp(A)` of an alignment `A : X[x..x') ⇝ Y[y..y')`
(Definition 3.8): the entry `((x, ε), (y, ε))`, the entries of all breakpoints (tails of edits) in
path order, and the entry `((x', ε), (y', ε))`. -/
def bp (X Y : ℤ → ℕ) (x x' y y' : ℤ) (A : List (ℤ × ℤ)) : List BPEntry :=
  [((x, none), (y, none))] ++
    ((edges A).filter (fun e => 0 < stepCost X Y e.1 e.2)).map (fun e => bpEntry X Y e.1 e.2) ++
    [((x', none), (y', none))]

/-- The arithmetic progression `{a + jδ : 0 ≤ j < ℓ}`. -/
def prog (a δ ℓ : ℕ) : Set ℕ := {v | ∃ j, j < ℓ ∧ v = a + j * δ}

/-- A list of progressions `(a_i, ℓ_i)` with common difference `δ` represents `S` as pairwise
disjoint nonempty progressions: every `ℓ_i ≥ 1`, distinct entries are disjoint, and their union is
`S`. -/
def DisjointProgRep (δ : ℕ) (L : List (ℕ × ℕ)) (S : Set ℕ) : Prop :=
  (∀ x ∈ L, 1 ≤ x.2) ∧
  (∀ i j (hi : i < L.length) (hj : j < L.length), i ≠ j →
    Disjoint (prog L[i].1 δ L[i].2) (prog L[j].1 δ L[j].2)) ∧
  (∀ v, v ∈ S ↔ ∃ x ∈ L, v ∈ prog x.1 δ x.2)

/-- A list of nonempty progressions `(a_i, ℓ_i)` with common difference `δ` whose union is `S`
(not necessarily disjoint). -/
def ProgUnionRep (δ : ℕ) (L : List (ℕ × ℕ)) (S : Set ℕ) : Prop :=
  (∀ x ∈ L, 1 ≤ x.2) ∧ (∀ v, v ∈ S ↔ ∃ x ∈ L, v ∈ prog x.1 δ x.2)

/-- The words `[a₁, ℓ₁, a₂, ℓ₂, …]` of a list of pairs. -/
def pairWords (L : List (ℕ × ℕ)) : List ℕ := L.flatMap (fun x => [x.1, x.2])

end PMEdits.Main


