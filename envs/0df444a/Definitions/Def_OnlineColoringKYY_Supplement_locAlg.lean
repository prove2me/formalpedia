-- Prove2me | Definitions.Def_OnlineColoringKYY_Supplement_locAlg
-- name    : OnlineColoringKYY_Supplement_locAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:09:30.98763+00:00
-- url     : https://prove2.me/theorems/ac777ef1-84fa-4832-a431-12aa63a7e256
-- title:
--   The deterministic algorithm for LOC$(k)$: LOC$'(k)$ (Algorithm 5), CB$(k,M,\nu)$ and CB$(k,\ell,\nu)$ (Algorithm 6)
-- statement:
--   The algorithm of Part B of Section 6. Fix $0 < \varepsilon < 2$ and the number of vertices $N$, known in advance, and put (logarithms to base 2)
--   $$
--   M = \bigl\lfloor (\log\log N)^{1-\varepsilon/2} \bigr\rfloor, \qquad L = \bigl\lfloor N^{1/M^{11}} \bigr\rfloor .
--   $$
--   A clique block is a set of $M$-cliques; $\mathrm{vert}(\mathcal S)$ is the union of its cliques. Every sub-instance below uses its own palette, disjoint from all others.
--
--   1. **LOC$(k)$** (Section 6.5). For $t = 0, 1, \dots$, process the next $2^t$ vertices with a new instance of LOC$'(k)$ on $2^t$ vertices; if it returns a certificate $X$, return $X$.
--   2. **LOC$'(k)$, $k \le M$** (Section 6.6). Put the $i$-th arriving vertex into bin $B_{\lceil i/L\rceil}$, and color each bin with the algorithm of Corollary 6.5. When an $(M+1)$-clique appears in a bin, output such a clique and terminate, coloring the last vertex with one extra color.
--   3. **LOC$'(k)$, $k > M$** (Algorithm 5), on $n$ vertices. Let $J = \max\{1, \lfloor n/\max(L, n^{1/k^5})\rfloor\}$ and $\nu = 2n\,L^{M-1}/J$. For an arriving $v$, let $j$ be the smallest index with $|B_j| < L$ and $G[B_j \cup \{v\}]$ $(M+1)$-clique-free. If $B_j = \emptyset$ and exactly $J$ bins have size between $1$ and $L-1$, color $v$ with the single instance of CB$(k,k,\nu)$, giving it $\mathcal C(v)$, the $M$-cliques inside one bin all of whose vertices are adjacent to $v$; if CB returns $(\mathcal S', V')$, return $\mathrm{vert}(\mathcal S') \cup V'$. Otherwise put $v$ into $B_j$ and color it with the algorithm of Corollary 6.5 for $B_j$.
--   4. **CB$(k, M, \nu)$** (Section 6.7). Color every vertex with one instance of LOC$(k-M)$; if it returns $X$, return $(\{\mathrm{adj}(x) : x \in X\}, X)$ with $\mathrm{adj}(x) \in \mathcal C(x)$.
--   5. **CB$(k, \ell, \nu)$, $M < \ell \le k$** (Algorithm 6). Keep the current instance $I^{\mathrm{LOC}}_t$ of LOC$(k-\ell)$, the sets $Q_1, Q_2, \dots$ and instances $I_{i,j}$ of CB$(k,\ell-1,2\nu)$. For an arriving $v$: if some non-terminated $I_{i,j}$ has $|\mathcal S(I_{i,j}) \cap \mathcal C(v)| \ge |\mathcal S(I_{i,j})|/(2\nu)$, color $v$ with such an $I_{i,j}$, giving it $\mathcal S(I_{i,j}) \cap \mathcal C(v)$, and if then $I_{i,1}, \dots, I_{i,|Q_i|}$ have all terminated with $(\mathcal S'_j, V'_j)$, return $(\bigcup_j \mathcal S'_j, \bigcup_j V'_j \cup Q_i)$. Otherwise color $v$ with $I^{\mathrm{LOC}}_t$; if it returns $X = \{x_1, \dots\}$, set $Q_t \leftarrow X$, create $I_{t,j}$ with $\mathcal S(I_{t,j}) = \mathcal C(x_j)$, start $I^{\mathrm{LOC}}_{t+1}$ and set $t \leftarrow t+1$.
--
--   The **run of LOC$(M^2)$** on a graph with vertices $0, 1, \dots$ lists the colors it assigns, up to and including the vertex at which it terminates with a certificate, if it does; the **number of colors** is the number of distinct colors in this list.
--
--   This is the algorithm of Theorem 6.26.
--
--   **Formalization Note** Each instance's state is stored explicitly and updated vertex by vertex; at the arrival of $v$ the algorithm reads only the prefix graph at $v$. The arbitrary choices (the certificate clique, $\mathrm{adj}(x)$, the instance $I_{i,j}$, the color of Algorithm 3) are made by a resolver. Disjoint palettes are realized by tagging each color with the address of its instance. Branches for $M = 0$, for $\ell = 0$ or $\ell > k$, and for a state that does not match its problem never arise when $M \ge 1$, and get fixed values so that the recursion is total.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 6 "Proof framework", printed p.22 (PDF p.24); Section 6.4, Definitions 6.7–6.8, printed p.29 (PDF p.31); Sections 6.5–6.8 and Algorithms 5–6, printed pp.30–35 (PDF pp.32–37)

import Mathlib
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_Supplement_Common
import Definitions.Def_OnlineColoringKYY_Supplement_cliqueFree

set_option autoImplicit false

namespace OnlineColoringKYY.Supplement

open Classical

/-! Sections 6.4–6.8 of Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios
Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256
3d1eeea6…), printed pp.28–35 = PDF pp.30–37: the deterministic algorithm for LOC(k), built from
LOC′(k) (Section 6.6, Algorithm 5), CB(k, M, ν) (Section 6.7) and CB(k, ℓ, ν) for `ℓ > M`
(Section 6.8, Algorithm 6). -/

/-- The parameters of Section 6 (printed p.22 = PDF p.24): `M = ⌊(log log N)^{1−ε/2}⌋` and
`L = ⌊N^{1/M^{11}}⌋`, with logarithms to base 2 (p.10: "We generally assume base 2 for the
logarithm"). `N`, the number of vertices, is known in advance. -/
structure LocParams where
  M : ℕ
  L : ℕ

/-- `M = ⌊(log₂ log₂ N)^{1 − ε/2}⌋` (printed p.22 = PDF p.24). -/
noncomputable def locM (ε : ℝ) (N : ℕ) : ℕ :=
  ⌊(Real.logb 2 (Real.logb 2 (N : ℝ))) ^ (1 - ε / 2)⌋₊

/-- `L = ⌊N^{1/M^{11}}⌋` (printed p.22 = PDF p.24). -/
noncomputable def locL (ε : ℝ) (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ ((1 : ℝ) / ((locM ε N : ℕ) : ℝ) ^ 11)⌋₊

/-- The parameters `(M, L)` for `N` vertices and the fixed `ε`. -/
noncomputable def locParams (ε : ℝ) (N : ℕ) : LocParams := ⟨locM ε N, locL ε N⟩

/-- Which problem an instance solves: `loc k` is LOC(k) (number of vertices unknown), `locP k n`
is LOC′(k) on `n` vertices known in advance, `cb k ℓ ν` is CB(k, ℓ, ν) (Definitions 6.7, 6.8,
printed p.29 = PDF p.31). -/
inductive Mode where
  | loc (k : ℕ) : Mode
  | locP (k n : ℕ) : Mode
  | cb (k ℓ : ℕ) (ν : ℝ) : Mode

/-- Termination measure of the recursion LOC(k) → LOC′(k) → CB(k, k, ·) → ⋯ → CB(k, ℓ, ·) →
LOC(k − ℓ): lexicographic in `(k, stage)`. -/
def Mode.meas : Mode → ℕ × ℕ
  | .loc k => (k, k + 2)
  | .locP k _ => (k, k + 1)
  | .cb k ℓ _ => (k, ℓ)

/-- The output of a terminating instance: a pair `(𝒮′, V′)` of a set of cliques and a set of
vertices (for CB), or `(∅, X)` for a LOC/LOC′ certificate `X`. -/
abbrev Out : Type := Finset (Finset ℕ) × Finset ℕ

/-- The **state of an instance** of LOC, LOC′ or CB.

* `fresh`: just created, nothing received yet.
* `loc t cnt cur`: LOC(k) (Section 6.5) running its `t`-th LOC′(k) instance `cur` on `2^t`
  vertices, of which `cnt` have been received.
* `small cnt bins`: LOC′(k), `k ≤ M` (Section 6.6), `cnt` vertices received, the bins in order
  with their Corollary 6.5 states.
* `big bins cb`: LOC′(k), `k > M` (Algorithm 5): the nonempty bins in order of creation with
  their Corollary 6.5 states, and the CB(k, k, ν) instance.
* `cbBase loc cs`: CB(k, M, ν) (Section 6.7): its LOC(k − M) instance and the list of received
  vertices with their `𝒞(v)`.
* `cbStep t cur Q subs cs`: CB(k, ℓ, ν), `ℓ > M` (Algorithm 6): the current LOC(k − ℓ)
  instance `I^LOC_t`, the recorded certificates `Q_i` (as pairs `(i, Q_i)`), the instances
  `I_{i,x}` of CB(k, ℓ − 1, 2ν), one for each `x ∈ Q_i` (as tuples
  `(i, x, 𝒮(I_{i,x}), state, output if terminated)`), and the received vertices with their
  `𝒞(v)`. -/
inductive Inst where
  | fresh : Inst
  | loc (t cnt : ℕ) (cur : Inst) : Inst
  | small (cnt : ℕ) (bins : List (Finset ℕ × (ℕ × CFState))) : Inst
  | big (bins : List (Finset ℕ × (ℕ × CFState))) (cb : Inst) : Inst
  | cbBase (loc : Inst) (cs : List (ℕ × Finset (Finset ℕ))) : Inst
  | cbStep (t : ℕ) (cur : Inst) (Q : List (ℕ × Finset ℕ))
      (subs : List (ℕ × ℕ × Finset (Finset ℕ) × Inst × Option Out))
      (cs : List (ℕ × Finset (Finset ℕ))) : Inst

instance : Inhabited Inst := ⟨Inst.fresh⟩

/-- The initial state of a new instance for the given problem. -/
def Inst.initOf (P : LocParams) : Mode → Inst
  | .loc _ => .loc 0 0 .fresh
  | .locP k _ => if k ≤ P.M then .small 0 [] else .big [] .fresh
  | .cb _ ℓ _ => if ℓ ≤ P.M then .cbBase .fresh [] else .cbStep 1 .fresh [] [] []

/-- Replace a `fresh` state by the initial state of its problem. -/
def Inst.normalize (P : LocParams) (m : Mode) : Inst → Inst
  | .fresh => Inst.initOf P m
  | s => s

/-- The recorded `𝒞(x)` of a received vertex `x` (`∅` if `x` was not received). -/
def lookupC (cs : List (ℕ × Finset (Finset ℕ))) (x : ℕ) : Finset (Finset ℕ) :=
  ((cs.find? (fun p => p.1 = x)).map Prod.snd).getD ∅

/-- The recorded certificate `Q_i` (`∅` if none). -/
def lookupQ (Q : List (ℕ × Finset ℕ)) (i : ℕ) : Finset ℕ :=
  ((Q.find? (fun p => p.1 = i)).map Prod.snd).getD ∅

/-- The vertex set `vert(𝒮′) ∪ V′` of an output pair. -/
def Out.verts (o : Out) : Finset ℕ := o.1.sup id ∪ o.2

/-- **One step of an instance** of LOC(k), LOC′(k) or CB(k, ℓ, ν) (Kawarabayashi–Yoneda–Yoneda,
STOC 2027 submission (manuscript sha256 3d1eeea6…), Sections 6.5–6.8 and Algorithms 5, 6,
printed pp.30–35 = PDF pp.32–37), on the arrival of the vertex `v`. `Adj` is the adjacency of the
vertices arrived so far, `addr` the instance's address, `Cv` the set `𝒞(v)` of cliques given with
`v` (used by CB only). Returns the new state, the color of `v`, and the output if the instance
terminates at `v` (it colors `v` in every case).

* **LOC(k)** (Section 6.5): for `t = 0, 1, …` the next `2^t` vertices go to a new LOC′(k)
  instance on `2^t` vertices; if it returns a certificate, LOC(k) returns it.
* **LOC′(k), `k ≤ M`** (Section 6.6): the `i`-th received vertex goes to bin `⌈i/L⌉`, each bin
  colored by Corollary 6.5's algorithm. When an `(M+1)`-clique appears in the bin, output one
  (chosen by `R.clique`) and terminate, coloring `v` with one extra color.
* **LOC′(k), `k > M`** (Algorithm 5): `J = max{1, ⌊n/max(L, n^{1/k⁵})⌋}`,
  `ν = 2n·L^{M−1}/J`; `j` is the smallest index with `|B_j| < L` and `G[B_j ∪ {v}]`
  `(M+1)`-clique-free. If `B_j = ∅` and exactly `J` bins are incomplete (`1 ≤ |B_ℓ| < L`), color
  `v` by the CB(k, k, ν) instance with `𝒞(v)` the `M`-cliques inside one bin all of whose vertices
  are adjacent to `v`; if it returns `(𝒮′, V′)`, return `vert(𝒮′) ∪ V′`. Otherwise put `v` into
  `B_j` and color it with Corollary 6.5's algorithm for `B_j`.
* **CB(k, M, ν)** (Section 6.7): color with LOC(k − M); if it returns `X`, return
  `({adj(x) : x ∈ X}, X)` with `adj(x) ∈ 𝒞(x)` chosen by `R.adj`.
* **CB(k, ℓ, ν), `ℓ > M`** (Algorithm 6): if some non-terminated `I_{i,j}` has
  `|𝒮(I_{i,j}) ∩ 𝒞(v)| ≥ |𝒮(I_{i,j})|/(2ν)`, color `v` with the one chosen by `R.inst`, giving it
  `𝒮(I_{i,j}) ∩ 𝒞(v)`; if then all of `I_{i,1}, …, I_{i,|Q_i|}` have terminated, return
  `(𝒮′_1 ∪ ⋯, V′_1 ∪ ⋯ ∪ Q_i)`. Otherwise color `v` with `I^LOC_t`; if it returns `X`, set
  `Q_t ← X`, create `I_{t,x}` with `𝒮(I_{t,x}) = 𝒞(x)` for every `x ∈ X`, and start `I^LOC_{t+1}`.

**Formalization Note** All sub-instances get pairwise disjoint palettes through their addresses
(tags `[3, t, 0]` for the LOC′ instances of LOC, `[0, b, 0]` for bins, `[2, 0, 0]` for the extra
color, `[8, 0, 0]` for the CB instance of Algorithm 5, `[4, 0, 0]` for the LOC instance of
CB(k, M, ·), `[5, i, x]` and `[6, t, 0]` for the instances of Algorithm 6). The branches for
`M = 0`, for `ℓ = 0` or `ℓ > k`, and for a state that does not match its problem never occur
when `M ≥ 1` and are given a fixed value so that the recursion is total. -/
noncomputable def locStep (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (v : ℕ)
    (m : Mode) (addr : List ℕ) (Cv : Finset (Finset ℕ)) (s : Inst) : Inst × Color × Option Out :=
  match m, Inst.normalize P m s with
  | .loc k, .loc t cnt cur =>
    let t' := if 2 ^ t ≤ cnt then t + 1 else t
    let cnt' := if 2 ^ t ≤ cnt then 0 else cnt
    let cur' := if 2 ^ t ≤ cnt then Inst.fresh else cur
    let res := locStep P R Adj v (.locP k (2 ^ t')) (addr ++ [3, t', 0]) ∅ cur'
    (.loc t' (cnt' + 1) res.1, res.2.1, res.2.2)
  | .locP _ _, .small cnt bins =>
    let b := cnt / P.L
    let bin := bins.getD b (∅, (0, default))
    let B' := insert v bin.1
    let cl := cliquesIn Adj (P.M + 1) B'
    if cl.Nonempty then
      (.small (cnt + 1) bins, (addr ++ [2, 0, 0], 0), some (∅, R.clique addr v cl))
    else
      let res := c65Step P.M R Adj v (addr ++ [0, b, 0]) bin.2
      let bins' := if b < bins.length then bins.set b (B', res.1) else bins ++ [(B', res.1)]
      (.small (cnt + 1) bins', res.2, none)
  | .locP k n, .big bins cb =>
    let J : ℕ := max 1 ⌊(n : ℝ) / max (P.L : ℝ) ((n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ 5))⌋₊
    let ν : ℝ := 2 * (n : ℝ) * (P.L : ℝ) ^ (P.M - 1) / (J : ℝ)
    let ok : ℕ → Prop := fun j =>
      (bins.getD j (∅, (0, default))).1.card < P.L ∧
        cliquesIn Adj (P.M + 1) (insert v (bins.getD j (∅, (0, default))).1) = ∅
    have hex : ∃ j, (j < bins.length ∧ ok j) ∨ j = bins.length := ⟨bins.length, Or.inr rfl⟩
    let j : ℕ := Nat.find hex
    let incomplete : ℕ := (bins.filter (fun b => 1 ≤ b.1.card ∧ b.1.card < P.L)).length
    if j = bins.length ∧ incomplete = J then
      let C : Finset (Finset ℕ) := bins.foldr
        (fun b acc => acc ∪ (cliquesIn Adj P.M b.1).filter (fun S => ∀ u ∈ S, Adj v u)) ∅
      let res := locStep P R Adj v (.cb k k ν) (addr ++ [8, 0, 0]) C cb
      (.big bins res.1, res.2.1, res.2.2.map (fun o => (∅, Out.verts o)))
    else
      let bin := bins.getD j (∅, (0, default))
      let res := c65Step P.M R Adj v (addr ++ [0, j, 0]) bin.2
      let bins' := if j < bins.length then bins.set j (insert v bin.1, res.1)
        else bins ++ [({v}, res.1)]
      (.big bins' cb, res.2, none)
  | .cb k _ _, .cbBase loc cs =>
    let cs' := cs ++ [(v, Cv)]
    if _h : 0 < P.M ∧ P.M ≤ k then
      let res := locStep P R Adj v (.loc (k - P.M)) (addr ++ [4, 0, 0]) ∅ loc
      (.cbBase res.1 cs', res.2.1,
        res.2.2.map (fun o => (o.2.image (fun x => R.adj addr x (lookupC cs' x)), o.2)))
    else (.cbBase loc cs', (addr, 0), none)
  | .cb k ℓ ν, .cbStep t cur Q subs cs =>
    let cs' := cs ++ [(v, Cv)]
    if _h : 0 < ℓ ∧ ℓ ≤ k then
      let cand : Finset (ℕ × ℕ) := ((subs.filter (fun e =>
          e.2.2.2.2 = none ∧
            ((e.2.2.1 ∩ Cv).card : ℝ) ≥ (e.2.2.1.card : ℝ) / (2 * ν))).map
          (fun e => (e.1, e.2.1))).toFinset
      if cand.Nonempty then
        let key := R.inst addr v cand
        let idx := subs.findIdx (fun e => decide ((e.1, e.2.1) = key))
        let e := subs.getD idx (0, 0, ∅, Inst.fresh, none)
        let res := locStep P R Adj v (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, e.1, e.2.1])
          (e.2.2.1 ∩ Cv) e.2.2.2.1
        let subs' := subs.set idx (e.1, e.2.1, e.2.2.1, res.1, res.2.2)
        let fam := subs'.filter (fun f => f.1 = e.1)
        let outp : Option Out :=
          if fam.all (fun f => f.2.2.2.2.isSome) then
            some (fam.foldr (fun f acc => match f.2.2.2.2 with
              | some o => (acc.1 ∪ o.1, acc.2 ∪ o.2)
              | none => acc) (∅, lookupQ Q e.1))
          else none
        (.cbStep t cur Q subs' cs', res.2.1, outp)
      else
        let res := locStep P R Adj v (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅ cur
        match res.2.2 with
        | none => (.cbStep t res.1 Q subs cs', res.2.1, none)
        | some o =>
          (.cbStep (t + 1) .fresh (Q ++ [(t, o.2)])
            (subs ++ o.2.toList.map (fun x => (t, x, lookupC cs' x, Inst.fresh, none))) cs',
            res.2.1, none)
    else (.cbStep t cur Q subs cs', (addr, 0), none)
  | _, s' => (s', (addr, 0), none)
termination_by m.meas
decreasing_by
  all_goals simp only [Mode.meas]
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- The **run of LOC(M²) on `N` vertices** (Kawarabayashi–Yoneda–Yoneda, STOC 2027 submission
(manuscript sha256 3d1eeea6…), Section 6.11, printed p.37 = PDF p.39): the colors that the
algorithm for LOC(M²) of Sections 6.5–6.8, with the parameters `M`, `L` of `N` and `ε`, assigns to
the vertices `0, 1, …` of `G : SimpleGraph (Fin n)` in arrival order, up to and including the
vertex at which it terminates with a certificate, if it does (Definition 6.7: "even if we
terminate, we must color the last received vertex").

**Formalization Note** The top-level instance has the empty address. At the arrival of `v` the
algorithm sees only `prefixAdj G v`, the prefix graph at `v`. -/
noncomputable def locRun (ε : ℝ) (N : ℕ) (R : Resolver) {n : ℕ} (G : SimpleGraph (Fin n)) :
    List Color :=
  ((List.finRange n).foldl (fun (acc : Inst × Bool × List Color) v =>
    if acc.2.1 then acc else
      let res := locStep (locParams ε N) R (prefixAdj G v) v.val (.loc (locM ε N ^ 2)) [] ∅ acc.1
      (res.1, res.2.2.isSome, acc.2.2 ++ [res.2.1])) (Inst.fresh, false, [])).2.2

/-- The **number of colors used by LOC(M²)** on the input `G`: the cardinality of the set of
colors in `locRun ε N R G` (Definition 3.1, printed p.10 = PDF p.12: `|{c(v) : v ∈ V}|`, over the
vertices the algorithm colored). -/
noncomputable def locNumColors (ε : ℝ) (N : ℕ) (R : Resolver) {n : ℕ}
    (G : SimpleGraph (Fin n)) : ℕ :=
  (locRun ε N R G).toFinset.card

end OnlineColoringKYY.Supplement


