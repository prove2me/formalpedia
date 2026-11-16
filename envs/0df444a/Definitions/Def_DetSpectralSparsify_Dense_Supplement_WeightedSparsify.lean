-- Prove2me | Definitions.Def_DetSpectralSparsify_Dense_Supplement_WeightedSparsify
-- name    : DetSpectralSparsify_Dense_Supplement_WeightedSparsify
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:09:48.582018+00:00
-- url     : https://prove2.me/theorems/e55ded5c-297f-45b6-ba1b-cbe8bcd9803c
-- title:
--   Algorithms 2, 4–8 as execution relations: MatchingSparsifier, RegularizeDegrees, MatchingDecomposition, ExpanderSparsify, GlobalSparsify, WeightedSparsify
-- statement:
--   This file states, for every step of the weighted sparsification algorithm of §§4–5, what one run of the step may return. Each algorithm is an **execution relation** $\mathrm{Alg}(\text{input},\text{output})$; it contains no guarantee about its output. All graphs are the finite weighted multigraphs of the mission (parallel edges and self-loops allowed), and every relation is built from the published graph operations (Laplacian, normalized Laplacian, cluster graph $G\langle U\rangle$, contraction, aggregation) and from Algorithm 1.
--
--   **Fixed implementation data.** Before any input the algorithm fixes a multiplicity $a\ge1$ for the fiber expander edges, a padding constant $C_0>0$, the conductance constant $c>0$ of Lemma 10, and an expander family: for every $t\ge2$ a loop-free graph on $t$ vertices of maximum combinatorial degree at most $\Delta$ and, with unit weights, conductance at least $\varphi>0$ ($\Delta,\varphi$ independent of $t$).
--
--   1. **Algorithm 2** (p.10). For a graph $G$ on $N$ vertices with matchings $M_1,\dots,M_q$, weight bound $\beta$, conductance bound $\phi$ and accuracy $\varepsilon$: $P=(\mathcal L_G|_U)^{-1/2}$ extended by $0$ on $\operatorname{span}(D_G^{1/2}\mathbf 1)$, $A_i=q\,P D_G^{-1/2}L_{M_i}D_G^{-1/2}P$, $R=4\beta q/(\delta_G\phi^2)$ with $\delta_G$ the minimum weighted degree, $k=\lceil 4R\varepsilon^{-2}\ln(4N)\rceil$. The indices $i_1,\dots,i_k$ are chosen by Algorithm 1 with scores evaluated within the additive tolerance $R/(16\varepsilon k)$ of Lemma 6, and the output is $\frac qk(M_{i_1}\,\dot\cup\cdots\dot\cup\,M_{i_k})$.
--   2. **Algorithm 4** (p.18) with $s=\lceil d\rceil$: vertex $v$ becomes a fiber of $t_v=\max\{1,\lceil\deg_G(v)/s\rceil\}$ copies; the non-loop incidences at $v$ are assigned to copies so that every copy carries at most the average load plus $2$; every non-loop edge joins its two assigned copies with its weight; every fiber with $t_v\ge2$ receives $a$ unit-weight copies of the expander on $t_v$ vertices; finally every copy $x$ gets a self-loop of weight $C_0s-\deg(x)$, so that every degree equals $C_0 s$.
--   3. **Algorithm 5** (p.20): starting from $\{E^\times(G)\}$, while some member has $\Delta^\#>4$, every such member $Q$ is replaced by a red/blue partition in which each color has $\Delta^\#\le\Delta^\#(Q)/2+2$ (the outcome of the Euler-tour alternation); then every member is properly edge-colored with seven colors and the nonempty color classes are the matchings.
--   4. **Algorithm 6** (p.21): Algorithm 4, then Algorithm 5 on $G^\circ$, then Algorithm 2 on $G^\circ$ with $\beta=2$ and conductance $c\phi$, then contraction of every fiber with deletion of self-loops.
--   5. **Algorithm 7** (p.23) on an $n$-vertex graph: residual sets $R_0=E^\times(G),R_1,\dots,R_T$ with $|R_j|\ge n$ for $j<T$ and $|R_T|<n$. In iteration $j$, $F=(V,R_j)$, $d=2w(R_j)/n$; $U$ is the result of repeatedly deleting a vertex of degree below $d/10$ in $F[U]$; $F[U]$ (on $U$) is partitioned into clusters $V_1,\dots,V_t$ such that at most half of its edges join distinct clusters and every cluster graph of the unweighted $F[U]$ has conductance at least $\phi_n$; every cluster with a non-loop edge is sent to Algorithm 6 as $F[U]\langle V_i\rangle$ (on $V_i$) with $d$ and conductance $\phi_n/2$; the edges inside clusters leave $R$. The output is the union of all cluster outputs followed by the edges of $R_T$ with their original weights.
--   6. **Algorithm 8** (p.27): for every occupied dyadic class $a$ ($2^a\le w(e)<2^{a+1}$) of non-loop edges, $G_a$ is $E_a$ with weights divided by $2^a$, Algorithm 7 returns $H_a$ on $G_a$, and the output is the edge-disjoint union of the $H_a$ with weights multiplied by $2^a$.
--
--   These relations are the objects of Lemma 16 and Theorem 17: those results speak about every run of the named algorithms rather than about some algorithm with the same guarantees.
--
--   **Formalization Note** Where the paper leaves a choice open (vertex removal order, Euler tour and its start, greedy orders, the expander decomposition of [Chu23], the numerical score evaluation of §§4.1–4.3), the relation admits every choice that meets the structural property the paper states for it, so each fixed deterministic implementation is one run. The score evaluation is specified by the Lemma 6 tolerance, which is what both the dense and the sparse evaluation produce, so the `Mode` argument does not change the relation; it changes the cost of a program that computes it. The matrices $A_i$ and $P$ are zero-extended to $\mathbb R^N$ (traces in Algorithm 1 are unchanged); $P$ is the continuous functional calculus of $x\mapsto x^{-1/2}$ (value $0$ at $0$) applied to $\mathcal L_G$. Vertex subsets are relabelled onto $\{0,\dots,|U|-1\}$ in increasing order and mapped back after each call. The decomposition threshold is $\phi_n$ with $n$ the number of vertices of the input of Algorithm 7, the quantity Algorithm 7 line 11 uses.
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.9 ((4)–(6)), p.10 (Algorithm 2), p.18 (Algorithm 4), p.19 (greedy incidence placement, expander family [CGL+20]), p.20 (Algorithm 5 and its proof), p.21 (Algorithm 6), p.22 (Theorem 13, G⟨U⟩), p.23 (Algorithm 7), p.27 (Algorithm 8); δ_G from p.4

import Definitions.Def_DetSpectralSparsify_Dense_Machine
import Definitions.Def_DetSpectralSparsify_Dense_MatrixChernoff

set_option autoImplicit false

namespace DetSpectralSparsify.Dense.Supplement

open DetSpectralSparsify.Dense Matrix

/-! # The weighted sparsification algorithm (Algorithms 2, 4–8, pp.9–27)

Every algorithm is an *execution relation* `Alg … input … output : Prop`: it holds when `output`
is what one run of the algorithm returns on `input`. Where the paper leaves a step open (a tie
order, the Euler tour, the greedy order, the expander decomposition of [Chu23], the numerical
score evaluation) the relation admits every choice that meets the structural specification the
paper states for that step, so each fixed deterministic implementation is one execution.
No relation contains a correctness, size, weight or running-time guarantee of its output. -/

/-- The two implementations of the score evaluation (§4.1 dense, §4.3 sparse). Both are
specified below by the output they must produce (scores within the Lemma 6 tolerance), so the
mode changes how a program computes the scores, not the execution relation. -/
inductive Mode
  | dense
  | sparse

/-! ## Graph operations -/

/-- The graph with no edges on `Fin n`. -/
def emptyGraph (n : ℕ) : Multigraph n where
  m := 0
  src := Fin.elim0
  dst := Fin.elim0
  w := Fin.elim0

/-- The edges of `G` followed by those of `H`. -/
def appendGraph {n : ℕ} (G H : Multigraph n) : Multigraph n where
  m := G.m + H.m
  src := Fin.append G.src H.src
  dst := Fin.append G.dst H.dst
  w := Fin.append G.w H.w

/-- The edges of `G` with index in `S`, in increasing index order, on the same vertex set. -/
def edgeSub {n : ℕ} (G : Multigraph n) (S : Finset (Fin G.m)) : Multigraph n where
  m := S.card
  src := fun j => G.src (S.orderEmbOfFin rfl j)
  dst := fun j => G.dst (S.orderEmbOfFin rfl j)
  w := fun j => G.w (S.orderEmbOfFin rfl j)

/-- The non-loop edges `E^×(G)`. -/
def nonloops {n : ℕ} (G : Multigraph n) : Finset (Fin G.m) :=
  Finset.univ.filter fun e => ¬ G.IsLoop e

/-- The `i`-th vertex of `U` in increasing order. -/
def vertexEmb {n : ℕ} (U : Finset (Fin n)) (i : Fin U.card) : Fin n := U.orderEmbOfFin rfl i

/-- The position of `v ∈ U` in the increasing enumeration of `U`. -/
noncomputable def vertexPos {n : ℕ} (U : Finset (Fin n)) (v : Fin n) (hv : v ∈ U) :
    Fin U.card :=
  (U.orderIsoOfFin rfl).symm ⟨v, hv⟩

/-- The subgraph of `G` on the vertex set `U`, relabelled onto `Fin |U|` in increasing order:
the edges with both endpoints in `U` (self-loops in `U` included). This is `G[U]` with the
vertices outside `U` removed. -/
noncomputable def restrictTo {n : ℕ} (G : Multigraph n) (U : Finset (Fin n)) :
    Multigraph U.card :=
  let s := Finset.univ.filter fun e : Fin G.m => G.src e ∈ U ∧ G.dst e ∈ U
  { m := s.card
    src := fun j => vertexPos U (G.src (s.orderEmbOfFin rfl j))
      (Finset.mem_filter.1 (s.orderEmbOfFin_mem rfl j)).2.1
    dst := fun j => vertexPos U (G.dst (s.orderEmbOfFin rfl j))
      (Finset.mem_filter.1 (s.orderEmbOfFin_mem rfl j)).2.2
    w := fun j => G.w (s.orderEmbOfFin rfl j) }

/-- Relabel the vertices of `H` along `f`, keeping every edge (no edge is deleted). -/
def mapGraph {k n : ℕ} (f : Fin k → Fin n) (H : Multigraph k) : Multigraph n where
  m := H.m
  src := f ∘ H.src
  dst := f ∘ H.dst
  w := H.w

/-- Multiply every edge weight by `c`. -/
def scaleGraph {n : ℕ} (c : ℝ) (G : Multigraph n) : Multigraph n :=
  { G with w := fun e => c * G.w e }

/-- Minimum weighted degree `δ_G = min_v deg_G(v)` (p.4); `0` on the empty vertex set. -/
noncomputable def minDeg {n : ℕ} (G : Multigraph n) : ℝ :=
  if h : 0 < n then Finset.univ.inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ G.deg else 0

/-! ## Fixed implementation data -/

/-- The data the paper fixes once, before any input: the multiplicity `a` of the fiber-expander
edges (Algorithm 4 line 12), the padding constant `C₀` (Algorithm 4 line 14), the conductance
constant `c` of Lemma 10 used in Algorithm 6 line 3, and the explicit expander family placed on
the fibers (Algorithm 4 line 6, [CGL+20, Theorem 2.4]). -/
structure ImplData where
  a : ℕ
  C₀ : ℝ
  cCond : ℝ
  expander : (t : ℕ) → Multigraph t

/-- The structural specification of the implementation data (pp.18–19): `a ≥ 1`, `C₀ > 0`,
`c > 0`, and the fiber graphs form a constant-degree, constant-conductance expander family:
there are `Δ` and `φ > 0` such that for every `t ≥ 2` the graph on `t` vertices has no
self-loop, maximum combinatorial degree at most `Δ`, and, with unit weights, conductance at least
`φ`. -/
def ImplData.Spec (D : ImplData) : Prop :=
  1 ≤ D.a ∧ 0 < D.C₀ ∧ 0 < D.cCond ∧
  ∃ (Δ : ℕ) (φ : ℝ), 0 < φ ∧ ∀ t : ℕ, 2 ≤ t →
    (∀ e, ¬ (D.expander t).IsLoop e) ∧ (D.expander t).maxCombDeg ≤ Δ ∧
    (D.expander t).unitWeights.CondAtLeast φ

/-! ## Algorithm 2 (MatchingSparsifier, p.10) -/

/-- `D_G^{-1/2}`. -/
noncomputable def invSqrtDeg {N : ℕ} (G : Multigraph N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun v => (Real.sqrt (G.deg v))⁻¹

/-- `P = (𝓛_G|_U)^{-1/2}` extended by zero on `span(D_G^{1/2} 𝟏)` (p.9): the function
`x ↦ x^{-1/2}` (with value `0` at `0`) of the normalized Laplacian. For a connected `G` with
positive degrees the kernel of `𝓛_G` is exactly `span(D_G^{1/2} 𝟏)`. -/
noncomputable def invSqrtNormLap {N : ℕ} (G : Multigraph N) : Matrix (Fin N) (Fin N) ℝ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G.normLaplacian

/-- The matrices (4): `A_i = q P D_G^{-1/2} L_{M_i} D_G^{-1/2} P`, as operators on `ℝ^N` that
vanish on `U^⊥` (the paper regards them as operators on `U`; all traces in Algorithm 1 agree). -/
noncomputable def matchingMatrices {N : ℕ} (G : Multigraph N) {q : ℕ}
    (M : Fin q → Finset (Fin G.m)) (i : Fin q) : Matrix (Fin N) (Fin N) ℝ :=
  (q : ℝ) • (invSqrtNormLap G * invSqrtDeg G * (edgeSub G (M i)).laplacian * invSqrtDeg G *
    invSqrtNormLap G)

/-- `R = 4βq/(δ_G ϕ²)` (Algorithm 2 line 2, (5)). -/
noncomputable def alg2R {N : ℕ} (G : Multigraph N) (q : ℕ) (β ϕ : ℝ) : ℝ :=
  4 * β * q / (minDeg G * ϕ ^ 2)

/-- `k = ⌈4 R ε⁻² ln(4N)⌉` (Algorithm 2 line 2, (6)); `N` is the number of vertices. -/
noncomputable def alg2k {N : ℕ} (G : Multigraph N) (q : ℕ) (β ϕ ε : ℝ) : ℕ :=
  ⌈4 * alg2R G q β ϕ * (ε ^ 2)⁻¹ * Real.log (4 * N)⌉₊

/-- Algorithm 2 line 4: the multiset union of the selected matchings `M_{i_1}, …, M_{i_k}`,
every edge weight multiplied by `q/k`. -/
noncomputable def alg2Output {N : ℕ} (G : Multigraph N) {q k : ℕ}
    (M : Fin q → Finset (Fin G.m)) (idx : Fin k → Fin q) : Multigraph N :=
  Multigraph.union fun j : Fin k => scaleGraph ((q : ℝ) / k) (edgeSub G (M (idx j)))

/-- An execution of Algorithm 2 on `G` with matchings `M_1, …, M_q`, weight bound `β`,
conductance bound `ϕ` and accuracy `ε`, returning `H`: the indices `i_1, …, i_k` are chosen by
Algorithm 1 (MatrixChernoffSelect) on `A_1, …, A_q`, `R`, `ε`, `k`, with scores evaluated to the
additive accuracy of Lemma 6 (this is what both score implementations of §§4.1–4.3 compute), and
`H` is the reweighted union of line 4. -/
def MatchingSparsifier {N : ℕ} (G : Multigraph N) {q : ℕ} (M : Fin q → Finset (Fin G.m))
    (β ϕ ε : ℝ) (H : Multigraph N) : Prop :=
  ∃ idx : Fin (alg2k G q β ϕ ε) → Fin q,
    IsApproxAlg1Selection (matchingMatrices G M) (alg2R G q β ϕ) ε idx ∧
    H = alg2Output G M idx

/-! ## Algorithm 4 (RegularizeDegrees, p.18) -/

/-- `t_v = max{1, ⌈deg_G(v)/s⌉}` (line 3). -/
noncomputable def fiberSize {n : ℕ} (G : Multigraph n) (s : ℕ) (v : Fin n) : ℕ :=
  max 1 ⌈G.deg v / s⌉₊

/-- `|V(G°)| = ∑_v t_v`. -/
noncomputable def regN {n : ℕ} (G : Multigraph n) (s : ℕ) : ℕ := ∑ v, fiberSize G s v

/-- The `i`-th copy of `v`, a vertex of the fiber `F_v`. -/
noncomputable def copyOf {n : ℕ} (G : Multigraph n) (s : ℕ) (v : Fin n)
    (i : Fin (fiberSize G s v)) : Fin (regN G s) :=
  finSigmaFinEquiv ⟨v, i⟩

/-- The fiber map `V(G°) → V(G)`: `x ∈ F_v ↦ v`. -/
noncomputable def fiberMap {n : ℕ} (G : Multigraph n) (s : ℕ) (x : Fin (regN G s)) : Fin n :=
  (finSigmaFinEquiv.symm x).1

/-- Total weight of the non-loop incidences at `v`. -/
noncomputable def incWeight {n : ℕ} (G : Multigraph n) (v : Fin n) : ℝ :=
  ∑ e : Fin G.m, if G.IsLoop e then 0 else
    (if G.src e = v then G.w e else 0) + (if G.dst e = v then G.w e else 0)

/-- Load of the `i`-th copy of `v` under the incidence assignment `cs, cd` (the copies that
receive the source and target incidence of every edge; loops are not distributed). -/
noncomputable def copyLoad {n : ℕ} (G : Multigraph n) (s : ℕ)
    (cs : (e : Fin G.m) → Fin (fiberSize G s (G.src e)))
    (cd : (e : Fin G.m) → Fin (fiberSize G s (G.dst e))) (v : Fin n) (i : ℕ) : ℝ :=
  ∑ e : Fin G.m, if G.IsLoop e then 0 else
    (if G.src e = v ∧ (cs e).val = i then G.w e else 0) +
    (if G.dst e = v ∧ (cd e).val = i then G.w e else 0)

/-- Line 7: the non-loop incidences at `v` are distributed among the copies of `F_v` so that every
copy receives total weight `O(s)`. Specified as the bound achieved by greedily placing each
incidence on the least-loaded copy (p.19): at most the average load plus `2`, the maximum
non-loop weight. -/
def IsBalancedAssignment {n : ℕ} (G : Multigraph n) (s : ℕ)
    (cs : (e : Fin G.m) → Fin (fiberSize G s (G.src e)))
    (cd : (e : Fin G.m) → Fin (fiberSize G s (G.dst e))) : Prop :=
  ∀ v : Fin n, ∀ i < fiberSize G s v,
    copyLoad G s cs cd v i ≤ incWeight G v / fiberSize G s v + 2

/-- Lines 9–10: every non-loop edge of `G` joins the copies assigned to its two incidences, with
its weight. -/
noncomputable def regOriginal {n : ℕ} (G : Multigraph n) (s : ℕ)
    (cs : (e : Fin G.m) → Fin (fiberSize G s (G.src e)))
    (cd : (e : Fin G.m) → Fin (fiberSize G s (G.dst e))) : Multigraph (regN G s) :=
  let E := nonloops G
  { m := E.card
    src := fun j => copyOf G s _ (cs (E.orderEmbOfFin rfl j))
    dst := fun j => copyOf G s _ (cd (E.orderEmbOfFin rfl j))
    w := fun j => G.w (E.orderEmbOfFin rfl j) }

/-- Lines 5–6 and 11–12: on every fiber with `t_v ≥ 2`, `a` parallel unit-weight copies of every
edge of the fixed expander on `t_v` vertices. -/
noncomputable def regExpanders (D : ImplData) {n : ℕ} (G : Multigraph n) (s : ℕ) :
    Multigraph (regN G s) :=
  Multigraph.union fun v : Fin n =>
    if 2 ≤ fiberSize G s v then
      Multigraph.union fun _ : Fin D.a =>
        mapGraph (copyOf G s v) (D.expander (fiberSize G s v)).unitWeights
    else emptyGraph _

/-- Lines 13–14: at every vertex `x` a self-loop raising `deg(x)` to `C₀ s`. -/
noncomputable def regPadding {N : ℕ} (C₀ : ℝ) (s : ℕ) (B : Multigraph N) : Multigraph N where
  m := N
  src := id
  dst := id
  w := fun x => C₀ * s - B.deg x

/-- The graph `G°` returned by Algorithm 4 with `s = ⌈d⌉` and incidence assignment `cs, cd`. -/
noncomputable def regGraph (D : ImplData) {n : ℕ} (G : Multigraph n) (s : ℕ)
    (cs : (e : Fin G.m) → Fin (fiberSize G s (G.src e)))
    (cd : (e : Fin G.m) → Fin (fiberSize G s (G.dst e))) : Multigraph (regN G s) :=
  let B := appendGraph (regOriginal G s cs cd) (regExpanders D G s)
  appendGraph B (regPadding D.C₀ s B)

/-! ## Algorithm 5 (MatchingDecomposition, p.20) -/

/-- Combinatorial degree of `v` in the edge set `S` (non-loop edges only). -/
def subCombDeg {n : ℕ} (G : Multigraph n) (S : Finset (Fin G.m)) (v : Fin n) : ℕ :=
  (S.filter fun e => ¬ G.IsLoop e ∧ (G.src e = v ∨ G.dst e = v)).card

/-- Maximum combinatorial degree `Δ#` of the edge set `S`. -/
def subMaxCombDeg {n : ℕ} (G : Multigraph n) (S : Finset (Fin G.m)) : ℕ :=
  Finset.univ.sup (subCombDeg G S)

/-- Lines 8–12: `Q` is split into red and blue spanning subgraphs by alternating colors along
Euler tours (with dummy vertices adjacent to the odd-degree vertices, whose edges are deleted).
Specified by its structural outcome (p.20): a partition of `Q` in which each color has maximum
combinatorial degree at most `Δ#(Q)/2 + 2`. -/
def IsEulerSplit {n : ℕ} (G : Multigraph n) (Q red blue : Finset (Fin G.m)) : Prop :=
  red ∪ blue = Q ∧ Disjoint red blue ∧
  (subMaxCombDeg G red : ℝ) ≤ (subMaxCombDeg G Q : ℝ) / 2 + 2 ∧
  (subMaxCombDeg G blue : ℝ) ≤ (subMaxCombDeg G Q : ℝ) / 2 + 2

/-- Lines 4–12 for one member `Q` of `𝓗`: kept if `Δ#(Q) ≤ 4`, otherwise replaced by its red
and blue subgraphs. -/
def SplitStep {n : ℕ} (G : Multigraph n) (Q : Finset (Fin G.m))
    (L : List (Finset (Fin G.m))) : Prop :=
  (subMaxCombDeg G Q ≤ 4 ∧ L = [Q]) ∨
  (4 < subMaxCombDeg G Q ∧ ∃ red blue, IsEulerSplit G Q red blue ∧ L = [red, blue])

/-- One pass of the while loop (lines 3–13): `𝓗' ` is obtained from `𝓗` member by member. -/
def SplitRound {n : ℕ} (G : Multigraph n) (H H' : List (Finset (Fin G.m))) : Prop :=
  ∃ Ls : List (List (Finset (Fin G.m))), List.Forall₂ (SplitStep G) H Ls ∧ H' = Ls.flatten

/-- Line 16: a proper edge coloring of `Q` with at most seven colors (greedy coloring of a graph of
maximum combinatorial degree at most `4` uses at most seven). -/
def IsSevenColoring {n : ℕ} (G : Multigraph n) (Q : Finset (Fin G.m))
    (col : Fin G.m → Fin 7) : Prop :=
  ∀ e ∈ Q, ∀ e' ∈ Q, e ≠ e' →
    (G.src e = G.src e' ∨ G.src e = G.dst e' ∨ G.dst e = G.src e' ∨ G.dst e = G.dst e') →
    col e ≠ col e'

/-- An execution of Algorithm 5 on `G` returning the list of matchings `Ms`: splitting rounds
`𝓗_0 = {E^×(G)}, 𝓗_1, …, 𝓗_T` while some member has `Δ# > 4`, then the nonempty color classes
of a seven-coloring of every member of `𝓗_T`, in order. -/
def MatchingDecomposition {n : ℕ} (G : Multigraph n) (Ms : List (Finset (Fin G.m))) : Prop :=
  ∃ (T : ℕ) (Hs : ℕ → List (Finset (Fin G.m))) (col : ℕ → Fin G.m → Fin 7),
    Hs 0 = [nonloops G] ∧
    (∀ j < T, (∃ Q ∈ Hs j, 4 < subMaxCombDeg G Q) ∧ SplitRound G (Hs j) (Hs (j + 1))) ∧
    (∀ Q ∈ Hs T, subMaxCombDeg G Q ≤ 4) ∧
    (∀ i < (Hs T).length, IsSevenColoring G ((Hs T).getD i ∅) (col i)) ∧
    Ms = ((List.range (Hs T).length).flatMap fun i =>
        (List.finRange 7).map fun c => ((Hs T).getD i ∅).filter fun e => col i e = c).filter
      fun M => decide M.Nonempty

/-! ## Algorithm 6 (ExpanderSparsify, p.21) -/

/-- An execution of Algorithm 6 on `G` with degree parameter `d`, conductance bound `ϕ`, accuracy
`ε` and `mode`, returning `H`: regularize with `s = ⌈d⌉` (Algorithm 4), decompose the non-loop
edges of `G°` into matchings (Algorithm 5), run Algorithm 2 on `G°` with `β = 2` and `ϕ° = cϕ`,
then contract every fiber and delete self-loops. -/
def ExpanderSparsify (D : ImplData) {n : ℕ} (G : Multigraph n) (d ϕ ε : ℝ) (_mode : Mode)
    (H : Multigraph n) : Prop :=
  ∃ (cs : (e : Fin G.m) → Fin (fiberSize G ⌈d⌉₊ (G.src e)))
    (cd : (e : Fin G.m) → Fin (fiberSize G ⌈d⌉₊ (G.dst e))),
    IsBalancedAssignment G ⌈d⌉₊ cs cd ∧
    ∃ (Ms : List (Finset (Fin (regGraph D G ⌈d⌉₊ cs cd).m)))
      (Hc : Multigraph (regN G ⌈d⌉₊)),
      MatchingDecomposition (regGraph D G ⌈d⌉₊ cs cd) Ms ∧
      MatchingSparsifier (regGraph D G ⌈d⌉₊ cs cd) (fun i : Fin Ms.length => Ms.get i) 2
        (D.cCond * ϕ) ε Hc ∧
      H = Multigraph.contract (fiberMap G ⌈d⌉₊) Hc

/-! ## Algorithm 7 (GlobalSparsify, p.23) -/

/-- One removal of the peeling loop (lines 5–6): some `v ∈ U` has `deg_{F[U]}(v) < d/10`. -/
def PeelStep {n : ℕ} (F : Multigraph n) (d : ℝ) (U U' : Finset (Fin n)) : Prop :=
  ∃ v ∈ U, (F.induced U).deg v < d / 10 ∧ U' = U.erase v

/-- `U` is a possible result of the peeling loop started from `U = V`: reached by removals and no
remaining vertex has degree below `d/10` in `F[U]`. -/
def IsPeeled {n : ℕ} (F : Multigraph n) (d : ℝ) (U : Finset (Fin n)) : Prop :=
  Relation.ReflTransGen (PeelStep F d) Finset.univ U ∧ ∀ v ∈ U, d / 10 ≤ (F.induced U).deg v

/-- Line 7: `lab` labels the vertices of `F` by clusters `0, …, t-1`, every label used, as
Theorem 13 does for the unweighted graph: at most half of the edges join distinct clusters, and
every cluster graph of the unweighted graph has conductance at least `ϕv`. -/
def IsExpanderDecomposition {k : ℕ} (F : Multigraph k) (ϕv : ℝ) (t : ℕ) (lab : Fin k → ℕ) :
    Prop :=
  (∀ x, lab x < t) ∧ (∀ i < t, ∃ x, lab x = i) ∧
  2 * (Finset.univ.filter fun e : Fin F.m => lab (F.src e) ≠ lab (F.dst e)).card ≤ F.m ∧
  ∀ i < t, (F.unitWeights.cluster (Finset.univ.filter fun x => lab x = i)).CondAtLeast ϕv

/-- The cluster `V_i = lab⁻¹(i)`. -/
def clusterSet {k : ℕ} (lab : Fin k → ℕ) (i : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun x => lab x = i

/-- `F[V_i]` has a non-loop edge (line 9). -/
def ClusterHasEdge {k : ℕ} (F : Multigraph k) (lab : Fin k → ℕ) (i : ℕ) : Prop :=
  ∃ e : Fin F.m, ¬ F.IsLoop e ∧ lab (F.src e) = i ∧ lab (F.dst e) = i

/-- The cluster label of a vertex of `G` lying in `U` (unused value `0` outside `U`). -/
noncomputable def labelOf {n : ℕ} (U : Finset (Fin n)) (lab : Fin U.card → ℕ) (v : Fin n) : ℕ :=
  if h : v ∈ U then lab (vertexPos U v h) else 0

open Classical in
/-- One iteration of the outer loop (lines 3–13) on the residual edge set `R ⊆ E^×(G)` of the
`n`-vertex input `G`, producing the new residual `R'` and the union `Hr` of the cluster outputs
`H_i` (line 12) of this iteration, on the vertex set of `G`. The conductance bound passed to
Algorithm 6 is `ϕ_n / 2` and the decomposition of line 7 meets the bound `ϕ_n`, `n = |V(G)|`. -/
noncomputable def GlobalRound (D : ImplData) (ϕ : ℕ → ℝ) {n : ℕ} (G : Multigraph n) (ε : ℝ) (mode : Mode)
    (R R' : Finset (Fin G.m)) (Hr : Multigraph n) : Prop :=
  ∃ U : Finset (Fin n),
    IsPeeled (edgeSub G R) (2 * (∑ e ∈ R, G.w e) / n) U ∧
    ∃ (t : ℕ) (lab : Fin U.card → ℕ),
      IsExpanderDecomposition (restrictTo (edgeSub G R) U) (ϕ n) t lab ∧
      ∃ Hs : (i : Fin t) → Multigraph (clusterSet lab i).card,
        (∀ i : Fin t, ClusterHasEdge (restrictTo (edgeSub G R) U) lab i →
          ExpanderSparsify D
            (restrictTo ((restrictTo (edgeSub G R) U).cluster (clusterSet lab i))
              (clusterSet lab i))
            (2 * (∑ e ∈ R, G.w e) / n) (ϕ n / 2) ε mode (Hs i)) ∧
        Hr = Multigraph.union (fun i : Fin t =>
          if ClusterHasEdge (restrictTo (edgeSub G R) U) lab i then
            mapGraph (fun x => vertexEmb U (vertexEmb (clusterSet lab i) x)) (Hs i)
          else emptyGraph n) ∧
        R' = R.filter fun e =>
          ¬ (G.src e ∈ U ∧ G.dst e ∈ U ∧ labelOf U lab (G.src e) = labelOf U lab (G.dst e))

/-- An execution of Algorithm 7 on `G` with accuracy `ε` and `mode`, returning `H`: outer
iterations `R_0 = E^×(G), R_1, …, R_T` with `|R_j| ≥ n` for `j < T` and `|R_T| < n`, and
`H` the union of the iteration outputs followed by the final residual edges with their original
weights (line 14). -/
def GlobalSparsify (D : ImplData) (ϕ : ℕ → ℝ) {n : ℕ} (G : Multigraph n) (ε : ℝ) (mode : Mode)
    (H : Multigraph n) : Prop :=
  ∃ (T : ℕ) (Rs : ℕ → Finset (Fin G.m)) (Hr : ℕ → Multigraph n),
    Rs 0 = nonloops G ∧
    (∀ j < T, n ≤ (Rs j).card ∧ GlobalRound D ϕ G ε mode (Rs j) (Rs (j + 1)) (Hr j)) ∧
    (Rs T).card < n ∧
    H = appendGraph (Multigraph.union fun j : Fin T => Hr j) (edgeSub G (Rs T))

/-! ## Algorithm 8 (WeightedSparsify, p.27) -/

/-- The dyadic class `a` of an edge: `2^a ≤ w(e) < 2^{a+1}` for positive weights. -/
noncomputable def dyadicClass {n : ℕ} (G : Multigraph n) (e : Fin G.m) : ℤ :=
  ⌊Real.logb 2 (G.w e)⌋

/-- The occupied classes `{a : E_a ≠ ∅}` of the non-loop edges. -/
noncomputable def occupiedClasses {n : ℕ} (G : Multigraph n) : Finset ℤ :=
  (nonloops G).image (dyadicClass G)

/-- Line 4: `G_a`, the edges of `E_a` with weights divided by `2^a`, on the vertex set of `G`. -/
noncomputable def classGraph {n : ℕ} (G : Multigraph n) (a : ℤ) : Multigraph n :=
  scaleGraph ((2 : ℝ) ^ a)⁻¹ (edgeSub G ((nonloops G).filter fun e => dyadicClass G e = a))

/-- An execution of Algorithm 8 on `G` with accuracy `ε` and `mode`, returning `H`: for every
occupied class `a` (in increasing order), Algorithm 7 on `G_a` returns `H_a`, and `H` is the
edge-disjoint union of the `H_a` with weights multiplied back by `2^a`. -/
def WeightedSparsify (D : ImplData) (ϕ : ℕ → ℝ) {n : ℕ} (G : Multigraph n) (ε : ℝ)
    (mode : Mode) (H : Multigraph n) : Prop :=
  ∃ Hs : Fin (occupiedClasses G).card → Multigraph n,
    (∀ i, GlobalSparsify D ϕ
      (classGraph G ((occupiedClasses G).orderEmbOfFin rfl i)) ε mode (Hs i)) ∧
    H = Multigraph.union fun i =>
      scaleGraph ((2 : ℝ) ^ ((occupiedClasses G).orderEmbOfFin rfl i)) (Hs i)

end DetSpectralSparsify.Dense.Supplement


