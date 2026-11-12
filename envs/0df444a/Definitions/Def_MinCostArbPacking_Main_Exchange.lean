-- Prove2me | Definitions.Def_MinCostArbPacking_Main_Exchange
-- name    : MinCostArbPacking_Main_Exchange
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:31.713181+00:00
-- url     : https://prove2.me/theorems/6af8fef2-bb43-4140-8e0a-b2dc14f80f97
-- title:
--   Exchange graphs, augmenting paths, $\mathrm{OPT}(b)$, proposals, compatibility and vertex prices
-- statement:
--   Let $\mathcal I_1,\mathcal I_2$ be independence systems on a finite set (for instance two matroids) and $c$ real costs. For a set $I$:
--
--   1. The **exchange graph** $D(I)=D_{M_1,M_2}(I)$ has an arc $e\to f$ of weight $c(e)-c(f)$ for $e\notin I$, $f\in I$ with $I-f+e\in\mathcal I_1$, and an arc $f\to e$ of weight $0$ when $I-f+e\in\mathcal I_2$. $X_i(I)=\{e\notin I: I+e\in\mathcal I_i\}$.
--   2. An **augmenting path** is a simple path $(e_0,f_0,\dots,f_{q-1},e_q)$ with $e_0\in X_2(I)$, $e_q\in X_1(I)$. Its **cost** is $\ell(P)=\sum_j c(e_j)-\sum_j c(f_j)$ and its **exchange count** is $q(P)=|P\cap I|$; a **shortest** path minimizes $\ell$, ties broken by minimum $q$. A **negative cycle** is a directed cycle whose arc weights sum to $w(C)<0$.
--   3. $I$ is **extreme** if it is common independent and $c(I)\le c(X)$ for every common independent $X$ with $|X|=|I|$.
--   4. **Partition setting.** For classes $E_v$ ($v\in V$) and $b\ge0$, $N_b$ allows at most $b_v$ elements of $E_v$;
--   $$\mathrm{OPT}(b)=\min\{c(X): X\in\mathcal I,\ |X\cap E_v|=b_v\ \forall v\}\in\mathbb R\cup\{+\infty\},$$
--   $I$ with class counts $b$ is extreme iff $c(I)=\mathrm{OPT}(b)$, $\Delta_u=\mathrm{OPT}(b+\mathbf 1_u)-\mathrm{OPT}(b)$, and an **augmenting path from class $u$** is a simple path in $D_{M,N_b}(I)$ (current capacities $b$) from $E_u\setminus I$ to $X_1(I)$.
--   5. **Graph instance.** $M=\mathcal G^k$ and $E_v$ the arcs entering $v$; $d_v$ is the minimum cost of an augmenting path from $v$ ($+\infty$ if none). The **standing assumptions** of §4.2 say that $I$ is independent, cheapest among independent sets with its indegree vector, has no arc entering $r$, and has indegree $\le k$ elsewhere.
--   6. **Proposals.** In every deficient tight block $T$ a deficient vertex $u_T$ is chosen and $P_T$ is a shortest augmenting path from $u_T$; its last element $e_T$ is the terminal, $A=\{e_T\}$. A set $A'\subseteq A$ is **compatible** if $I^{cr}\cup A'$ is independent in the contracted graph, and executing it gives $I\oplus\bigcup_{T:e_T\in A'}P_T$. One phase of Algorithm 1 executes a maximal compatible set.
--   7. **Prices.** For $h:V\to\mathbb R$, $a(e)=c(e)-h(\mathrm{head}(e))$; invariant (5.1) says $I\in\arg\min\{a(X):X\in\mathcal G^k\}$. $\delta_v=d_v-h(v)$, $L=\max(\{0\}\cup\{\delta_v:\delta_v<\infty\})$ and $h^+(v)=h(v)+\min\{\delta_v,L\}$.
--
--   These objects are the vocabulary of §§3.3, 4.1, 4.2 and 5.
--
--   **Formalization Note** $\mathrm{OPT}$, $\Delta_u$, $d_v$ and $\delta_v$ are extended reals; $\mathrm{OPT}$ is never $-\infty$ on a finite ground set, and $\Delta_u$ is used only when $\mathrm{OPT}(b)=c(I)$ is finite, so $\top-\top$ never occurs. Paths are lists of elements.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.3, p.8; §4.1, pp.9–10; §4.2, pp.11–13; §5.1–5.2, pp.22–23

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Graph

set_option autoImplicit false

/-!
# Exchange graphs, augmenting paths, extremality, proposals and vertex prices

Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.3 (p.8), §4.1 (pp.9–10),
§4.2 (pp.11–13), §5.1–5.2 (pp.22–23).

The exchange graph is defined for two arbitrary independence predicates `Ind₁ Ind₂` on finite sets
of elements, so that it applies both to Mathlib matroids (`fun X => M.Indep ↑X`) and to the
partition-matroid / `𝒢^k` setting of §4. A path is a list of elements (vertices of `D(I)`).
-/

noncomputable section
open Classical

namespace MinCostArbPacking.Main

variable {α : Type}

/-- The independence predicate of a Mathlib matroid on finite sets. -/
def matInd (M : Matroid α) : Finset α → Prop := fun X => M.Indep (X : Set α)

/-- The arcs of the exchange graph `D(I) = D_{M₁,M₂}(I)`: for `x ∉ I`, `y ∈ I`, an arc `x → y` iff
`I - y + x` is independent in `M₁`; for `x ∈ I`, `y ∉ I`, an arc `x → y` iff `I - x + y` is
independent in `M₂`. -/
def exArc (Ind₁ Ind₂ : Finset α → Prop) (I : Finset α) (x y : α) : Prop :=
  (x ∉ I ∧ y ∈ I ∧ Ind₁ (insert x (I.erase y))) ∨ (x ∈ I ∧ y ∉ I ∧ Ind₂ (insert y (I.erase x)))

/-- The weight of an arc of `D(I)`: `c(x) - c(y)` for an `M₁`-arc `x → y` (`x ∉ I`), `0` for an
`M₂`-arc (`x ∈ I`). -/
def exWeight (c : α → ℝ) (I : Finset α) (x y : α) : ℝ := if x ∈ I then 0 else c x - c y

/-- The cost `ℓ(P) = Σ_j c(e_j) - Σ_j c(f_j)` of a path (elements outside `I` count positively,
elements of `I` negatively). -/
def pathCost (c : α → ℝ) (I : Finset α) (P : List α) : ℝ :=
  (P.map fun x => if x ∈ I then -c x else c x).sum

/-- The exchange count `q(P) = |P ∩ I|`. -/
def exchCount (I : Finset α) (P : List α) : ℕ := P.countP (fun x => decide (x ∈ I))

/-- A simple path for the arc relation `R`: a nonempty list of distinct vertices, consecutive ones
joined by arcs. -/
def IsSimplePath (R : α → α → Prop) (P : List α) : Prop := P ≠ [] ∧ P.Nodup ∧ P.IsChain R

/-- A directed cycle for `R`: a nonempty list of distinct vertices, consecutive ones joined by arcs,
and an arc from the last vertex back to the first. -/
def IsCycleE (R : α → α → Prop) (C : List α) : Prop :=
  C ≠ [] ∧ C.Nodup ∧ C.IsChain R ∧ ∀ a ∈ C.head?, ∀ b ∈ C.getLast?, R b a

/-- The weight `w(C)` of a cycle of `D(I)`: the sum of the weights of its arcs (including the arc
from the last vertex back to the first). -/
def cycleWeight (c : α → ℝ) (I : Finset α) (C : List α) : ℝ :=
  ((C.zip (C.rotate 1)).map fun p => exWeight c I p.1 p.2).sum

/-- An augmenting path of `D_{M₁,M₂}(I)`: a simple path `(e₀, f₀, …, e_q)` with `e₀ ∈ X₂(I)` and
`e_q ∈ X₁(I)`. -/
def IsAugPath (Ind₁ Ind₂ : Finset α → Prop) (I : Finset α) (P : List α) : Prop :=
  IsSimplePath (exArc Ind₁ Ind₂ I) P ∧
    (∀ x ∈ P.head?, x ∉ I ∧ Ind₂ (insert x I)) ∧ (∀ x ∈ P.getLast?, x ∉ I ∧ Ind₁ (insert x I))

/-- `P` is shortest among the paths satisfying `Q`: minimum cost `ℓ`, ties broken by minimum
exchange count `q`. -/
def IsShortestAmong (Q : List α → Prop) (c : α → ℝ) (I : Finset α) (P : List α) : Prop :=
  Q P ∧ ∀ P', Q P' → pathCost c I P ≤ pathCost c I P' ∧
    (pathCost c I P = pathCost c I P' → exchCount I P ≤ exchCount I P')

/-- Common independence. -/
def CommonIndep (Ind₁ Ind₂ : Finset α → Prop) (X : Finset α) : Prop := Ind₁ X ∧ Ind₂ X

/-- `I` is extreme: common independent and `c(I) ≤ c(X)` for every common independent `X` with
`|X| = |I|`. -/
def IsExtreme (Ind₁ Ind₂ : Finset α → Prop) (c : α → ℝ) (I : Finset α) : Prop :=
  CommonIndep Ind₁ Ind₂ I ∧ ∀ X, CommonIndep Ind₁ Ind₂ X → X.card = I.card → cost c I ≤ cost c X

/-- `I` is a common independent set of maximum cardinality. -/
def IsMaxCommon (Ind₁ Ind₂ : Finset α → Prop) (I : Finset α) : Prop :=
  CommonIndep Ind₁ Ind₂ I ∧ ∀ X, CommonIndep Ind₁ Ind₂ X → X.card ≤ I.card

/-! ### The partition setting of §4.1 -/

variable {V : Type}

/-- Class counts `|X ∩ E_v|`, where `E_v = cls⁻¹(v)`. -/
def classCount (cls : α → V) (X : Finset α) (v : V) : ℕ := (X.filter (fun x => cls x = v)).card

/-- Independence in the partition matroid `N_b`: at most `b_v` elements in class `v`. -/
def partIndep (cls : α → V) (b : V → ℕ) (X : Finset α) : Prop := ∀ v, classCount cls X v ≤ b v

/-- `OPT(b) = min{c(X) : X independent in M, |X ∩ E_v| = b_v ∀ v}`, and `+∞` if there is no such
`X` (extended reals; never `-∞` on a finite ground set). -/
def OPT (Ind : Finset α → Prop) (cls : α → V) (c : α → ℝ) (b : V → ℕ) : EReal :=
  sInf {z : EReal | ∃ X : Finset α, Ind X ∧ (∀ v, classCount cls X v = b v) ∧ z = (cost c X : EReal)}

/-- `I` is extreme for `M` and `N_b`, `b` its class counts: independent with `c(I) = OPT(b)`. -/
def ExtremeP (Ind : Finset α → Prop) (cls : α → V) (c : α → ℝ) (I : Finset α) : Prop :=
  Ind I ∧ (cost c I : EReal) = OPT Ind cls c (classCount cls I)

/-- `b + 1_U`. -/
def addOne (b : V → ℕ) (U : Finset V) : V → ℕ := fun v => b v + if v ∈ U then 1 else 0

/-- An augmenting path from class `u` in `D(I) = D_{M,N_b}(I)` with `b` the class counts of `I`
(Remark 4.1: the current capacities): a simple path `(e₀, f₀, …, e_q)` with `e₀ ∈ E_u ∖ I` and
`e_q ∈ X₁(I)`. -/
def IsAugPathFrom (Ind : Finset α → Prop) (cls : α → V) (I : Finset α) (u : V) (P : List α) :
    Prop :=
  IsSimplePath (exArc Ind (partIndep cls (classCount cls I)) I) P ∧
    (∀ x ∈ P.head?, x ∉ I ∧ cls x = u) ∧ (∀ x ∈ P.getLast?, x ∉ I ∧ Ind (insert x I))

/-- `∆_u = OPT(b + 1_u) - OPT(b)` (extended reals). -/
def Delta (Ind : Finset α → Prop) (cls : α → V) (c : α → ℝ) (b : V → ℕ) (u : V) : EReal :=
  OPT Ind cls c (addOne b {u}) - OPT Ind cls c b

/-- The minimum cost of an augmenting path from class `u`, `+∞` if none exists. -/
def minAugCost (Ind : Finset α → Prop) (cls : α → V) (c : α → ℝ) (I : Finset α) (u : V) : EReal :=
  sInf {z : EReal | ∃ P, IsAugPathFrom Ind cls I u P ∧ z = (pathCost c I P : EReal)}

/-! ### The graph instance: `M = 𝒢^k`, classes `E_v` = arcs entering `v` -/

variable {E : Type}

namespace Digraph

/-- An augmenting path from `u` in `D(I)` for `M = 𝒢^k` and the indegree partition. -/
def AugFrom (G : Digraph V E) (k : ℕ) (I : Finset E) (u : V) (P : List E) : Prop :=
  IsAugPathFrom (G.IndepK k) G.head I u P

/-- A shortest augmenting path from `u` (lexicographic in `(ℓ, q)`). -/
def ShortestFrom (G : Digraph V E) (k : ℕ) (c : E → ℝ) (I : Finset E) (u : V) (P : List E) :
    Prop :=
  IsShortestAmong (G.AugFrom k I u) c I P

/-- `d_v`: the minimum cost of an augmenting path from `v` in `D(I)`, `+∞` if none. -/
def dCost (G : Digraph V E) (k : ℕ) (c : E → ℝ) (I : Finset E) (v : V) : EReal :=
  minAugCost (G.IndepK k) G.head c I v

/-- The standing assumptions of §4.2 (p.11): `I` is independent in `𝒢^k`, cheapest among
independent sets with its indegree vector, no arc of `I` enters `r`, and every other vertex has
indegree at most `k`. -/
def Standing (G : Digraph V E) (k : ℕ) (r : V) (c : E → ℝ) (I : Finset E) : Prop :=
  G.IndepK k I ∧ ExtremeP (G.IndepK k) G.head c I ∧ G.inDeg I r = 0 ∧
    ∀ v, v ≠ r → G.inDeg I v ≤ k

/-- §3.1 / Algorithm 1 line 1: no loops and no arcs entering `r`. -/
def NoLoopNoRootArc (G : Digraph V E) (r : V) : Prop :=
  ∀ e, G.tail e ≠ G.head e ∧ G.head e ≠ r

variable [Fintype V] [DecidableEq V] [DecidableEq E]

/-- The deficient tight blocks. -/
def deficientBlocks (G : Digraph V E) (k : ℕ) (r : V) (I : Finset E) : Finset (Finset V) :=
  Finset.univ.filter (fun T => G.IsTightBlock k I T ∧ 0 < G.defiSet k r I T)

/-- A proposal system (p.11): in every deficient block `T` a deficient vertex `u T ∈ T` is chosen,
and `P T` is a shortest augmenting path from `u T` (its proposal). -/
def IsProposalSystem (G : Digraph V E) (k : ℕ) (r : V) (c : E → ℝ) (I : Finset E)
    (u : Finset V → V) (P : Finset V → List E) : Prop :=
  ∀ T ∈ G.deficientBlocks k r I, u T ∈ T ∧ 0 < G.defi k r I (u T) ∧ G.ShortestFrom k c I (u T) (P T)

/-- The set `A = {e_T}` of terminals (last elements) of the proposals of the deficient blocks. -/
def terminals (G : Digraph V E) (k : ℕ) (r : V) (I : Finset E) (P : Finset V → List E) :
    Finset E :=
  (G.deficientBlocks k r I).biUnion (fun T => (P T).getLast?.toFinset)

/-- `A' ⊆ A` is compatible if `I^cr ∪ A'` is independent in the contracted graph. -/
def Compatible (G : Digraph V E) (k : ℕ) (r : V) (I : Finset E) (P : Finset V → List E)
    (A' : Finset E) : Prop :=
  A' ⊆ G.terminals k r I P ∧ (G.contract k I).IndepK k (G.crossingPart k I ∪ A')

/-- A maximal compatible set of terminals. -/
def MaximalCompatible (G : Digraph V E) (k : ℕ) (r : V) (I : Finset E) (P : Finset V → List E)
    (A' : Finset E) : Prop :=
  G.Compatible k r I P A' ∧ ∀ A'', A' ⊆ A'' → G.Compatible k r I P A'' → A'' = A'

/-- The deficient blocks whose terminal belongs to `A'`. -/
def chosenBlocks (G : Digraph V E) (k : ℕ) (r : V) (I : Finset E) (P : Finset V → List E)
    (A' : Finset E) : Finset (Finset V) :=
  (G.deficientBlocks k r I).filter (fun T => ∃ e ∈ (P T).getLast?, e ∈ A')

/-- Executing `A'`: `I ⊕ ⋃_{T : e_T ∈ A'} P_T`. -/
def execute (G : Digraph V E) (k : ℕ) (r : V) (I : Finset E) (P : Finset V → List E)
    (A' : Finset E) : Finset E :=
  symmDiff I ((G.chosenBlocks k r I P A').biUnion (fun T => (P T).toFinset))

/-- `U = {u_T : e_T ∈ A'}`. -/
def chosenVertices (G : Digraph V E) (k : ℕ) (r : V) (I : Finset E) (u : Finset V → V)
    (P : Finset V → List E) (A' : Finset E) : Finset V :=
  (G.chosenBlocks k r I P A').image u

/-- One phase of Algorithm 1 (pp.11–13): `I` satisfies the §4.2 invariants and has positive total
deficiency, a proposal system and a maximal compatible set of terminals are chosen, and `I'` is the
result of executing it. -/
def PhaseStep (G : Digraph V E) (k : ℕ) (r : V) (c : E → ℝ) (I I' : Finset E) : Prop :=
  G.Standing k r c I ∧ 0 < G.defiSet k r I Finset.univ ∧
    ∃ (u : Finset V → V) (P : Finset V → List E) (A' : Finset E),
      G.IsProposalSystem k r c I u P ∧ G.MaximalCompatible k r I P A' ∧ I' = G.execute k r I P A'

/-! ### Vertex prices (§5) -/

/-- Adjusted cost `a(e) = c(e) - h(head(e))`. -/
def adj (G : Digraph V E) (c : E → ℝ) (h : V → ℝ) : E → ℝ := fun e => c e - h (G.head e)

/-- The price invariant (5.1): `I ∈ argmin{a(X) : X independent in 𝒢^k}`. -/
def PriceInv (G : Digraph V E) (k : ℕ) (c : E → ℝ) (h : V → ℝ) (I : Finset E) : Prop :=
  G.IndepK k I ∧ ∀ X, G.IndepK k X → cost (G.adj c h) I ≤ cost (G.adj c h) X

/-- The adjusted distance `δ_v = d_v - h(v)` (`+∞` when `d_v = +∞`). -/
def delta (G : Digraph V E) (k : ℕ) (c : E → ℝ) (h : V → ℝ) (I : Finset E) (v : V) : EReal :=
  G.dCost k c I v - (h v : EReal)

/-- `L = max({0} ∪ {δ_v : δ_v < +∞})`. -/
def capL (G : Digraph V E) (k : ℕ) (c : E → ℝ) (h : V → ℝ) (I : Finset E) : ℝ :=
  max 0 (⨆ v, if G.delta k c h I v = ⊤ then (0 : ℝ) else (G.delta k c h I v).toReal)

/-- The updated prices `h⁺(v) = h(v) + min{δ_v, L}`. -/
def hplus (G : Digraph V E) (k : ℕ) (c : E → ℝ) (h : V → ℝ) (I : Finset E) (v : V) : ℝ :=
  h v + (min (G.delta k c h I v) ((G.capL k c h I : ℝ) : EReal)).toReal

end Digraph

end MinCostArbPacking.Main


