-- Prove2me | Definitions.Def_ComplexityUnpred_Catalytic_WeakExcess
-- name    : ComplexityUnpred_Catalytic_WeakExcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:02:39.08761+00:00
-- url     : https://prove2.me/theorems/0ce2228b-7d2d-4470-a593-274705d7650f
-- title:
--   Deterministic hypercube digraphs, the predictors P(G), and the search problem WeakExcess (Definitions 4.2, 4.3, 4.5)
-- statement:
--   A **deterministic hypercube digraph of dimension $n$ with $\ell$-bit labels** is a directed multigraph $G=(V,E,\mathrm{lab},\mathrm{ind})$ with $V=\{0,1\}^n$, a multiset $E$ of edges (parallel copies and self-loops allowed), labels $\mathrm{lab}:E\to\{0,1\}^\ell$ and a map $\mathrm{ind}:\{0,1\}^\ell\to[n]$ such that (2) for every vertex $v$ and label $l$ at most one edge (counting copies) leaves $v$ with label $l$, and (3) every edge $e=(v,v')$ satisfies $\{i: v_i\neq v'_i\}\subseteq\{\mathrm{ind}(\mathrm{lab}(e))\}$. Degrees count edge copies, a self-loop contributing $1$ to both. $\mathrm{EdgeExists}(v,l)$ holds if some non-self-loop edge leaves $v$ with label $l$.
--
--   The **predictors of $G$** are $\mathcal P(G)=(P_{lb}(G))_{l\in\{0,1\}^\ell,b\in\{0,1\}}$, where $P_{lb}(G)$ is the middle-bit predictor at index $\mathrm{ind}(l)$ with
--   $$P_{lb}(G)(s)=\begin{cases}1&\text{if }\mathrm{EdgeExists}(s^{\mathrm{ind}(l),0},l)\wedge\neg\mathrm{EdgeExists}(s^{\mathrm{ind}(l),1},l),\\0&\text{if }\mathrm{EdgeExists}(s^{\mathrm{ind}(l),1},l)\wedge\neg\mathrm{EdgeExists}(s^{\mathrm{ind}(l),0},l),\\b&\text{otherwise.}\end{cases}$$
--
--   **WeakExcess**: an instance consists of $n,\ell\ge1$ in unary, a circuit $C$ on $n+\ell$ inputs (the vertex bits, then the label bits) and the table of $\mathrm{ind}:\{0,1\}^\ell\to[n]$ (one entry per label, labels in lexicographic order, entries 1-based, each in binary); it describes the hidden deterministic hypercube digraph $G$ with this $\mathrm{ind}$ and $\mathrm{EdgeExists}(v,l)=C(v,l)$. A solution is the $n$-bit string of a vertex $v$ with $\text{out-degree}_G(v)\ge\text{in-degree}_G(v)$.
--
--   **Formalization Note** Edges are stored as triples (tail, head, label) in a `Multiset`; indices are 0-based. The hidden graph is taken to be `HypercubeDigraph.ofOracle`: one edge $v\to v\oplus\mathrm{ind}(l)$ labelled $l$ for each $(v,l)$ with $C(v,l)=1$. It is a deterministic hypercube digraph with $\mathrm{EdgeExists}=C$, and every deterministic hypercube digraph with the same $\mathrm{ind}$ and $\mathrm{EdgeExists}$ has the same non-self-loop edges (by (2) and (3)) and differs only by self-loops, which change no $\text{out-degree}-\text{in-degree}$; so the answer set is the paper's whichever hidden graph is meant, and WeakExcess is total. The fallback index of `indFn` is never used on a well-formed instance.
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 30, Definitions 4.2, 4.3; pp. 31–32, Definition 4.5

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_ComplexityUnpred_Catalytic_Predictor
import Definitions.Def_ComplexityUnpred_Catalytic_Circuit

namespace ComplexityUnpred.Catalytic

open Classical

/-! Agarwala, Dorfman, *The Complexity of Unpredictability*, arXiv:2611.05956v1, §4.1:
Definition 4.2 (deterministic hypercube digraph, p. 30), Definition 4.3 (WeakExcess, p. 30) and
Definition 4.5 (the predictors `P(G)`, pp. 31–32). Indices are 0-based (`Fin n`); the paper's
`ind(l) ∈ [n]` is `ind l + 1`. -/

/-- A directed multigraph on the vertex set `V = {0,1}ⁿ` with `ℓ`-bit edge labels and a label
index map `ind : {0,1}^ℓ → [n]`. Each edge is recorded as `(tail, head, label)`; `E` is a
multiset, so parallel copies are kept, and self-loops are allowed. -/
structure HypercubeDigraph (n ℓ : ℕ) where
  E : Multiset ((Fin n → Bool) × (Fin n → Bool) × (Fin ℓ → Bool))
  ind : (Fin ℓ → Bool) → Fin n

namespace HypercubeDigraph

variable {n ℓ : ℕ}

/-- **Definition 4.2** (p. 30): `G` is a deterministic hypercube digraph of dimension `n` with
`ℓ`-bit labels: (2) for each vertex `v` and label `l` at most one edge (counting copies) leaves
`v` with label `l`; (3) every edge `e = (v, v')` changes at most the coordinate `ind(lab(e))`,
i.e. `{i | vᵢ ≠ v'ᵢ} ⊆ {ind(lab(e))}`. -/
def IsDeterministic (G : HypercubeDigraph n ℓ) : Prop :=
  (∀ v l, (G.E.filter (fun e => e.1 = v ∧ e.2.2 = l)).card ≤ 1) ∧
  (∀ e ∈ G.E, ∀ i, e.1 i ≠ e.2.1 i → i = G.ind e.2.2)

/-- Out-degree: the number of edge copies with tail `v` (a self-loop counts once). -/
noncomputable def outDeg (G : HypercubeDigraph n ℓ) (v : Fin n → Bool) : ℕ :=
  G.E.countP (fun e => e.1 = v)

/-- In-degree: the number of edge copies with head `v` (a self-loop counts once). -/
noncomputable def inDeg (G : HypercubeDigraph n ℓ) (v : Fin n → Bool) : ℕ :=
  G.E.countP (fun e => e.2.1 = v)

/-- `EdgeExists(v, l)`: some non-self-loop edge leaves `v` with label `l` (p. 30). -/
def EdgeExists (G : HypercubeDigraph n ℓ) (v : Fin n → Bool) (l : Fin ℓ → Bool) : Prop :=
  ∃ e ∈ G.E, e.1 = v ∧ e.2.2 = l ∧ e.2.1 ≠ v

/-- **Definition 4.5** (pp. 31–32): the middle-bit predictor `P_{lb}(G)` over `{0,1}ⁿ` at index
`ind(l)`: on `s ∈ {0,1}^{n−1}` it outputs `1` if `EdgeExists(s^{ind(l),0}, l)` and not
`EdgeExists(s^{ind(l),1}, l)`; `0` if `EdgeExists(s^{ind(l),1}, l)` and not
`EdgeExists(s^{ind(l),0}, l)`; and `b` otherwise. -/
noncomputable def predictor (G : HypercubeDigraph n ℓ) (l : Fin ℓ → Bool) (b : Bool) :
    MiddleBitPredictor n where
  ind := G.ind l
  P := fun s =>
    if G.EdgeExists (insertAt s (G.ind l) false) l ∧
        ¬ G.EdgeExists (insertAt s (G.ind l) true) l then true
    else if G.EdgeExists (insertAt s (G.ind l) true) l ∧
        ¬ G.EdgeExists (insertAt s (G.ind l) false) l then false
    else b

/-- The family `P(G) := (P_{lb}(G))_{l ∈ {0,1}^ℓ, b ∈ {0,1}}`, indexed by `(l, b)`. -/
noncomputable def predictors (G : HypercubeDigraph n ℓ) :
    (Fin ℓ → Bool) × Bool → MiddleBitPredictor n :=
  fun p => G.predictor p.1 p.2

/-- The hypercube digraph described by an edge oracle `O` and an index map `ind`: for every
vertex `v` and label `l` with `O(v, l) = 1` one edge from `v` to `v ⊕ ind(l)` with label `l`. It
is deterministic, has no self-loops, and `EdgeExists(v, l) ↔ O(v, l) = 1`; every deterministic
hypercube digraph with the same `ind` and the same `EdgeExists` differs from it only by
self-loops, which change no `out-degree − in-degree`. -/
noncomputable def ofOracle (ind : (Fin ℓ → Bool) → Fin n)
    (O : (Fin n → Bool) → (Fin ℓ → Bool) → Bool) : HypercubeDigraph n ℓ where
  E := (Finset.univ.filter (fun p : (Fin n → Bool) × (Fin ℓ → Bool) => O p.1 p.2 = true)).val.map
    (fun p => (p.1, flipAt p.1 (ind p.2), p.2))
  ind := ind

end HypercubeDigraph

/-- The data of a WeakExcess instance: `n`, `ℓ`, the circuit `C` on `n + ℓ` inputs (the
vertex `v` first, then the label `l`), and the table of `ind`: its entry number `k` (0-based) is
`ind(l) ∈ [n]` (1-based, as in the paper) for the label `l` whose bits `l₁ … l_ℓ`, read as a
binary number with `l₁` most significant, equal `k` (lexicographic order of the labels). -/
structure WeakExcessInstance where
  n : ℕ
  ℓ : ℕ
  C : Circuit
  indTab : List ℕ

/-- The position of the label `l ∈ {0,1}^ℓ` in lexicographic order. -/
def labelIndex {ℓ : ℕ} (l : Fin ℓ → Bool) : ℕ :=
  ∑ i : Fin ℓ, if l i then 2 ^ (ℓ - 1 - i.val) else 0

/-- Well-formed instance: `n, ℓ ≥ 1`, `C` well formed on `n + ℓ` inputs, and the table has one
entry in `[n]` for each of the `2^ℓ` labels. -/
def WeakExcessInstance.WF (I : WeakExcessInstance) : Prop :=
  1 ≤ I.n ∧ 1 ≤ I.ℓ ∧ I.C.WF (I.n + I.ℓ) ∧ I.indTab.length = 2 ^ I.ℓ ∧
    ∀ k ∈ I.indTab, 1 ≤ k ∧ k ≤ I.n

/-- Instance code: `n` and `ℓ` in unary, the code of `C`, then the table (`encList encNat`). -/
def WeakExcessInstance.encode (I : WeakExcessInstance) : List Bool :=
  encUnary I.n ++ encUnary I.ℓ ++ I.C.encode ++ encList encNat I.indTab

/-- The index map `ind : {0,1}^ℓ → [n]` of a well-formed instance, 0-based. (The fallback `0`
is never used on a well-formed instance.) -/
def WeakExcessInstance.indFn (I : WeakExcessInstance) (h : I.WF) (l : Fin I.ℓ → Bool) :
    Fin I.n :=
  if hk : I.indTab.getD (labelIndex l) 1 - 1 < I.n then ⟨I.indTab.getD (labelIndex l) 1 - 1, hk⟩
  else ⟨0, h.1⟩

/-- `C(v, l)`: the circuit evaluated on the bits of `v` followed by the bits of `l`. -/
def WeakExcessInstance.edgeOracle (I : WeakExcessInstance) (v : Fin I.n → Bool)
    (l : Fin I.ℓ → Bool) : Bool :=
  I.C.eval (List.ofFn v ++ List.ofFn l)

/-- The hidden deterministic hypercube digraph of a well-formed instance, up to self-loops:
`EdgeExists(v, l) = C(v, l)`. -/
noncomputable def WeakExcessInstance.graph (I : WeakExcessInstance) (h : I.WF) :
    HypercubeDigraph I.n I.ℓ :=
  HypercubeDigraph.ofOracle (I.indFn h) I.edgeOracle

/-- **WeakExcess** (Definition 4.3, p. 30). Valid instances are the codes of well-formed
instances; an answer is the `n`-bit string of a vertex `v` with
`out-degree_G(v) ≥ in-degree_G(v)` in the hidden graph `G` with `EdgeExists = C`. -/
noncomputable def WeakExcess : TetrisHard.Rows.SearchProblem where
  valid s := ∃ I : WeakExcessInstance, I.WF ∧ s = I.encode
  answer s t := ∃ (I : WeakExcessInstance) (h : I.WF), s = I.encode ∧
    ∃ v : Fin I.n → Bool, t = List.ofFn v ∧ (I.graph h).inDeg v ≤ (I.graph h).outDeg v

end ComplexityUnpred.Catalytic


