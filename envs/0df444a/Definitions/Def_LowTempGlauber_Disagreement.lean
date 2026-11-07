-- Prove2me | Definitions.Def_LowTempGlauber_Disagreement
-- name    : LowTempGlauber_Disagreement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:00.590203+00:00
-- url     : https://prove2.me/theorems/dbba8158-f14e-4147-b266-17ea5a9a44da
-- title:
--   Disagreement components, tree excess, the bad event $B_{\ell,r}$, $b_{G,\ell,r}(s)$, Lemma-8 orderings and the component switch $\gamma_{I,J,C}$
-- statement:
--   Let $G$ be a graph on $V^+\sqcup V^-$ and $I,J$ two configurations.
--
--   1. $I\oplus J$ is the set of vertices where $I$ and $J$ differ, and $\mathcal C(I,J)$ is the set of (vertex sets of) connected components of the induced graph $G[I\oplus J]$. A set $C$ is such a component when $C\subseteq I\oplus J$, $G[C]$ is connected, and every vertex of $I\oplus J$ adjacent to $C$ lies in $C$.
--   2. The **tree excess** of $C$ is $\operatorname{exc}(C)=|E(G[C])|-|C|+1$.
--   3. The **bad event** (3): $(I,J)\in B_{\ell,r}$ if some $C\in\mathcal C(I,J)$ has $|C|>\ell$ or $\operatorname{exc}(C)>r$; and $b_{G,\ell,r}(s)=\Pr[(I,J)\in B_{\ell,r}]$ for independent $I,J\sim\mu^+_{G,s}$.
--   4. A **Lemma-8 ordering** of a vertex set $C$ lists $C$ without repetition so that, for every $i$, the number of edges of $G[C]$ between the first $i$ listed vertices and the others is at most $d\lceil\log_2|C|\rceil+\operatorname{exc}(C)$.
--   5. The **component switch** $\gamma_{I,J,C}$ (Definition 9): fix a vertex labelling and an ordering of $C$, and let $A=I\cap C$, $B=J\cap C$. Sweep through $C$ in that order starting from $I$; a vertex of $A$ is deleted if still occupied; for a vertex $v$ of $B$, first its still-occupied $A$-neighbours are deleted one at a time in increasing label order, then $v$ is inserted. The switch is the sequence of configurations visited, and a transition $Y\to Y'$ is **traversed** by it when $Y'$ immediately follows $Y$.
--
--   These are the ingredients of the canonical-path argument (Lemma 10) that turns small, tree-like disagreement components between two equilibrium samples into a weak Poincaré inequality for Glauber dynamics.
--
--   **Formalization Note** Definition 9 writes the switch as $I_0\to\dots\to I_\ell$, but the sweep can make more than $\ell$ moves when $A$-neighbours are deleted; the formal path lists every move. The bad event uses "$>r$" as in (3); the recall on p.34 writes "$\ge r$".
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), §3, (3), p.9; Lemma 8, Definition 9, Lemma 10, p.10

import Mathlib
import Definitions.Def_LowTempGlauber_HardCore

open Classical

namespace LowTempGlauber

/-!
# Disagreement components, tree excess, the bad event `B_{ℓ,r}`, and component switches

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), §3, (3), p.9;
Lemma 8, Definition 9 and Lemma 10, p.10.

**Formalization Note.**
* `disagree σ τ` is `I ⊕ J`, the vertices where the configurations differ.
* `IsComponent G S C` says that `C` is the vertex set of a connected component of the induced graph
  `G[S]`: `C ⊆ S`, `G[C]` is connected (hence `C ≠ ∅`), and every `S`-vertex adjacent to `C` lies in
  `C`. `components G S` is the finite set of these, `C(I, J) = components G (I ⊕ J)`.
* `edgesIn G C` counts the edges of `G` with both ends in `C`; `exc G C = |E(G[C])| − |C| + 1` is the
  tree excess of `G[C]` (p.9), an integer.
* `BadComp G ℓ r σ τ` is `(I, J) ∈ B_{ℓ,r}` of (3), p.9: some component has more than `ℓ` vertices or
  tree excess **greater than** `r`. (The recall on p.34 writes "≥ r"; (3) is used.)
* `bBad G λ ℓ r s = b_{G,ℓ,r}(s) = Pr[(I, J) ∈ B_{ℓ,r}]` for independent `I, J ∼ μ⁺_{G,s}`.
* `cutSize G C l i` is the number of edges of `G[C]` between the first `i` vertices of the list `l`
  and the rest of `C`. `IsCutOrder G d C l` says that `l` lists `C` without repetition and every such
  cut has at most `d⌈log₂|C|⌉ + exc(C)` edges: the conclusion of Lemma 8 for `G[C]`
  (`⌈log₂ ℓ⌉ = Nat.clog 2 ℓ`).
* The component switch of Definition 9, p.10: given the vertex labelling `lab` and the order `l` of
  `C`, `switchPath G lab C I J l` is the list of configurations `I = I₀, I₁, …` visited by the sweep:
  an `A = I ∩ C` vertex is deleted if still occupied; for a `B = J ∩ C` vertex `v`, its still-occupied
  `A`-neighbours are deleted one by one in increasing label order and then `v` is inserted. The page
  writes the path as `I₀ → ⋯ → I_ℓ`, but the sweep can make more than `ℓ` moves when `A`-neighbours
  are deleted; the list records every move. `Traverses Y Y' path` says `Y → Y'` is one of its moves.
-/

open ExpanderBIS.RandomHardCore

/-- `I ⊕ J`: the vertices where `σ` and `τ` disagree. -/
noncomputable def disagree {n : ℕ} (σ τ : Vertex n → Bool) : Finset (Vertex n) :=
  Finset.univ.filter (fun v => σ v ≠ τ v)

/-- `C` is the vertex set of a connected component of `G[S]`. -/
def IsComponent {V : Type*} (G : SimpleGraph V) (S C : Finset V) : Prop :=
  C ⊆ S ∧ (G.induce (C : Set V)).Connected ∧ ∀ u ∈ C, ∀ w ∈ S, G.Adj u w → w ∈ C

/-- The vertex sets of the connected components of `G[S]`. -/
noncomputable def components {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    Finset (Finset V) :=
  Finset.univ.filter (IsComponent G S)

/-- The number of edges of `G` with both ends in `C`. -/
noncomputable def edgesIn {V : Type*} [Fintype V] (G : SimpleGraph V) (C : Finset V) : ℕ :=
  (Finset.univ.filter (fun e : Sym2 V => e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ C)).card

/-- The tree excess `exc(C) = |E(C)| − |V(C)| + 1` of `G[C]`, p.9. -/
noncomputable def exc {V : Type*} [Fintype V] (G : SimpleGraph V) (C : Finset V) : ℤ :=
  (edgesIn G C : ℤ) - (C.card : ℤ) + 1

/-- `(I, J) ∈ B_{ℓ,r}`, (3), p.9: some component of `G[I ⊕ J]` has more than `ℓ` vertices or tree
excess greater than `r`. -/
def BadComp {n : ℕ} (G : SimpleGraph (Vertex n)) (ℓ r : ℕ) (σ τ : Vertex n → Bool) : Prop :=
  ∃ C ∈ components G (disagree σ τ), ℓ < C.card ∨ (r : ℤ) < exc G C

/-- `b_{G,ℓ,r}(s) = Pr[(I, J) ∈ B_{ℓ,r}]` for independent `I, J ∼ μ⁺_{G,s}`, p.9. -/
noncomputable def bBad {n : ℕ} (G : SimpleGraph (Vertex n)) (lam : ℝ) (ℓ r : ℕ) (s : ℝ) : ℝ :=
  ∑ σ, ∑ τ, if BadComp G ℓ r σ τ then muPlus G lam s σ * muPlus G lam s τ else 0

/-- The number of edges of `G[C]` between the first `i` entries of `l` and the rest of `C`. -/
noncomputable def cutSize {V : Type*} [Fintype V] (G : SimpleGraph V) (C : Finset V) (l : List V)
    (i : ℕ) : ℕ :=
  ((C ×ˢ C).filter (fun p => G.Adj p.1 p.2 ∧ p.1 ∈ l.take i ∧ p.2 ∉ l.take i)).card

/-- `l` is an ordering of `C` satisfying the cut bound of Lemma 8, p.10, for `G[C]`: every prefix cut
has at most `d⌈log₂|C|⌉ + exc(C)` edges. -/
def IsCutOrder {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) (C : Finset V) (l : List V) :
    Prop :=
  l.Nodup ∧ l.toFinset = C ∧
    ∀ i ≤ l.length, (cutSize G C l i : ℤ) ≤ ((d * Nat.clog 2 C.card : ℕ) : ℤ) + exc G C

/-- The configurations visited when deleting the vertices of `l` one at a time from `Y`. -/
def deleteSeq {n : ℕ} : (Vertex n → Bool) → List (Vertex n) → List (Vertex n → Bool)
  | _, [] => []
  | Y, u :: us => Function.update Y u false :: deleteSeq (Function.update Y u false) us

/-- The still-occupied `A`-neighbours of `v` (`A = I ∩ C`), in increasing label order. -/
noncomputable def occANbrs {n : ℕ} (G : SimpleGraph (Vertex n)) (lab : Vertex n ≃ Fin (n + n))
    (C : Finset (Vertex n)) (I Y : Vertex n → Bool) (v : Vertex n) : List (Vertex n) :=
  ((Finset.univ.filter (fun w => w ∈ C ∧ I w = true ∧ G.Adj v w ∧ Y w = true)).image lab).sort
      (· ≤ ·) |>.map lab.symm

/-- The sweep of Definition 9, p.10, through the list `l`, from the current configuration `Y`: the
configurations after each Glauber move. -/
noncomputable def sweep {n : ℕ} (G : SimpleGraph (Vertex n)) (lab : Vertex n ≃ Fin (n + n))
    (C : Finset (Vertex n)) (I J : Vertex n → Bool) :
    (Vertex n → Bool) → List (Vertex n) → List (Vertex n → Bool)
  | _, [] => []
  | Y, u :: us =>
      if I u = true then
        if Y u = true then
          Function.update Y u false :: sweep G lab C I J (Function.update Y u false) us
        else sweep G lab C I J Y us
      else if J u = true then
        let dels := deleteSeq Y (occANbrs G lab C I Y u)
        let Y₁ := dels.getLast?.getD Y
        dels ++ Function.update Y₁ u true :: sweep G lab C I J (Function.update Y₁ u true) us
      else sweep G lab C I J Y us

/-- The component switch `γ_{I,J,C}` of Definition 9, p.10: `I` followed by the configurations of the
sweep through `C` in the order `l`. -/
noncomputable def switchPath {n : ℕ} (G : SimpleGraph (Vertex n)) (lab : Vertex n ≃ Fin (n + n))
    (C : Finset (Vertex n)) (I J : Vertex n → Bool) (l : List (Vertex n)) :
    List (Vertex n → Bool) :=
  I :: sweep G lab C I J I l

/-- The transition `Y → Y'` is one of the moves of the path. -/
def Traverses {α : Type*} (Y Y' : α) (path : List α) : Prop :=
  [Y, Y'] <:+: path

end LowTempGlauber


