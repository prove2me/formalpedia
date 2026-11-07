-- Prove2me | Definitions.Def_MinSumClust_Alg3State
-- name    : MinSumClust_Alg3State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:36.894722+00:00
-- url     : https://prove2.me/theorems/51dd9c0a-832e-49c1-90ae-b9992729835c
-- title:
--   Algorithm 3: parameters, states and the cluster-based dependency forest
-- statement:
--   **Parameters.** Algorithm 3 runs on clients $D=\{0,\dots,n-1\}$ with a distance $d$, an opening cost $f$ and three constants $\gamma_{DC},\gamma_{IC},r_S$. Its standing assumptions (§4) are: $d$ is a metric, $f>0$, and $\gamma_{DC},\gamma_{IC},r_S>1$.
--
--   **States.** A state records the current time $\theta$, the dual vector $\alpha$, the set $A$ of active clients, the opened clusters $S_0,S_1,\dots$ in opening order, each with the set $D_A(S_t)=S_t\cap A$ of clients active when it was opened, and the indirect connections $C_I(j)$.
--
--   **The dependency forest** $(V,E)$ (pp.20, 24) is determined by the openings. Its nodes are a node $\upsilon_i$ for each client $i$ that lies in no $D_A(S)$, and one node per opened cluster $S$, with involved clients $D_V(\upsilon_i)=\{i\}$, $D_V(\upsilon_S)=D_A(S)$ and original clusters $S_V(\upsilon_i)=\bot$, $S_V(\upsilon_S)=S$. When $S$ is opened, the client nodes of $D_A(S)$ are removed, the node $\upsilon_S$ is created, and every other node that is still a root and whose tree contains a node $\upsilon''$ with $D_V(\upsilon'')\cap S\ne\emptyset$ gets the parent $\upsilon_S$.
--
--   **Preorder and available sets.** $i\preceq j$ (Definition 9) iff the node involving $i$ equals or is a descendant of the node involving $j$. A set $S$ is **available** (Definition 8) if $i\preceq j$ and $i\in S$ imply $j\in S$. The **current root** of $i$ (Definition 11) is the root of the tree containing the node involving $i$.
--
--   **Formalization Note** The forest is not stored but recomputed from the opening history by replaying the update rule; nodes are client indices or cluster positions in the history.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), §4.1, pp.19–21 (PDF pp.21–23): Definitions 8, 9, 11, 12; Algorithm 3, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_IsMetric

namespace MinSumClust

/-- **Parameters of Algorithm 3**: a distance on the clients `Fin n`, the opening cost `f` and the
three constants `γ_DC, γ_IC, r_S`.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), §4, pp.19–24 (PDF pp.21–26). -/
structure Alg3Params (n : ℕ) where
  /-- the distance -/
  d : Fin n → Fin n → ℝ
  /-- the uniform opening cost -/
  f : ℝ
  /-- the constant `γ_DC` -/
  γDC : ℝ
  /-- the constant `γ_IC` -/
  γIC : ℝ
  /-- the constant `r_S` -/
  rS : ℝ

/-- The standing assumptions of §4: `d` is a metric, `f > 0` (p.19), and `γ_DC, γ_IC, r_S > 1`
(p.21: "we have three constants γDC, γIC, rS > 1"). -/
def Alg3Params.Valid {n : ℕ} (P : Alg3Params n) : Prop :=
  IsMetric P.d ∧ 0 < P.f ∧ 1 < P.γDC ∧ 1 < P.γIC ∧ 1 < P.rS

/-- **A state of Algorithm 3** (the dual-fitting forward stage, p.24, PDF p.26).

* `θ` is the current time and `α` the dual vector;
* `A` is the set of active clients;
* `hist` lists the opened clusters in opening order, each as the pair `(S, D_A(S))` where
  `D_A(S) = S ∩ A` is recorded at the moment `S` is opened (p.20);
* `CI j = some t` records `C_I(j) = S_t`, the `t`-th opened cluster (Algorithm 3, step 2).

**Formalization Note.** The dependency forest `(V, E)` of p.20 is not stored: it is a function of
`hist` (`forestParent`), since each opening updates it deterministically. -/
structure Alg3State (n : ℕ) where
  /-- the current time -/
  θ : ℝ
  /-- the dual variables -/
  α : Fin n → ℝ
  /-- the active clients -/
  A : Finset (Fin n)
  /-- the opened clusters with their sets `D_A(S)`, in opening order -/
  hist : List (Finset (Fin n) × Finset (Fin n))
  /-- the indirect connections `C_I` -/
  CI : Fin n → Option ℕ

/-- Nodes of the dependency forest: `inl i` is the node `υ_i` of client `i`, `inr t` the node of
the `t`-th opened cluster (p.20). -/
abbrev Node (n : ℕ) : Type := Fin n ⊕ ℕ

/-- The `t`-th entry `(S_t, D_A(S_t))` of the opening history. -/
def histGet {n : ℕ} (h : List (Finset (Fin n) × Finset (Fin n))) (t : ℕ) :
    Finset (Fin n) × Finset (Fin n) :=
  h.getD t (∅, ∅)

/-- The nodes of `V` after the openings `h` (p.20): a client node `υ_i` while `i` lies in no
`D_A(S)`, and one node per opened cluster. -/
def NodeAlive {n : ℕ} (h : List (Finset (Fin n) × Finset (Fin n))) : Node n → Prop
  | .inl i => ∀ p ∈ h, i ∉ p.2
  | .inr t => t < h.length

/-- **Involved clients** `D_V(υ)` (p.20): `{i}` for a client node, `D_A(S)` for the node of `S`. -/
def nodeDV {n : ℕ} (h : List (Finset (Fin n) × Finset (Fin n))) : Node n → Finset (Fin n)
  | .inl i => {i}
  | .inr t => (histGet h t).2

/-- **Original cluster** `S_V(υ)` (p.20): `⊥` (`none`) for a client node, `S` for the node of `S`. -/
def nodeSV {n : ℕ} (h : List (Finset (Fin n) × Finset (Fin n))) : Node n → Option (Finset (Fin n))
  | .inl _ => none
  | .inr t => if t < h.length then some (histGet h t).1 else none

/-- `a` is equal to `b` or an ancestor of `b` for the parent map `p` (some number of parent steps
leads from `b` to `a`). -/
def AncOrSelf {n : ℕ} (p : Node n → Option (Node n)) (a b : Node n) : Prop :=
  ∃ m : ℕ, (fun o : Option (Node n) => o.bind p)^[m] (some b) = some a

/-- **Forest update when `S` is opened** (Algorithm 3, step 1, p.24): the new node `υ` of `S` is
`inr |h|`; every other node `υ′` of `V` (the client nodes of `D_A(S)` are removed from `V`) that is
still a root and whose tree contains a node `υ″` with `D_V(υ″) ∩ S ≠ ∅` gets the parent `υ`. -/
noncomputable def openUpdate {n : ℕ} (h : List (Finset (Fin n) × Finset (Fin n)))
    (p : Node n → Option (Node n)) (S DA : Finset (Fin n)) : Node n → Option (Node n) :=
  open Classical in
  fun v =>
    if NodeAlive h v ∧ (∀ i, v = Sum.inl i → i ∉ DA) ∧ p v = none ∧
        ∃ u, NodeAlive h u ∧ AncOrSelf p v u ∧ (nodeDV h u ∩ S).Nonempty then
      some (Sum.inr h.length)
    else p v

/-- **The cluster-based dependency forest** `(V, E)` (pp.20, 24) after the openings `h`, as a
parent map: replay the forest updates of the openings in order, starting from the forest of client
nodes with no edges. -/
noncomputable def forestParent {n : ℕ} (h : List (Finset (Fin n) × Finset (Fin n))) :
    Node n → Option (Node n) :=
  (List.range h.length).foldl
    (fun p t => openUpdate (h.take t) p (histGet h t).1 (histGet h t).2) (fun _ => none)

/-- Client `i` is involved in node `υ` of the current forest: `υ ∈ V` and `i ∈ D_V(υ)`. -/
def Involves {n : ℕ} (σ : Alg3State n) (v : Node n) (i : Fin n) : Prop :=
  NodeAlive σ.hist v ∧ i ∈ nodeDV σ.hist v

/-- **Definition 9 (the preorder `P(V, E)`)**, p.21: `i ⪯ j` iff the node involving `i` is equal
to or a descendant of the node involving `j`. -/
def Prec {n : ℕ} (σ : Alg3State n) (i j : Fin n) : Prop :=
  ∃ v w, Involves σ v i ∧ Involves σ w j ∧ AncOrSelf (forestParent σ.hist) w v

/-- **Definition 8 (available sets)**, p.20: `S` is available if `i ⪯ j` and `i ∈ S` imply
`j ∈ S`. -/
def Available {n : ℕ} (σ : Alg3State n) (S : Finset (Fin n)) : Prop :=
  ∀ i j, Prec σ i j → i ∈ S → j ∈ S

/-- `r` is a root of the current forest: `r ∈ V` with no parent. -/
def IsRoot {n : ℕ} (σ : Alg3State n) (r : Node n) : Prop :=
  NodeAlive σ.hist r ∧ forestParent σ.hist r = none

/-- **Definition 11 (current root)**, p.21: `r = root(i)`, the root of the tree containing the node
involving `i`. -/
def IsRootOf {n : ℕ} (σ : Alg3State n) (r : Node n) (i : Fin n) : Prop :=
  IsRoot σ r ∧ ∃ v, Involves σ v i ∧ AncOrSelf (forestParent σ.hist) r v

end MinSumClust


