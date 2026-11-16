-- Prove2me | Definitions.Def_ShiAuthentication_BA_Supplement_Complexity
-- name    : ShiAuthentication_BA_Supplement_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:21:51.007403+00:00
-- url     : https://prove2.me/theorems/339a0fcc-df62-4aee-badb-2d94557ec6b4
-- title:
--   Edge counts, cut conditions, the authentication complexities $A_{BA}$, $A^{\max}_{BA}$, $A_{BB}$, and the setups of Lemma 5.2 and Theorem 5.10
-- statement:
--   Let $G=(P,E)$ be an authentication graph on the $n$ parties $P$ (a loopless digraph; $x\to y$ means that $y$ is a verifier of $x$), with verifier sets $V_x=\{y:x\to y\}$ and key sets $K_v=\{x: x\to v\}$. This definition file introduces the quantities used to measure the cost of a cryptographic setup.
--
--   1. The **edge count** $|E(G)|=\sum_{v\in P}|K_v|$ and the **maximum indegree** $\max_{v}|K_v|$.
--   2. The **closed verifier set** $\widehat V_z=\{z\}\cup V_z$.
--   3. For a designated sender $S$ and the receivers $R=P\setminus\{S\}$, the **receiver edges** $E_R=E(G)\cap(R\times R)$.
--   4. Two parties $a\neq b$ are **nonadjacent** if neither $a\to b$ nor $b\to a$.
--   5. For sizes $a,b$, $G$ satisfies the **cut condition** if for all disjoint $X,Y\subseteq P$ with $|X|=a$ and $|Y|=b$ there are $x\in X$, $y\in Y$ with $x\to y$.
--   6. The **authentication complexities** (Definition 3.3):
--   $$A_{BA}(n,t)=\min_{G}\ |E(G)|,\qquad A^{\max}_{BA}(n,t)=\min_G\ \max_{v}|K_v|,\qquad A_{BB}(n,t)=\min_G\ |E(G)|,$$
--   where the first two minima range over the graphs $G$ on $n$ parties on which some deterministic protocol solves Byzantine agreement with fault bound $t$ (in a chosen knowledge setting: public graph or local key tables), the third over the graphs on which some deterministic protocol solves broadcast from the designated sender $S$ with fault bound $t$ ($\mathrm{BB}(G,S,t)$, public graph). Each minimum is $+\infty$ when no such graph exists.
--   7. The **registered-party graph** of Lemma 5.2: for a set $K_{\mathrm{reg}}$ of parties and an injective listing $e$ of further parties $U_{\mathrm{res}}$ carrying a graph $G_{\mathrm{res}}$, the graph whose edges are those of $G_{\mathrm{res}}$ transported along $e$ together with $x\to y$ for every $x\in K_{\mathrm{reg}}$ and every $y\neq x$.
--   8. The **forward graph** of Theorem 5.10: for an ordering $v_0,v_1,\dots,v_{n-1}$ of $P$, all edges $v_i\to v_j$ with $i<j$ except $v_{n-2}\to v_{n-1}$.
--
--   These objects turn the operational feasibility notions of the base mission into the counting problems studied in §§4.3 and 5 of the paper.
--
--   **Formalization Note** The complexities take values in `ℕ∞` and are infima over the published predicates `BAPossible` and `BBPossible`; the infimum of the empty family is `⊤`, which is the paper's $+\infty$. An ordering of $P$ is an equivalence `v : Fin n ≃ Fin n` with `v i` the $i$-th party.
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), §3.1 p. 16 (degrees, V̂_x), Definition 3.3 p. 16, §4.3 p. 22 (cut conditions), Lemma 5.2 p. 25, §5.2 p. 26 (E_R), §5.3 p. 33 (nonadjacent), Theorem 5.10 and Figure 2, p. 34

import Definitions.Def_ShiAuthentication_BA_Execution

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

open ShiAuthentication.BA

/-! # Edge counts, cut conditions and authentication complexity

Kecheng Shi, *The Authentication Complexity of Byzantine Consensus*, STOC 2027 submission #203:
§3.1 (p. 16: degrees, `V̂_x`), Definition 3.3 (p. 16: `A_T(n,t)`, `A^max_T(n,t)`), §4.3 (p. 22:
cut conditions), Lemma 5.2 (p. 25: registered parties), §5.2 (p. 26: receiver edges),
§5.3 (p. 33: nonadjacent receivers), Theorem 5.10 (p. 34: the optimal maximum-resilience setup).
All objects are built on the published `AuthGraph` and on the published feasibility predicates
`BAPossible` and `BBPossible`. -/

variable {n : ℕ}

/-- `E(G)`, the set of directed authentication edges `x → y` (p. 2, p. 16). -/
def edges (G : AuthGraph n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => G.adj p.1 p.2 = true)

/-- `|E(G)| = Σ_v |K_v| = Σ_x |V_x|`, the number of initial authentication bindings. -/
def edgeCount (G : AuthGraph n) : ℕ := (edges G).card

/-- `max_v |K_v|`, the maximum indegree (maximum number of initially authenticated keys held by
one party). -/
def maxIndegree (G : AuthGraph n) : ℕ := Finset.univ.sup (fun v => (G.signersOf v).card)

/-- `V̂_z = {z} ∪ V_z`, the verifier set of `z` together with `z` itself (p. 16). -/
def closedVerifiers (G : AuthGraph n) (z : Fin n) : Finset (Fin n) :=
  insert z (G.verifiers z)

/-- `E_R = E(G) ∩ (R × R)` for the receivers `R = P \ {S}` (p. 26). -/
def receiverEdges (G : AuthGraph n) (S : Fin n) : Finset (Fin n × Fin n) :=
  (edges G).filter (fun p => p.1 ≠ S ∧ p.2 ≠ S)

/-- `|E_R|`. -/
def receiverEdgeCount (G : AuthGraph n) (S : Fin n) : ℕ := (receiverEdges G S).card

/-- Two parties are **nonadjacent** if they are distinct and neither `a → b` nor `b → a`
(p. 33). -/
def Nonadjacent (G : AuthGraph n) (a b : Fin n) : Prop :=
  a ≠ b ∧ G.adj a b = false ∧ G.adj b a = false

/-- **Cut condition** (§4.3, p. 22): `G` has an edge from every `a`-set to every disjoint `b`-set,
i.e. for all disjoint `X, Y ⊆ P` with `|X| = a`, `|Y| = b` some `x ∈ X`, `y ∈ Y` have `x → y`. -/
def CutCondition (G : AuthGraph n) (a b : ℕ) : Prop :=
  ∀ X Y : Finset (Fin n), Disjoint X Y → X.card = a → Y.card = b →
    ∃ x ∈ X, ∃ y ∈ Y, G.adj x y = true

/-- **Definition 3.3** (p. 16) for Byzantine agreement: `A_BA(n, t)`, the minimum of `|E(G)|` over
authentication graphs `G` on `n` parties on which Byzantine agreement with fault bound `t` is
possible in the knowledge setting `mode`; `+∞ = ⊤` if there is none (the infimum of the empty
family in `ℕ∞`). -/
noncomputable def ABA (mode : Knowledge) (n t : ℕ) : ℕ∞ :=
  ⨅ (G : AuthGraph n) (_ : BAPossible mode t G), (edgeCount G : ℕ∞)

/-- **Definition 3.3** (p. 16): `A^max_BA(n, t)`, the minimum over the same graphs of
`max_v |K_v|`; `+∞ = ⊤` if there is none. -/
noncomputable def ABAmax (mode : Knowledge) (n t : ℕ) : ℕ∞ :=
  ⨅ (G : AuthGraph n) (_ : BAPossible mode t G), (maxIndegree G : ℕ∞)

/-- **Definition 3.3** (p. 16) for broadcast from the designated sender `S`: `A_BB(n, t)`, the
minimum of `|E(G)|` over authentication graphs `G` on the `n` parties with `BB(G, S, t)`
(Definition 3.1, public authentication graph, §3.1); `+∞ = ⊤` if there is none. -/
noncomputable def ABB (t : ℕ) (S : Fin n) : ℕ∞ :=
  ⨅ (G : AuthGraph n) (_ : BBPossible .publicGraph t G S), (edgeCount G : ℕ∞)

/-- The graph of **Lemma 5.2** (p. 25). `K` is the set `K_reg` of registered parties and
`e : Fin m ↪ P` lists the remaining parties `U_res` (in the lemma `m = n − s` and the range of
`e` is `P \ K_reg`). The graph `Gres` on `U_res` is transported along `e`, and every registered
party `x ∈ K` is authenticated to every other party: `x → y` for all `y ≠ x`. -/
def registeredGraph {m : ℕ} (K : Finset (Fin n)) (e : Fin m ↪ Fin n) (Gres : AuthGraph m) :
    AuthGraph n where
  adj x y := decide ((x ∈ K ∧ x ≠ y) ∨ ∃ i j : Fin m, e i = x ∧ e j = y ∧ Gres.adj i j = true)
  loopless x := by
    simp only [ne_eq, not_true_eq_false, and_false, false_or, decide_eq_false_iff_not, not_exists,
      not_and]
    intro i j hi hj
    have hij : i = j := e.injective (hi.trans hj.symm)
    subst hij
    simp [Gres.loopless i]

/-- The optimal setup of **Theorem 5.10** (p. 34, Figure 2). The equivalence `v` lists the parties
in the order `v 0, v 1, …, v (n−1)` (`v.symm x` is the position of `x`); the edges are all forward
edges `v_i → v_j` with `i < j`, except `v_{n−2} → v_{n−1}`. -/
def forwardGraph (v : Fin n ≃ Fin n) : AuthGraph n where
  adj x y := decide (v.symm x < v.symm y ∧ ¬ ((v.symm x).val + 2 = n ∧ (v.symm y).val + 1 = n))
  loopless x := by simp

end ShiAuthentication.BA.Supplement


