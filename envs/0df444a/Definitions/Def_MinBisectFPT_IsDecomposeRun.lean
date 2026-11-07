-- Prove2me | Definitions.Def_MinBisectFPT_IsDecomposeRun
-- name    : MinBisectFPT_IsDecomposeRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:22.758193+00:00
-- url     : https://prove2.me/theorems/edcbed70-ff93-4595-b1c9-e0d393127d83
-- title:
--   Algorithm 2 (Decompose): excess, sets under consideration, loop step, finished runs
-- statement:
--   Fix a graph $G$ and $k$. A call $\mathrm{Decompose}(D)$ receives a nonempty $D$ with $G[D]$ connected and $|N(D)|\le 2k$, and works in $H_D=G[D\cup N(D)]-E(G[N(D)])$. Line 2 returns the single bag $V(H)$ if $|V(H)|\le 2k+1$. Otherwise Line 3 fixes $Z=N(D)\cup D_0$ with $D_0\subseteq D$ and $|Z|=2k+1$, and sets $\beta=V(H)$.
--
--   The **excess** of $R$ is the integer $\mathrm{ex}(R)=|(R\cap\beta)\setminus Z|-|\delta(R)|-|R\cap Z|$. The sets **under consideration** are $R_H(F)$ for every important $(A_0,Z\setminus A_0)$-cut $F$ of size at most $k$, for every nonempty $A_0\subseteq Z$ with $|A_0|\le k$, and for every important $(\{v\},Z)$-cut $F$ of size at most $k$, for every $v\in\beta\setminus Z$.
--
--   One **loop step** picks such an $R$ with $\mathrm{ex}(R)\ge 1$, any $|\delta(R)|+|R\cap Z|+1$ vertices $Z_1$ of $(R\cap\beta)\setminus Z$, a separation $(A,B)$ of $H$ minimizing $|A\cap B|$ subject to $Z_1\subseteq A$ and $Z\subseteq B$, and sets $\beta\leftarrow(\beta\cap B)\cup(A\cap B)$. The loop ends only when no set under consideration has positive excess. Line 8 makes one child call per component of $H-\beta$.
--
--   A **finished run** records the call tree: a rooted tree whose nodes carry the set of their call and its bag.
--
--   **Formalization Note** All free choices stay free, so a statement over all runs covers each of them. The node numbering is arbitrary. The definition does not say that the tree is a tree decomposition; Lemma 5.6 proves that.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Algorithm 2 and §5.1, pp.16–18; §3, p.9

import Mathlib
import Definitions.Def_MinBisectFPT_RootedTD
import Definitions.Def_MinBisectFPT_IsImportant

open scoped Classical

namespace MinBisectFPT

variable {n : ℕ}

/-- `V(H_D) = D ∪ N(D)`. Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*, STOC
2027 submission (manuscript sha256 8db80a52…), §5, p.16. -/
noncomputable def callVerts (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) : Finset (Fin n) :=
  D ∪ nbr G D

/-- `H_D = G[D ∪ N(D)] − E(G[N(D)])` (p.16), on the ambient vertex type. -/
noncomputable def callGraph (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) : SimpleGraph (Fin n) :=
  restrictMinus G (callVerts G D) (nbr G D)

/-- The input condition of `Decompose(D)` (p.16): "a nonempty set D ⊆ V(G) such that G[D] is connected
and |N(D)| ≤ 2k". -/
def IsLegalCall (G : SimpleGraph (Fin n)) (k : ℕ) (D : Finset (Fin n)) : Prop :=
  D.Nonempty ∧ (G.induce (D : Set (Fin n))).Connected ∧ (nbr G D).card ≤ 2 * k

/-- **The state after Lines 1–3 of Algorithm 2**, past the test of Line 2 (p.17): the call is legal,
`|V(H)| > 2k + 1`, and `Z ← N(D) ∪ D0` for an arbitrary `D0 ⊆ D` with `|N(D) ∪ D0| = 2k + 1`. -/
def IsCallSetup (G : SimpleGraph (Fin n)) (k : ℕ) (D Z : Finset (Fin n)) : Prop :=
  IsLegalCall G k D ∧ 2 * k + 1 < (callVerts G D).card ∧
    ∃ D0, D0 ⊆ D ∧ Z = nbr G D ∪ D0 ∧ Z.card = 2 * k + 1

/-- **The excess** `ex(R) = |(R ∩ β) \ Z| − |δ(R)| − |R ∩ Z|` (§5.1, p.17), an integer (it can be
negative). -/
noncomputable def excess (H : SimpleGraph (Fin n)) (Z β R : Finset (Fin n)) : ℤ :=
  (((R ∩ β) \ Z).card : ℤ) - (cutSize H R : ℤ) - ((R ∩ Z).card : ℤ)

/-- **The reachable sets under consideration** (§5.1, p.17): `R_H(F)` for "every important
(A0, Z \ A0)-cut F in H of size at most k, for every nonempty A0 ⊆ Z with |A0| ≤ k, and every important
({v}, Z)-cut F in H of size at most k, for every v ∈ β \ Z." -/
def IsConsidered (H : SimpleGraph (Fin n)) (Z β : Finset (Fin n)) (k : ℕ) (R : Finset (Fin n)) :
    Prop :=
  (∃ A0 F, A0 ⊆ Z ∧ A0.Nonempty ∧ A0.card ≤ k ∧ IsImportant H A0 (Z \ A0) F ∧ F.card ≤ k ∧
      R = reach H A0 F) ∨
    ∃ v F, v ∈ β \ Z ∧ IsImportant H {v} Z F ∧ F.card ≤ k ∧ R = reach H {v} F

/-- A separation (§3, p.9): "a pair (A, B) with A ∪ B = V(H) and no edge between A \ B and B \ A". -/
def IsSeparation (H : SimpleGraph (Fin n)) (VH A B : Finset (Fin n)) : Prop :=
  A ∪ B = VH ∧ ∀ u v, H.Adj u v → ¬(u ∈ A \ B ∧ v ∈ B \ A)

/-- Line 6 (p.17): `(A, B)` is "a separation of H minimizing |A ∩ B| subject to Z1 ⊆ A and Z ⊆ B". -/
def IsMinSeparation (H : SimpleGraph (Fin n)) (VH Z1 Z A B : Finset (Fin n)) : Prop :=
  IsSeparation H VH A B ∧ Z1 ⊆ A ∧ Z ⊆ B ∧
    ∀ A' B', IsSeparation H VH A' B' → Z1 ⊆ A' → Z ⊆ B' → (A ∩ B).card ≤ (A' ∩ B').card

/-- Line 5 (p.17): `Z1` is "any |δ(R)| + |R ∩ Z| + 1 vertices of (R ∩ β) \ Z". -/
def IsLine5 (H : SimpleGraph (Fin n)) (Z β R Z1 : Finset (Fin n)) : Prop :=
  Z1 ⊆ (R ∩ β) \ Z ∧ Z1.card = cutSize H R + (R ∩ Z).card + 1

/-- **One iteration of the loop of Algorithm 2** (Lines 4–7, p.17): some `R` under consideration has
`ex(R) ≥ 1`, and `β′ = (β ∩ B) ∪ (A ∩ B)` for any `Z1` and any `(A, B)` the lines allow. -/
def LoopStep (H : SimpleGraph (Fin n)) (VH Z : Finset (Fin n)) (k : ℕ) (β β' : Finset (Fin n)) :
    Prop :=
  ∃ R Z1 A B, IsConsidered H Z β k R ∧ 1 ≤ excess H Z β R ∧ IsLine5 H Z β R Z1 ∧
    IsMinSeparation H VH Z1 Z A B ∧ β' = (β ∩ B) ∪ (A ∩ B)

/-- The loop of Line 4 has ended: no set `R` under consideration has `ex(R) ≥ 1`. -/
def LoopEnded (H : SimpleGraph (Fin n)) (Z β : Finset (Fin n)) (k : ℕ) : Prop :=
  ∀ R, IsConsidered H Z β k R → excess H Z β R < 1

/-- Invariant (I2) (p.18): "Every component C of H − β satisfies |N_H(C)| ≤ 2k." -/
def InvI2 (H : SimpleGraph (Fin n)) (VH β : Finset (Fin n)) (k : ℕ) : Prop :=
  ∀ C, IsComponent H (VH \ β) C → (nbr H C).card ≤ 2 * k

/-- **The bag a call of Algorithm 2 may create** (p.17): either Line 2 applies and the bag is `V(H)`,
or Line 3 picks some `Z`, the loop runs from `β = V(H)` through any choices, and it stops only when no
set under consideration has positive excess. -/
def IsCallBag (G : SimpleGraph (Fin n)) (k : ℕ) (D β : Finset (Fin n)) : Prop :=
  ((callVerts G D).card ≤ 2 * k + 1 ∧ β = callVerts G D) ∨
    ∃ Z, IsCallSetup G k D Z ∧
      Relation.ReflTransGen (LoopStep (callGraph G D) (callVerts G D) Z k) (callVerts G D) β ∧
        LoopEnded (callGraph G D) Z β k

/-- **A finished run of `Decompose(D₀)`** (Algorithm 2, p.17): its call tree, one node per call. `T` is
the tree created and `call t` the set `D` of the call at node `t`. The root is the call on `D₀`. Every
call is legal, its bag is one that the call may create under some resolution of its free choices, and
(Line 8) its children are exactly one call per component of `H − β`.

**Formalization Note** Every free choice ("arbitrary", "any", "a separation minimizing") is left
free, so a statement about all runs covers all of them. The nodes are numbered arbitrarily. Nothing
here says that `T` is a tree decomposition; that is the content of Lemma 5.6. -/
def IsDecomposeRun (G : SimpleGraph (Fin n)) (k : ℕ) (D₀ : Finset (Fin n)) (T : RootedTD n)
    (call : Fin T.N → Finset (Fin n)) : Prop :=
  (∃ r, T.parent r = none ∧ call r = D₀ ∧ ∀ t, T.parent t = none → t = r) ∧
    ∀ t, IsLegalCall G k (call t) ∧ IsCallBag G k (call t) (T.bag t) ∧
      Set.InjOn call (T.children t : Set (Fin T.N)) ∧
      ∀ D', IsComponent (callGraph G (call t)) (callVerts G (call t) \ T.bag t) D' ↔
        ∃ c ∈ T.children t, call c = D'

end MinBisectFPT


