-- Prove2me | Definitions.Def_KColoringFaster_ListBootstrap_TwoBlock
-- name    : KColoringFaster_ListBootstrap_TwoBlock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:58.24372+00:00
-- url     : https://prove2.me/theorems/624f866d-7a49-4540-b24b-f3babe9d0250
-- title:
--   Theorem 3.7, Corollary 3.8 — two-block restricted coloring instances
-- statement:
--   The inputs of Theorem 3.7 and Corollary 3.8 (p. 11).
--
--   A **two-block instance** consists of a graph $G$ on $\{0,\dots,n-1\}$, a finite palette $P\subseteq\mathbb N$ split as $P=Q\,\dot\cup\,R$ (with $R=P\setminus Q$), and an allowed domain $V_c\subseteq V(G)$ for each color $c\in P$. It is a yes-instance if $G$ has a proper coloring $\varphi:V(G)\to P$ with $\varphi(v)=c\Rightarrow v\in V_c$. Put
--   $$D_Q=\bigcup_{c\in Q}V_c,\qquad D_R=\bigcup_{c\in R}V_c.$$
--   It is encoded as $n$, the adjacency bits, $|P|$, and then for each $c\in P$ in increasing order the color $c$, a flag ($1$ if $c\in Q$, $0$ if $c\in R$) and the set $V_c$.
--
--   The input of Corollary 3.8 is a list instance $(G,L)$ together with a set $Q$ of colors; $R$ is the set of colors outside $Q$. Put
--   $$A_Q=\{v: L(v)\subseteq Q\},\qquad B_R=\{v: L(v)\subseteq R\}=\{v: L(v)\cap Q=\emptyset\}.$$
--   These are the largest sets $A,B$ with the property assumed in Corollary 3.8. The input is encoded as the list instance followed by $|Q|$ and the elements of $Q$ in increasing order.
--
--   **Formalization Note** Only the domains of colors in $P$ enter the yes-condition and the encoding.
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 11, Theorem 3.7 and Corollary 3.8

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances

open Classical

namespace KColoringFaster.ListBootstrap

/-! # Two-block restricted coloring (Theorem 3.7, p. 11) and two-block list instances
(Corollary 3.8, p. 11)

**Formalization Note.**
* A two-block instance is a graph on `Fin n`, a finite palette `P ⊆ ℕ`, a block `Q ⊆ P` (the other
  block is `R = P \ Q`, so `P = Q ∪̇ R`), and an allowed domain `V c ⊆ V(G)` for every color. Only the
  domains of colors in `P` matter; the encoding lists them for `c ∈ P` only.
* For Corollary 3.8 the input is a list instance together with the block `Q`; `R` is the complement
  of `Q` among the colors. `supportedQ` is the largest admissible `A` (`L v ⊆ Q`) and `supportedR` the
  largest admissible `B` (`L v ⊆ R`, i.e. `L v ∩ Q = ∅`). -/

/-- An instance of two-block restricted coloring. -/
structure TwoBlockInstance where
  n : ℕ
  G : SimpleGraph (Fin n)
  P : Finset ℕ
  Q : Finset ℕ
  hQP : Q ⊆ P
  V : ℕ → Finset (Fin n)

/-- The yes-instances: a proper coloring `φ : V(G) → P` in which every color `c` is used only on
`V c`. -/
def TwoBlockInstance.Yes (I : TwoBlockInstance) : Prop :=
  ∃ φ : Fin I.n → ℕ, (∀ v, φ v ∈ I.P ∧ v ∈ I.V (φ v)) ∧ ∀ u v, I.G.Adj u v → φ u ≠ φ v

/-- `D_Q = ⋃_{c ∈ Q} V c`. -/
def TwoBlockInstance.DQ (I : TwoBlockInstance) : Finset (Fin I.n) := I.Q.biUnion I.V

/-- `D_R = ⋃_{c ∈ R} V c` with `R = P \ Q`. -/
def TwoBlockInstance.DR (I : TwoBlockInstance) : Finset (Fin I.n) := (I.P \ I.Q).biUnion I.V

/-- A set of vertices: its size, then its elements in increasing order. -/
def encVertexSet {n : ℕ} (s : Finset (Fin n)) : List ℤ :=
  (s.card : ℤ) :: (s.sort (· ≤ ·)).map fun v => ((v : ℕ) : ℤ)

/-- Canonical encoding: `n`, the adjacency bits, `|P|`, then for each `c ∈ P` in increasing order
the color `c`, the flag `1` if `c ∈ Q` and `0` if `c ∈ R`, and the domain `V c`. -/
noncomputable def encTwoBlock (I : TwoBlockInstance) : List ℤ :=
  ((I.n : ℤ) :: adjBits I.G) ++ ((I.P.card : ℤ) ::
    (I.P.sort (· ≤ ·)).flatMap fun (c : ℕ) =>
      [(c : ℤ), if c ∈ I.Q then 1 else 0] ++ encVertexSet (I.V c))

/-- The input of Corollary 3.8: a list instance and the block `Q` of the palette. -/
structure ListQInstance where
  I : ListInstance
  Q : Finset ℕ

/-- Canonical encoding: the list instance, then `Q` (`encFinset`). -/
noncomputable def encListQ (J : ListQInstance) : List ℤ := encList J.I ++ encFinset J.Q

/-- `A_Q = {v : L(v) ⊆ Q}`, the largest set `A` admissible in Corollary 3.8. -/
noncomputable def ListQInstance.supportedQ (J : ListQInstance) : Finset (Fin J.I.n) :=
  Finset.univ.filter fun v => J.I.L v ⊆ J.Q

/-- `B_R = {v : L(v) ⊆ R}` with `R` the colors outside `Q`, the largest admissible `B`. -/
noncomputable def ListQInstance.supportedR (J : ListQInstance) : Finset (Fin J.I.n) :=
  Finset.univ.filter fun v => Disjoint (J.I.L v) J.Q

end KColoringFaster.ListBootstrap


