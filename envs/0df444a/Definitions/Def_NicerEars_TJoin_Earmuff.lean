-- Prove2me | Definitions.Def_NicerEars_TJoin_Earmuff
-- name    : NicerEars_TJoin_Earmuff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:50.930078+00:00
-- url     : https://prove2.me/theorems/0faaa384-9a03-4697-a2f4-f5ba4326a432
-- title:
--   Definitions 9, 12, p. 15 — eardrums, earmuffs, µ(G,M), U_f, surplus, L_µ, L_ϕ, containing a maximum earmuff
-- statement:
--   (Sebő–Vygen, Definition 9, p. 8.) An **eardrum** in $G$ is the set $M$ of components of an induced subgraph in which every vertex has degree at most 1: the members of $M$ are pairwise disjoint sets of one or two vertices, the two vertices of a two-element member are adjacent, and vertices of different members are non-adjacent. Write $V_M:=\bigcup M$.
--
--   (Definition 12, p. 11.) For $f\in M$ let $\mathcal P_f$ be the set of paths $P$ in $G$ with $\mathrm{in}(P)=f$. An **earmuff** for $M$ is a family of paths $\{P_f: f\in F\}$ with $F\subseteq M$ and $P_f\in\mathcal P_f$ such that $(V(G),\bigcup_{f\in F}E(P_f))$ is a forest; its size is $|F|$, and $\mu(G,M)$ is the maximum size of an earmuff.
--
--   (p. 15.) $U_f$ is the set of endpoints of paths in $\mathcal P_f$, and for $W\subseteq V(G)\setminus V_M$ the **surplus** of $W$ is
--   $$\mathrm{sur}(W):=|\{f\in M: U_f\subseteq W\}|-(|W|-1).$$
--
--   (Theorems 19, 20, p. 16.)
--   $$L_\mu(G,M):=|V(G)|-1+|M|-\mu(G,M),\qquad L_\varphi(G):=|V(G)|+\varphi(G)-1.$$
--
--   (Lemma 23, Theorem 24, p. 18.) An ear-decomposition **contains a maximum earmuff** for the eardrum $M$ associated with it and $T$ if, for some $F\subseteq M$ with $|F|=\mu(G,M)$, the clean ears with internal vertex sets in $F$ form an earmuff.
--
--   $L_\mu$ is the lower bound of Theorem 20 and $L_\varphi$ enters the upper bound of Theorem 24.
--
--   **Formalization Note.** Degree at most 1 in the induced subgraph is read as adjacency in the underlying simple graph, so a parallel copy of a middle edge does not disqualify a 3-ear. A forest is an edge set every edge of which is a bridge of it, so two parallel edges form a circuit. $\mu$ is a supremum in $\mathbb N$ over a set that contains $0$ (the empty earmuff) and is bounded by $|M|$, so it is a maximum. Surplus, $L_\mu$ and $L_\varphi$ are integers (no truncated subtraction).
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 8 (Definition 9), p. 11 (Definition 12), p. 15 (U_f, sur(W)), p. 16 (Theorems 19, 20), p. 18 (Lemma 23, Theorem 24)

import Mathlib
import Definitions.Def_NicerEars_TJoin_Ears

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Definition 9 (p. 8): `M` is an eardrum in `G`: the set of components of an induced subgraph in
which every vertex has degree at most 1. Equivalently: the members of `M` are pairwise disjoint sets
of one or two vertices, the two vertices of a two-element member are adjacent, and vertices of
different members are non-adjacent. Degree is read in the underlying simple graph (adjacency). -/
def IsEardrum (G : Graph V E) (M : Finset (Finset V)) : Prop :=
  (∀ f ∈ M, #f = 1 ∨ (#f = 2 ∧ ∀ u ∈ f, ∀ w ∈ f, u ≠ w → (G.spanGraph univ).Adj u w)) ∧
  (∀ f ∈ M, ∀ g ∈ M, f ≠ g →
    Disjoint f g ∧ ∀ u ∈ f, ∀ w ∈ g, ¬ (G.spanGraph univ).Adj u w)

/-- `V_M := ⋃ M` (p. 8). -/
def VM (M : Finset (Finset V)) : Finset V := M.biUnion id

/-- Definition 12 (p. 11): `𝒫_f`, the set of paths `P` in `G` with `in(P) = f`. -/
def PathsThrough (G : Graph V E) (f : Finset V) : Set (Ear G) :=
  {P | P.IsOpen ∧ P.inner = f}

open Classical in
/-- `U_f` (p. 15): the set of endpoints of paths in `𝒫_f`. -/
noncomputable def endSet (G : Graph V E) (f : Finset V) : Finset V :=
  univ.filter (fun u => ∃ P ∈ PathsThrough G f, P.first = u ∨ P.last = u)

/-- The edge set `S` forms a forest in `G`: every edge of `S` is a bridge of `(V(G), S)`, i.e. its two
ends are not connected in `(V(G), S ∖ {e})`. Parallel edges in `S` form a circuit. -/
def IsForest (G : Graph V E) (S : Finset E) : Prop :=
  ∀ e ∈ S, ∀ u w, G.ends e = s(u, w) → ¬ (G.spanGraph (S.erase e)).Reachable u w

/-- Definition 12 (p. 11): an earmuff for `M` in `G`: a family of paths `{P_f : f ∈ F}` with
`F ⊆ M` and `P_f ∈ 𝒫_f`, such that `(V(G), ⋃_{f ∈ F} E(P_f))` is a forest. -/
def IsEarmuff (G : Graph V E) (M F : Finset (Finset V)) (P : ∀ f ∈ F, Ear G) : Prop :=
  F ⊆ M ∧ (∀ f (hf : f ∈ F), P f hf ∈ PathsThrough G f) ∧
    IsForest G (F.attach.biUnion (fun f => (P f.1 f.2).edges))

/-- Definition 12 (p. 11): µ(G, M), the maximum size `|F|` of an earmuff for `M` in `G`. The set is
nonempty (the empty earmuff) and bounded by `|M|`, so this is a maximum. -/
noncomputable def mu (G : Graph V E) (M : Finset (Finset V)) : ℕ :=
  sSup {n | ∃ F : Finset (Finset V), ∃ P : ∀ f ∈ F, Ear G, IsEarmuff G M F P ∧ #F = n}

open Classical in
/-- p. 15: the surplus of `W ⊆ V(G) ∖ V_M`: `sur(W) := |{f ∈ M : U_f ⊆ W}| − (|W| − 1)`, in `ℤ`. -/
noncomputable def surplus (G : Graph V E) (M : Finset (Finset V)) (W : Finset V) : ℤ :=
  (#(M.filter (fun f => endSet G f ⊆ W)) : ℤ) - ((#W : ℤ) - 1)

/-- Theorem 20 (p. 16): `L_µ(G, M) := |V(G)| − 1 + |M| − µ(G, M)`, in `ℤ`. -/
noncomputable def Lmu (G : Graph V E) (M : Finset (Finset V)) : ℤ :=
  (Fintype.card V : ℤ) - 1 + #M - mu G M

/-- Theorem 19 (p. 16): `L_ϕ(G) := |V(G)| + ϕ(G) − 1`, in `ℤ`. -/
noncomputable def Lphi (G : Graph V E) : ℤ :=
  (Fintype.card V : ℤ) + phi G - 1

/-- Lemma 23, Theorem 24 (p. 18): the ear-decomposition `D` contains a maximum earmuff for the
eardrum `M` associated with it and `T`: for some `F ⊆ M` with `|F| = µ(G, M)`, the clean ears whose
internal vertex sets lie in `F` form an earmuff for `M`. -/
def EarDecomposition.ContainsMaxEarmuff {G : Graph V E} (D : EarDecomposition G) (T : Finset V) :
    Prop :=
  ∃ F ⊆ D.eardrumOf T, #F = mu G (D.eardrumOf T) ∧
    ∃ P : ∀ f ∈ F, Ear G, (∀ f (hf : f ∈ F), ∃ i, D.IsClean T i ∧ D.ear i = P f hf) ∧
      IsEarmuff G (D.eardrumOf T) F P

end NicerEars.TJoin


