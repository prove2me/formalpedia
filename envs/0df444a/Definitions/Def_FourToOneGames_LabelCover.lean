-- Prove2me | Definitions.Def_FourToOneGames_LabelCover
-- name    : FourToOneGames_LabelCover
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T23:00:19.132359+00:00
-- url     : https://prove2.me/theorems/bc429335-aff0-4c47-a2f2-65535cb341f6
-- title:
--   Label cover, $d$-to-1 games, and polynomial-time gap reductions
-- statement:
--   The basic objects of the mission, following Definitions 1.1 and 1.3 of the source paper.
--
--   A **label-cover instance with projection constraints** is a five-tuple: a number $n_L$ of left vertices, a number $n_R$ of right vertices, alphabet sizes $|\Sigma_L|$ and $|\Sigma_R|$, a finite set of edges $E \subseteq [n_L] \times [n_R]$, and for every pair $(u,v)$ a projection map $\varphi_{u,v} : \Sigma_L \to \Sigma_R$. An edge $(u,v)$ is satisfied by a pair of assignments $(A_L, A_R)$ when $\varphi_{u,v}(A_L(u)) = A_R(v)$; the value $\mathrm{val}(\Psi)$ is the largest fraction of edges that can be satisfied simultaneously.
--
--   An instance is a **$d$-to-1 game** when for every edge $(u,v)$ and every $\sigma \in \Sigma_R$ there are exactly $d$ symbols $\tau \in \Sigma_L$ with $\varphi_{u,v}(\tau) = \sigma$. An instance obeys the alphabet bound $r$ when both alphabets have size at most $r$.
--
--   Finally, a **gap-preserving reduction** between two promise problems is a map on instances that (i) is computed by a Turing machine in polynomial time, with respect to fixed binary encodings of the two instance types, (ii) sends yes-instances to yes-instances and (iii) sends no-instances to no-instances. Its existence transfers NP-hardness from the source promise problem to the target one. The binary encoding of a label-cover instance writes the four size parameters in unary, then the adjacency bits of the bipartite graph, then the values of all projection maps.
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, pp. 4-5, Definitions 1.1 and 1.3

import Mathlib

/-!
# Label cover, `d`-to-1 games, and polynomial-time gap-preserving reductions

Basic objects for the mission "4-to-1 Games with Perfect Completeness", following
Fei–Minzer–Wang, *On the Hardness of 4-to-1 Games with Perfect Completeness*
(ECCC TR26-179), Definitions 1.1 and 1.3.

Hardness statements are phrased as the existence of a polynomial-time many-one reduction
between promise problems: `GapReduction` bundles a map on instances together with a Turing
machine computing it in polynomial time (Mathlib's `Turing.TM2ComputableInPolyTime`), and the
requirement that yes-instances go to yes-instances and no-instances to no-instances.
-/

namespace FourToOneGames

/-- A finite instance of the label-cover problem **with projection constraints**
(Definition 1.1).  The left vertices are `Fin nL`, the right vertices are `Fin nR`, the
alphabets are `Fin sizeL` and `Fin sizeR`, and the constraint attached to an edge `(u, v)`
is the projection constraint given by the map `proj u v : Fin sizeL → Fin sizeR`. -/
structure LabelCover where
  /-- Number of left vertices. -/
  nL : ℕ
  /-- Number of right vertices. -/
  nR : ℕ
  /-- Size of the left alphabet. -/
  sizeL : ℕ
  /-- Size of the right alphabet. -/
  sizeR : ℕ
  /-- The edge set of the underlying bipartite graph. -/
  edges : Finset (Fin nL × Fin nR)
  /-- The projection map attached to each (potential) edge. -/
  proj : Fin nL → Fin nR → Fin sizeL → Fin sizeR

namespace LabelCover

/-- The fraction of edges satisfied by the pair of assignments `(AL, AR)`. -/
noncomputable def valAssign (P : LabelCover) (AL : Fin P.nL → Fin P.sizeL)
    (AR : Fin P.nR → Fin P.sizeR) : ℝ :=
  ((P.edges.filter fun e => P.proj e.1 e.2 (AL e.1) = AR e.2).card : ℝ) / (P.edges.card : ℝ)

/-- The value `val(P)` of a label-cover instance: the largest fraction of constraints that can
be satisfied simultaneously. -/
noncomputable def val (P : LabelCover) : ℝ :=
  ⨆ A : (Fin P.nL → Fin P.sizeL) × (Fin P.nR → Fin P.sizeR), P.valAssign A.1 A.2

/-- `P` is a `d`-to-1 game (Definition 1.3): every edge constraint is `d`-to-1, i.e. every
right-alphabet symbol has exactly `d` preimages under the edge's projection map. -/
def IsDToOne (d : ℕ) (P : LabelCover) : Prop :=
  ∀ e ∈ P.edges, ∀ σ : Fin P.sizeR,
    (Finset.univ.filter fun τ : Fin P.sizeL => P.proj e.1 e.2 τ = σ).card = d

/-- Both alphabets of `P` have size at most `r`. -/
def AlphabetBound (r : ℕ) (P : LabelCover) : Prop := P.sizeL ≤ r ∧ P.sizeR ≤ r

end LabelCover

/-- Unary encoding of a natural number, terminated by `false`. -/
def unaryCode (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- A binary encoding of a label-cover instance: the four size parameters in unary, followed by
the adjacency bits of the bipartite graph in lexicographic order, followed by the values of the
projection maps (each in unary).  Its length is polynomial in the number of vertices, the
alphabet sizes and the number of edges. -/
def encodeLabelCover (P : LabelCover) : List Bool :=
  unaryCode P.nL ++ unaryCode P.nR ++ unaryCode P.sizeL ++ unaryCode P.sizeR ++
    ((List.finRange P.nL).flatMap fun u =>
      (List.finRange P.nR).map fun v => decide ((u, v) ∈ P.edges)) ++
    ((List.finRange P.nL).flatMap fun u =>
      (List.finRange P.nR).flatMap fun v =>
        (List.finRange P.sizeL).flatMap fun τ => unaryCode (P.proj u v τ : ℕ))

/-- A Karp-style **gap-preserving reduction** between two promise problems.

`ea` and `eb` are the binary encodings of source and target instances, `yesa`/`noa` are the yes-
and no-instances of the source promise problem and `yesb`/`nob` those of the target.  A term of
this type is a map on instances that is computable by a Turing machine in polynomial time, sends
source yes-instances to target yes-instances and source no-instances to target no-instances.

Consequently, if the source promise problem is NP-hard, so is the target one. -/
structure GapReduction {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (yesa noa : α → Prop) (yesb nob : β → Prop) where
  /-- The reduction map. -/
  map : α → β
  /-- A Turing machine computing `map` in polynomial time. -/
  polyTime : Nonempty (Turing.TM2ComputableInPolyTime ea eb map)
  /-- Yes-instances are mapped to yes-instances. -/
  yes_to_yes : ∀ a, yesa a → yesb (map a)
  /-- No-instances are mapped to no-instances. -/
  no_to_no : ∀ a, noa a → nob (map a)

end FourToOneGames


