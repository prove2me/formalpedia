-- Prove2me | Definitions.Def_BeyondGomoryHu_Units_Cuts
-- name    : BeyondGomoryHu_Units_Cuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:40:21.560809+00:00
-- url     : https://prove2.me/theorems/b311fb12-9d7c-4055-a230-3fd051ba0ff4
-- title:
--   Capacity, S-cuts (corrected: S-cut meets S on both sides), S-mincuts, units, valid partitions and the order ≼(x,y)
-- statement:
--   Let $G=(V,E,w)$ be an undirected graph with positive integer edge weights, encoded by a symmetric weight $w(a,b)\in\mathbb N$ on vertex pairs ($0$ means no edge). The **capacity** of $A\subseteq V$ is $c(A)=\sum_{a\in A,\ b\notin A} w(a,b)$.
--
--   For a terminal set $S$, a set $A$ is an **$S$-cut** if $A\cap S\neq\emptyset$ and $\bar A\cap S\neq\emptyset$. The page prints "$A\cap S=\emptyset$"; read literally, $\emptyset$ would be the unique $S$-mincut of every connected graph, so the definition is corrected to the one every proof uses. $\lambda_S\in\mathbb N\cup\{\infty\}$ is the least capacity of an $S$-cut ($\infty$ if there is none, so $\lambda_{x,x}=\infty$), and an **$S$-mincut** is an $S$-cut of capacity $\lambda_S$. An $(x,y)$-mincut is an $\{x,y\}$-mincut $A$ with $x\in A$, $y\notin A$.
--
--   Two vertices are **$S$-equivalent** ($\phi_S(u)=\phi_S(v)$) if no $S$-mincut separates them; the classes are the **$S$-units**, and $d(S)$ is the number of units meeting $S$ ($0$ if $|S|\le1$). A partition $S_1,S\setminus S_1$ is **valid** if some $S$-mincut induces it; $v$ is **distinguished** by it if two $S$-mincuts inducing it keep $v$ with $S_1$ and with $S\setminus S_1$ respectively; $v$ is **stretched** if some valid partition distinguishes it.
--
--   Definition 6.1: $u\preceq_{(x,y)}v$ iff every $x,y$-mincut with $v$ on the side of $x$ has $u$ on the side of $x$; for sets, every element of the first precedes every element of the second; $U\prec U'$ iff $U\preceq U'$ and not $U'\preceq U$. A topological ordering of the $x,y$-units lists each unit once with $U_j\not\preceq U_i$ for all $i<j$.
--
--   These are the objects in which every statement of the mission is written.
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Section 2, p. 3 (PDF 5); Definition 6.1, p. 20 (PDF 22); Lemmas 2.5–2.6, p. 4 (PDF 6)

import Mathlib

set_option autoImplicit false

namespace BeyondGomoryHu.Units

/-!
Section 2 (p. 3) of Bhanja–Parter–Petruschka, *Beyond Gomory-Hu*: weighted graphs, capacities,
Steiner cuts (corrected), Steiner mincuts, units, valid partitions, distinguished and stretched
vertices; and Definition 6.1 (p. 20), the relation `≼(x,y)` and topological orderings of units.
-/

/-- An undirected graph with nonnegative integer weights on vertex pairs. `w a b = 0` means that
`a` and `b` are not adjacent; a positive value is the edge weight (parallel edges are added up).
The diagonal is irrelevant: a loop never crosses a cut. -/
structure WGraph (V : Type) where
  w : V → V → ℕ
  symm : ∀ a b, w a b = w b a

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The graph is connected: the simple graph of the pairs with positive weight is connected. -/
def WGraph.Connected (G : WGraph V) : Prop :=
  (SimpleGraph.fromRel (fun a b => 0 < G.w a b)).Connected

/-- Capacity `c(A)`: the total weight of the edges between `A` and `V \ A`. -/
def cap (G : WGraph V) (A : Finset V) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ Aᶜ, G.w a b

/-- `A` is an `S`-cut: it contains a terminal of `S` and misses a terminal of `S`.
(Corrected: the page prints `A ∩ S = ∅`; see the item's natural-language statement.) -/
def IsCut (S A : Finset V) : Prop :=
  (A ∩ S).Nonempty ∧ (S \ A).Nonempty

/-- `λ_S`, the minimum capacity of an `S`-cut, in `ℕ∞`; it is `∞` when no `S`-cut exists
(in particular `λ_{x,x} = ∞`). -/
noncomputable def lam (G : WGraph V) (S : Finset V) : ℕ∞ :=
  ⨅ (A : Finset V) (_ : IsCut S A), (cap G A : ℕ∞)

/-- `A` is an `S`-mincut: an `S`-cut of the smallest capacity. -/
def IsMincut (G : WGraph V) (S A : Finset V) : Prop :=
  IsCut S A ∧ ∀ B : Finset V, IsCut S B → cap G A ≤ cap G B

/-- `A` is an `(x, y)`-mincut: an `x, y`-mincut with `x ∈ A` and `y ∉ A`. -/
def IsOrientedMincut (G : WGraph V) (x y : V) (A : Finset V) : Prop :=
  IsMincut G {x, y} A ∧ x ∈ A ∧ y ∉ A

/-- `u` and `v` are `S`-equivalent: no `S`-mincut separates them. Its classes are the `S`-units,
and `ϕ_S(u) = ϕ_S(v)` means `SEquiv G S u v`. -/
def SEquiv (G : WGraph V) (S : Finset V) (u v : V) : Prop :=
  ∀ A : Finset V, IsMincut G S A → (u ∈ A ↔ v ∈ A)

/-- `u` and `v` lie in the same `x, y`-unit (`ϕ_{x,y}(u) = ϕ_{x,y}(v)`). -/
def SameUnit (G : WGraph V) (x y u v : V) : Prop :=
  SEquiv G {x, y} u v

/-- The `S`-unit of `u`. -/
noncomputable def unitOf (G : WGraph V) (S : Finset V) (u : V) : Finset V :=
  open Classical in Finset.univ.filter (fun v => SEquiv G S u v)

/-- `U` is an `S`-unit. -/
def IsUnit (G : WGraph V) (S U : Finset V) : Prop :=
  ∃ u : V, U = unitOf G S u

/-- `d(S)`: the number of terminal `S`-units (those meeting `S`), and `0` when `|S| ≤ 1`. -/
noncomputable def dS (G : WGraph V) (S : Finset V) : ℕ :=
  if S.card ≤ 1 then 0 else (S.image (fun s => unitOf G S s)).card

/-- The `S`-mincut `A` induces the partition `S₁, S \ S₁` of `S`. -/
def InducesSide (S A : Finset V) (S₁ : Set V) : Prop :=
  ((A ∩ S : Finset V) : Set V) = S₁ ∨ ((A ∩ S : Finset V) : Set V) = (S : Set V) \ S₁

/-- `S₁, S \ S₁` is a valid partition: it is induced by some `S`-mincut. -/
def IsValidSide (G : WGraph V) (S : Finset V) (S₁ : Set V) : Prop :=
  ∃ A : Finset V, IsMincut G S A ∧ InducesSide S A S₁

/-- The cut `A` (inducing `S₁, S \ S₁`) keeps `v` on the side containing `S₁`. -/
def OnSide (S A : Finset V) (S₁ : Set V) (v : V) : Prop :=
  (v ∈ A ↔ ((A ∩ S : Finset V) : Set V) = S₁)

/-- `v` is distinguished by the partition `S₁, S \ S₁`: there are two `S`-mincuts inducing it,
one keeping `v` with `S₁` and the other keeping `v` with `S \ S₁`. -/
def DistinguishedBy (G : WGraph V) (S : Finset V) (S₁ : Set V) (v : V) : Prop :=
  ∃ A B : Finset V, IsMincut G S A ∧ IsMincut G S B ∧ InducesSide S A S₁ ∧ InducesSide S B S₁ ∧
    OnSide S A S₁ v ∧ ¬ OnSide S B S₁ v

/-- `v` is stretched (w.r.t. `S`): it is distinguished by at least one valid partition. -/
def Stretched (G : WGraph V) (S : Finset V) (v : V) : Prop :=
  ∃ S₁ : Set V, IsValidSide G S S₁ ∧ DistinguishedBy G S S₁ v

/-- Definition 6.1: `u ≼(x,y) v` iff every `x, y`-mincut with `v` on the side of `x` also has
`u` on the side of `x`. -/
def Prec (G : WGraph V) (x y u v : V) : Prop :=
  ∀ A : Finset V, IsMincut G {x, y} A → ((v ∈ A ↔ x ∈ A) → (u ∈ A ↔ x ∈ A))

/-- `≼(x,y)` extended to sets (used for atomic sets): every element of `U` precedes every
element of `U'`. -/
def SetPrec (G : WGraph V) (x y : V) (U U' : Set V) : Prop :=
  ∀ u ∈ U, ∀ u' ∈ U', Prec G x y u u'

/-- `U ≺(x,y) U'`: `U ≼ U'` but not `U' ≼ U`. -/
def SetStrict (G : WGraph V) (x y : V) (U U' : Set V) : Prop :=
  SetPrec G x y U U' ∧ ¬ SetPrec G x y U' U

/-- `u` and `v` are comparable w.r.t. `x, y`. -/
def Comparable (G : WGraph V) (x y u v : V) : Prop :=
  Prec G x y u v ∨ Prec G x y v u

/-- The vertices of `U` all lie in one `x, y`-unit together with the vertices of `U'`. -/
def SameUnitSets (G : WGraph V) (x y : V) (U U' : Set V) : Prop :=
  ∀ u ∈ U, ∀ u' ∈ U', SameUnit G x y u u'

/-- Definition 6.1: the list `L` is a topological ordering of the `x, y`-units: it lists every
`x, y`-unit exactly once, and `L_j ⋠ L_i` whenever `i < j`. -/
def IsTopOrderOfUnits (G : WGraph V) (x y : V) (L : List (Finset V)) : Prop :=
  L.Nodup ∧ (∀ U : Finset V, U ∈ L ↔ IsUnit G {x, y} U) ∧
    L.Pairwise (fun U U' => ¬ SetPrec G x y (U' : Set V) (U : Set V))

/-- Lemma 2.5's four cuts `A ∩ B, A ∪ B, A \ B, B \ A`, in this order. -/
def fourCuts (A B : Finset V) : Fin 4 → Finset V :=
  ![A ∩ B, A ∪ B, A \ B, B \ A]

/-- Lemma 2.6's four sets `A \ (B ∪ C), B \ (A ∪ C), C \ (A ∪ B), A ∩ B ∩ C`, in this order. -/
def fourComponents (A B C : Finset V) : Fin 4 → Finset V :=
  ![A \ (B ∪ C), B \ (A ∪ C), C \ (A ∪ B), A ∩ B ∩ C]

end BeyondGomoryHu.Units


