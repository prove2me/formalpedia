-- Prove2me | Definitions.Def_StrongPerfectGraph_DoubleSplit_KnotOutcomes
-- name    : StrongPerfectGraph_DoubleSplit_KnotOutcomes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:05:30.730139+00:00
-- url     : https://prove2.me/theorems/f04a37c4-7935-430a-9129-204b0a3015e0
-- title:
--   The outcomes 2–4 of 9.3 and the symmetry of a knot
-- statement:
--   Let $(P_1, P_2, Q_1, Q_2)$ be a knot in $G$ with ends $a_i, b_i, x_j, y_j$, let $F \subseteq V(G)$ and write $W = V(P_2) \cup V(Q_1) \cup V(Q_2)$.
--
--   1. **Outcome 2**: there is a path $R$ in $F$ with ends $r_1, r_2$ such that $r_1, a_1$ have the same neighbours in $W$, there are no edges between $R \setminus r_1$ and $W$, $r_2$ has a neighbour in $P_1 \setminus a_1$, and there are no edges between $R \setminus r_2$ and $P_1 \setminus a_1$.
--   2. **Outcome 3**: there is an odd path $R$ in $F$ with ends $r_1, r_2$ such that $r_1, a_1$ have the same neighbours in $W$, so do $r_2, b_1$, there are no edges between the interior $R^*$ and $W$, and no edges between $R$ and $P_1$ except possibly $r_1a_1$ and $r_2b_1$.
--   3. **Outcome 4**: there is $f \in F$ such that $f, x_1$ have the same neighbours in $V(P_1) \cup V(P_2) \cup V(Q_2)$ and $f$ is not adjacent to $y_1$.
--
--   An outcome holds **up to symmetry** if it holds for the knot as labelled or after exchanging $P_1, P_2$ and $Q_1, Q_2$ and renaming the ends accordingly. Writing $P^{r}$ for a reversed path, the quadruples considered are
--
--   $$(P_1, P_2, Q_1, Q_2),\quad (P_1^r, P_2^r, Q_1^r, Q_2^r),\quad (P_2^r, P_1, Q_2, Q_1^r),\quad (P_2, P_1^r, Q_2^r, Q_1).$$
--
--   The last two are the two relabellings of the exchanged quadruple that are again knots; the second is their composite.
--
--   These predicates make up the conclusion of 9.3.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 109, §9, statements 2–4 of 9.3 and the meaning of "up to symmetry"

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

namespace StrongPerfectGraph.DoubleSplit

/-- Outcome 2 of 9.3 for the knot `(P₁, P₂, Q₁, Q₂)` with `a₁ = P₁.head`: a path `R` in `F` with
ends `r₁ = R.head`, `r₂ = R.getLast` such that `r₁, a₁` have the same neighbours in
`W = V(P₂) ∪ V(Q₁) ∪ V(Q₂)`, there are no edges between `R \ r₁` and `W`, `r₂` has a neighbour in
`P₁ \ a₁`, and there are no edges between `R \ r₂` and `P₁ \ a₁`. -/
def KnotOutcome2 {V : Type*} (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) (F : Set V) : Prop :=
  ∃ (R : List V) (a₁ r₁ r₂ : V), P₁.head? = some a₁ ∧
    StrongPerfectGraph.Main.IsInducedPath G R ∧ (∀ v ∈ R, v ∈ F) ∧ R.head? = some r₁ ∧ R.getLast? = some r₂ ∧
    (∀ w, (w ∈ P₂ ∨ w ∈ Q₁ ∨ w ∈ Q₂) → (G.Adj r₁ w ↔ G.Adj a₁ w)) ∧
    (∀ v ∈ R, v ≠ r₁ → ∀ w, (w ∈ P₂ ∨ w ∈ Q₁ ∨ w ∈ Q₂) → ¬ G.Adj v w) ∧
    (∃ u ∈ P₁, u ≠ a₁ ∧ G.Adj r₂ u) ∧
    (∀ v ∈ R, v ≠ r₂ → ∀ u ∈ P₁, u ≠ a₁ → ¬ G.Adj v u)

/-- Outcome 3 of 9.3 for the knot `(P₁, P₂, Q₁, Q₂)` with `a₁ = P₁.head`, `b₁ = P₁.getLast`: an
odd path `R` in `F` with ends `r₁, r₂` such that `r₁, a₁` have the same neighbours in
`W = V(P₂) ∪ V(Q₁) ∪ V(Q₂)`, so do `r₂, b₁`, there are no edges between the interior `R*` and `W`,
and the only possible edges between `R` and `P₁` are `r₁a₁` and `r₂b₁`. -/
def KnotOutcome3 {V : Type*} (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) (F : Set V) : Prop :=
  ∃ (R : List V) (a₁ b₁ r₁ r₂ : V), P₁.head? = some a₁ ∧ P₁.getLast? = some b₁ ∧
    StrongPerfectGraph.Main.IsInducedPath G R ∧ Odd (R.length - 1) ∧ (∀ v ∈ R, v ∈ F) ∧
    R.head? = some r₁ ∧ R.getLast? = some r₂ ∧
    (∀ w, (w ∈ P₂ ∨ w ∈ Q₁ ∨ w ∈ Q₂) → (G.Adj r₁ w ↔ G.Adj a₁ w)) ∧
    (∀ w, (w ∈ P₂ ∨ w ∈ Q₁ ∨ w ∈ Q₂) → (G.Adj r₂ w ↔ G.Adj b₁ w)) ∧
    (∀ v ∈ R, v ≠ r₁ → v ≠ r₂ → ∀ w, (w ∈ P₂ ∨ w ∈ Q₁ ∨ w ∈ Q₂) → ¬ G.Adj v w) ∧
    (∀ v ∈ R, ∀ u ∈ P₁, G.Adj v u → (v = r₁ ∧ u = a₁) ∨ (v = r₂ ∧ u = b₁))

/-- Outcome 4 of 9.3 for the knot `(P₁, P₂, Q₁, Q₂)` with `x₁ = Q₁.head`, `y₁ = Q₁.getLast`: a
vertex `f ∈ F` such that `f, x₁` have the same neighbours in `V(P₁) ∪ V(P₂) ∪ V(Q₂)` and `f` is
not adjacent to `y₁`. -/
def KnotOutcome4 {V : Type*} (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) (F : Set V) : Prop :=
  ∃ (x₁ y₁ : V), Q₁.head? = some x₁ ∧ Q₁.getLast? = some y₁ ∧
    ∃ f ∈ F, (∀ w, (w ∈ P₁ ∨ w ∈ P₂ ∨ w ∈ Q₂) → (G.Adj f w ↔ G.Adj x₁ w)) ∧ ¬ G.Adj f y₁

/-- "Up to symmetry" (p. 109): the outcome holds for the knot as labelled, or after exchanging
`P₁, P₂` and `Q₁, Q₂` and renaming the ends accordingly. The relabellings of the exchanged
quadruple that are again knots are `(P₂ʳ, P₁, Q₂, Q₁ʳ)` and `(P₂, P₁ʳ, Q₂ʳ, Q₁)` (`ʳ` = reversed
list); the symmetry group they generate also contains the reversal `(P₁ʳ, P₂ʳ, Q₁ʳ, Q₂ʳ)` of all
four. -/
def UpToKnotSymmetry {V : Type*} (O : List V → List V → List V → List V → Prop)
    (P₁ P₂ Q₁ Q₂ : List V) : Prop :=
  O P₁ P₂ Q₁ Q₂ ∨ O P₁.reverse P₂.reverse Q₁.reverse Q₂.reverse ∨
  O P₂.reverse P₁ Q₂ Q₁.reverse ∨ O P₂ P₁.reverse Q₂.reverse Q₁

end StrongPerfectGraph.DoubleSplit


