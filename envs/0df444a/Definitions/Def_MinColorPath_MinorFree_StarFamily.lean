-- Prove2me | Definitions.Def_MinColorPath_MinorFree_StarFamily
-- name    : MinColorPath_MinorFree_StarFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:12:28.272303+00:00
-- url     : https://prove2.me/theorems/0e0e0da2-097f-413e-9ec5-c8ada778496f
-- title:
--   Star family, cover number, (A, B)-separators, the separator LP and well-linked diagrams
-- statement:
--   Let $\mathcal D=(D,P',\mathrm{cl}')$ be the diagram of a subgraph $G'$ of a colored graph $\mathcal G$. For $\tau\in P'$ let $F_\tau=\{\tau\}\cup\{v\in V(G'):\tau\in\mathrm{cl}'(v)\}$; the **star family** is $\mathcal F=\{F_\tau:\tau\in P'\}$, and $\mathcal F_Q=\bigcup_{\tau\in Q}F_\tau$. The **cover number** $\mathrm{cov}_{\mathcal F}(Z)$ is the least size of a subfamily covering $Z$ ($+\infty$ if none). An **$(A,B)$-separator** is a vertex set meeting every path from $A$ to $B$. **LP 1** for $(A,B,D)$ is
--   $$\min\sum_{F\in\mathcal F}x_F\quad\text{s.t.}\quad\sum_{F\cap Q\neq\emptyset}x_F\ge1\ \text{ for every induced } A\text{–}B \text{ path } Q,\quad x\ge0.$$
--   $\mathcal D$ is **well-linked** if some $P^\star\subseteq P'$ with $|P^\star|\ge20(\mathrm{cdeg}(\mathcal G)+1)^3$ satisfies: for all nonempty $P_1,P_2\subseteq P^\star$, every $(\mathcal F_{P_1},\mathcal F_{P_2})$-separator $S$ has $\mathrm{cov}_{\mathcal F}(S)\ge\min\{|P_1|,|P_2|\}$.
--
--   **Formalization Note.** Members of $\mathcal F$ are indexed by their colors (`star cl H τ`), a subfamily is a set of colors; `covF` is in `ℕ∞`. `LPAtMost cl H A B ℓ` states that LP 1 has a feasible point of value at most `ℓ`, which is equivalent to "optimal value at most `ℓ`" because the LP has finitely many constraints and a nonnegative objective. Induced means chordless.
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), pp. 25–27, star family, cover number, LP (1)–(2), well-linkedness

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_TreeDecomposition

set_option autoImplicit false

/-!
# Star family, cover number, separators, the separator LP and well-linkedness (pp. 25–27)

Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, *Algorithms for Min-Color Path with Bounded
Color-Degree* (STOC 2027 submission), pp. 25–27.

For the diagram `D = (D, P', cl')` of a subgraph `G'`: `F_τ = {τ} ∪ V'_τ` with
`V'_τ = {v ∈ V(G') : τ ∈ cl'(v)}`, the star family `F = {F_τ : τ ∈ P'}`, `F_Q = ⋃_{τ ∈ Q} F_τ`.

Conventions.
* The members of the star family are indexed by their colors `τ ∈ P'` (distinct colors give
  distinct members, since `τ ∈ F_τ` only), so a subfamily is a set `R ⊆ P'`.
* `cov_F(Z) ∈ ℕ∞` is the least `|R|` with `Z ⊆ F_R` (`⊤` if none, p. 25).
* An `(A, B)`-separator meets every path of `D` from a vertex of `A` to a vertex of `B`
  (a vertex of `A ∩ B` is a one-vertex path, so it must be in `S`).
* LP 1 (p. 26) has a constraint for every induced `A`–`B` path (a path with no chord). "Its
  optimal value is at most `ℓ`" is the existence of a feasible point of value at most `ℓ`: the LP
  has finitely many constraints and a nonnegative objective, so its optimum is attained when it is
  feasible, and it is `+∞` when it is not.
-/

namespace MinColorPath.MinorFree

noncomputable section

open Classical

variable {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- `F_τ = {τ} ∪ {v ∈ V(G') : τ ∈ cl'(v)}` (p. 25). -/
def star {G : SimpleGraph V} (cl : V → Finset C) (H : G.Subgraph) (τ : ↥(diagPal cl H)) :
    Finset (DV cl H) :=
  Finset.univ.filter fun y => y = Sum.inr τ ∨ ∃ v, y = Sum.inl v ∧ τ.1 ∈ cl v.1

/-- `F_R = ⋃_{τ ∈ R} F_τ`. -/
def starUnion {G : SimpleGraph V} (cl : V → Finset C) (H : G.Subgraph)
    (R : Finset ↥(diagPal cl H)) : Finset (DV cl H) :=
  R.biUnion (star cl H)

/-- The cover number `cov_F(Z)` (p. 25), `⊤` when no subfamily covers `Z`. -/
def covF {G : SimpleGraph V} (cl : V → Finset C) (H : G.Subgraph) (Z : Finset (DV cl H)) : ℕ∞ :=
  ⨅ (R : Finset ↥(diagPal cl H)) (_ : Z ⊆ starUnion cl H R), (R.card : ℕ∞)

/-- `S` is an `(A, B)`-separator in `D`: every path from a vertex of `A` to a vertex of `B`
contains a vertex of `S`. -/
def IsSeparator {W : Type} (D : SimpleGraph W) (A B S : Finset W) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : D.Walk a b, p.IsPath → ∃ v ∈ p.support, v ∈ S

/-- An induced path: a path of `D` with no chord (every edge of `D` between two of its vertices
is an edge of the path). -/
def IsInducedPath {W : Type} {D : SimpleGraph W} {a b : W} (p : D.Walk a b) : Prop :=
  p.IsPath ∧ ∀ u ∈ p.support, ∀ v ∈ p.support, D.Adj u v → s(u, v) ∈ p.edges

/-- LP 1 for `(A, B, D)` (p. 26) has optimal value at most `ℓ`: some `x ≥ 0` indexed by the star
family satisfies `∑_{F ∩ Q ≠ ∅} x_F ≥ 1` for every induced `A`–`B` path `Q` of the diagram
`D` and has `∑_F x_F ≤ ℓ`. -/
def LPAtMost {G : SimpleGraph V} (cl : V → Finset C) (H : G.Subgraph)
    (A B : Finset (DV cl H)) (ℓ : ℝ) : Prop :=
  ∃ x : ↥(diagPal cl H) → ℝ, (∀ τ, 0 ≤ x τ) ∧
    (∀ a ∈ A, ∀ b ∈ B, ∀ p : (diagGraph cl 1 H).Walk a b, IsInducedPath p →
      1 ≤ ∑ τ ∈ Finset.univ.filter (fun τ => ∃ v ∈ p.support, v ∈ star cl H τ), x τ) ∧
    ∑ τ, x τ ≤ ℓ

/-- The diagram `D` of `G'` is well-linked (p. 27): some `P⋆ ⊆ P'` with
`|P⋆| ≥ 20 (cdeg(G) + 1)^3` such that for all nonempty `P_1, P_2 ⊆ P⋆`, every
`(F_{P_1}, F_{P_2})`-separator `S` of `D` has `cov_F(S) ≥ min{|P_1|, |P_2|}`. -/
def WellLinked {G : SimpleGraph V} (P : Finset C) (cl : V → Finset C) (H : G.Subgraph) : Prop :=
  ∃ Pst : Finset ↥(diagPal cl H), 20 * (cdeg P cl + 1) ^ 3 ≤ Pst.card ∧
    ∀ P₁ ⊆ Pst, ∀ P₂ ⊆ Pst, P₁.Nonempty → P₂.Nonempty →
      ∀ S, IsSeparator (diagGraph cl 1 H) (starUnion cl H P₁) (starUnion cl H P₂) S →
        ((min P₁.card P₂.card : ℕ) : ℕ∞) ≤ covF cl H S

end

end MinColorPath.MinorFree


