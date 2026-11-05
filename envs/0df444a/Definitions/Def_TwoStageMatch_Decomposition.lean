-- Prove2me | Definitions.Def_TwoStageMatch_Decomposition
-- name    : TwoStageMatch_Decomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:54.202583+00:00
-- url     : https://prove2.me/theorems/ab4d0111-3bb3-49e2-9025-b7f43d77e627
-- title:
--   Levels $(D^{(l)},S^{(l)})$ and slacks $c^{(l)}$ of the structural decomposition (Lemma 1)
-- statement:
--   Let $x$ be a fractional first-stage matching (in Lemma 1, the optimal $x^*$ of $\mathscr P^g$), and write $y_j=\sum_{i\in N(j)}x_{ij}$ for the load of supply $j$. Define
--   $$S^{(0)}=\{j\in S: y_j=1\},\qquad D^{(0)}=\{i\in D_1:\exists j\in S^{(0)},\ x_{ij}>0\}.$$
--   Let $G'$ be the graph on $D_1\cup S$ with an edge $\{i,j\}$ whenever $x_{ij}>0$, and consider the connected components of the induced subgraph $G'[D_1\setminus D^{(0)},S\setminus S^{(0)}]$.
--
--   1. Every vertex has a **level**: level $0$ for the vertices of $D^{(0)}\cup S^{(0)}$, and otherwise the component containing it. The levels partition $D_1\cup S$.
--   2. The **slack** of a level is $c^{(0)}=0$; for a component it is $w_j(1-y_j)$ for a chosen supply vertex $j$ of the component (Lemma 1 shows the choice is immaterial), and $0$ for a component that contains no supply vertex.
--
--   **Formalization Note** Levels are elements of $\mathrm{Option}$ of the type of connected components (`none` is level 0). The paper numbers the components $1,\dots,L$ and does not consider components without supply vertices; giving them slack $0$ is the convention of Lemma 1 (corrected).
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, Lemma 1, pp.13–14 (restated p.ec4)

import Mathlib

open Finset

namespace TwoStageMatch

/-!
# The structural decomposition of Lemma 1: levels and their slacks `c^{(l)}`

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, Lemma 1, pp.13–14 (restated p.ec4).

For a fractional first-stage matching `x` (in Lemma 1, the optimal `x*` of `𝒫^g`):
* `y_j = Σ_{i ∈ N(j)} x_{ij}` is the load of supply `j` (p.15, `y*_j`);
* `S⁽⁰⁾ = {j ∈ S : y_j = 1}` and `D⁽⁰⁾ = {i ∈ D₁ : ∃ j ∈ S⁽⁰⁾, x_{ij} > 0}`;
* `G′` is the graph on `D₁ ⊕ S` with an edge between `i` and `j` iff `x_{ij} > 0`, and the
  remaining levels are the connected components of its subgraph induced on
  `(D₁ \ D⁽⁰⁾) ∪ (S \ S⁽⁰⁾)`.

**Formalization Note.** A level is an element of `Option C`, where `C` is the type of connected
components of the induced subgraph: `none` is level `0`, `some K` is the component `K`. Every
`i ∈ D₁` and every `j ∈ S` has exactly one level (`levelD`, `levelS`), so the levels partition
the vertices. The slack of level `0` is `c⁽⁰⁾ = 0`; the slack of a component is
`w_j (1 − y_j)` for a chosen supply vertex `j` of that component (Lemma 1(i) says the choice
does not matter); a component that contains no supply vertex — the paper overlooks this case,
see Lemma 1 (corrected) — gets slack `0`.
-/

variable {D₁ S : Type*}

section
variable [Fintype D₁] [Fintype S] [DecidableEq D₁] [DecidableEq S]

/-- `y_j = Σ_{i ∈ N(j)} x_{ij}` (for an `x` vanishing off the edges). -/
def load (x : D₁ → S → ℝ) (j : S) : ℝ := ∑ i, x i j

/-- `S⁽⁰⁾ = {j ∈ S : Σ_{i ∈ N(j)} x_{ij} = 1}`, the supplies fully matched by `x`. -/
noncomputable def S0 (x : D₁ → S → ℝ) : Finset S :=
  open Classical in (Finset.univ : Finset S).filter (fun j => load x j = 1)

/-- `D⁽⁰⁾ = {i ∈ D₁ : ∃ j ∈ S⁽⁰⁾, x_{ij} > 0}`. -/
noncomputable def D0 (x : D₁ → S → ℝ) : Finset D₁ :=
  open Classical in (Finset.univ : Finset D₁).filter (fun i => ∃ j ∈ S0 x, 0 < x i j)

/-- The support graph `G′ = (D₁, S, E′)`, `E′ = {(i, j) : x_{ij} > 0}`, as a simple graph on
`D₁ ⊕ S`. -/
def supportGraph (x : D₁ → S → ℝ) : SimpleGraph (D₁ ⊕ S) :=
  SimpleGraph.fromRel fun u v => ∃ i j, u = Sum.inl i ∧ v = Sum.inr j ∧ 0 < x i j

/-- The vertex set `(D₁ \ D⁽⁰⁾) ∪ (S \ S⁽⁰⁾)`. -/
noncomputable def residualVertices (x : D₁ → S → ℝ) : Set (D₁ ⊕ S) :=
  {v | (∃ i, v = Sum.inl i ∧ i ∉ D0 x) ∨ (∃ j, v = Sum.inr j ∧ j ∉ S0 x)}

/-- The induced subgraph `G′[D₁ \ D⁽⁰⁾, S \ S⁽⁰⁾]`. -/
noncomputable def residualGraph (x : D₁ → S → ℝ) : SimpleGraph (residualVertices x) :=
  (supportGraph x).induce (residualVertices x)

/-- The levels: `none` is level `0`, `some K` is a connected component `K` of
`G′[D₁ \ D⁽⁰⁾, S \ S⁽⁰⁾]`. -/
abbrev Level (x : D₁ → S → ℝ) : Type _ := Option (residualGraph x).ConnectedComponent

/-- The level of a first-stage demand vertex `i`: `0` if `i ∈ D⁽⁰⁾`, else its component. -/
noncomputable def levelD (x : D₁ → S → ℝ) (i : D₁) : Level x :=
  if h : i ∈ D0 x then none
  else some ((residualGraph x).connectedComponentMk ⟨Sum.inl i, Or.inl ⟨i, rfl, h⟩⟩)

/-- The level of a supply vertex `j`: `0` if `j ∈ S⁽⁰⁾`, else its component. -/
noncomputable def levelS (x : D₁ → S → ℝ) (j : S) : Level x :=
  if h : j ∈ S0 x then none
  else some ((residualGraph x).connectedComponentMk ⟨Sum.inr j, Or.inr ⟨j, rfl, h⟩⟩)

/-- The slack `c⁽ˡ⁾` of a level for weights `w`: `c⁽⁰⁾ = 0`; for a component, `w_j (1 − y_j)` for a
chosen supply vertex `j` of the component, and `0` if the component has no supply vertex. -/
noncomputable def levelSlack (w : S → ℝ) (x : D₁ → S → ℝ) : Level x → ℝ
  | none => 0
  | some K =>
    open Classical in
    if h : ∃ j, levelS x j = some K then w h.choose * (1 - load x h.choose) else 0

end

end TwoStageMatch


