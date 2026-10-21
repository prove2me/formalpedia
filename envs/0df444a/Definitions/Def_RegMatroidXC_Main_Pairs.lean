-- Prove2me | Definitions.Def_RegMatroidXC_Main_Pairs
-- name    : RegMatroidXC_Main_Pairs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:30.669106+00:00
-- url     : https://prove2.me/theorems/21a27a1d-4dad-4be2-9bbc-f4414acc89d4
-- title:
--   The pair of polytopes $P_{T_1,\dots,T_k}(M_0) \subseteq Q_{T_1,\dots,T_k}(M_0)$ of a star decomposition (p. 7)
-- statement:
--   Let $M_0$ be a matroid with finite ground set $E(M_0)$, and let $T_1, \dots, T_k \subseteq E(M_0)$ be triangles with named elements $T_i = \{\alpha_i, \beta_i, \gamma_i\}$. Put $E_0 := E(M_0) \setminus (T_1 \cup \dots \cup T_k)$. The polytopes below live in the space
--   $$\mathbb R^{E_0} \times \mathbb R^{T_1} \times \mathbb R^{T_1} \times \cdots \times \mathbb R^{T_k} \times \mathbb R^{T_k},$$
--   whose points are written $(x^0, x^{T'_1}, x^{T''_1}, \dots, x^{T'_k}, x^{T''_k})$: each triangle carries two copies $T'_i, T''_i$ of its coordinates.
--
--   1. $P_{T_1,\dots,T_k}(M_0)$ is the convex hull of the vectors $(\chi^{J_0}, \chi^{J'_1}, \chi^{J''_1}, \dots, \chi^{J'_k}, \chi^{J''_k})$ with $J_0 \subseteq E_0$ and $J'_i, J''_i \subseteq T_i$ such that $J_0 \cup J^*_1 \cup \dots \cup J^*_k$ is independent in $M_0$ for every choice $J^*_i \in \{J'_i, J''_i\}$, and for every $i$ either $J'_i = J''_i$, or $J'_i = \{\alpha_i, \beta_i\}$ and $J''_i = \{\beta_i, \gamma_i\}$.
--   2. $Q_{T_1,\dots,T_k}(M_0)$ is the set of points such that $(x^0, x^{T^*_1}, \dots, x^{T^*_k}) \in P(M_0)$ for every choice $T^*_i \in \{T'_i, T''_i\}$, $i \in [k]$.
--
--   One has $P_{T_1,\dots,T_k}(M_0) \subseteq Q_{T_1,\dots,T_k}(M_0)$. The extension complexity of the pair, $\mathrm{xc}(P, Q) = \min\{\mathrm{xc}(R) \mid R \text{ polytope}, P \subseteq R \subseteq Q\}$ (p. 7), is the quantity that Propositions 15, 16 and 18 bound; the file also records when a finite multigraph is connected.
--
--   **Formalization Note** The coordinates are indexed by pairs $(b, e)$: $(\mathrm{false}, e)$ for $e \in E(M_0)$ is $x^0_e$ when $e \in E_0$ and $x^{T'_i}_e$ when $e \in T_i$; $(\mathrm{true}, e)$, allowed only for $e$ in a triangle, is $x^{T''_i}_e$. A triangle is given by a map $\{0,1,2\} \to E$ ($\alpha_i, \beta_i, \gamma_i$ in this order). A choice $T^*_i$ is a map $s : [k] \to \{\mathrm{false}, \mathrm{true}\}$; for an element lying in several triangles the reading picks one of them, which never happens for the pairwise disjoint triangles of every statement. A multigraph on vertex set $V$ with edge $e$ from $\mathrm{tail}(e)$ to $\mathrm{head}(e)$ is connected when its underlying simple graph is.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 7 (Section 4.4: $P_{T_1,\dots,T_k}(M_0)$, $Q_{T_1,\dots,T_k}(M_0)$; xc of a pair, Section 4.3)

import Mathlib
import Definitions.Def_RegMatroidXC_Main_Matroids

namespace RegMatroidXC.Main

/-- Coordinates of the space `ℝ^{E₀} × ℝ^{T₁} × ℝ^{T₁} × ⋯ × ℝ^{T_k} × ℝ^{T_k}` of Section 4.4 (p. 7),
for a matroid `M₀` and triangles `Tᵢ = {tri i 0, tri i 1, tri i 2}` (`αᵢ, βᵢ, γᵢ` in the paper):
the index `(false, e)` with `e ∈ E(M₀)` is the coordinate `x⁰_e` if `e ∈ E₀ = E(M₀) \ ⋃ Tᵢ` and
`x^{T'ᵢ}_e` if `e ∈ Tᵢ`; the index `(true, e)`, allowed only for `e ∈ ⋃ Tᵢ`, is `x^{T''ᵢ}_e`. -/
def PairIdx {α : Type} (M₀ : Matroid α) {k : ℕ} (tri : Fin k → Fin 3 → α) : Type :=
  {p : Bool × M₀.E // p.1 = true → ∃ i j, tri i j = (p.2 : α)}

/-- The coordinate space of `PairIdx` is finite when `E(M₀)` is. -/
noncomputable instance PairIdx.instFintype {α : Type} (M₀ : Matroid α) {k : ℕ}
    (tri : Fin k → Fin 3 → α) [Finite M₀.E] : Fintype (PairIdx M₀ tri) :=
  haveI : Finite (PairIdx M₀ tri) := Subtype.finite
  Fintype.ofFinite _

/-- The triangle `Tᵢ = {αᵢ, βᵢ, γᵢ}` as a set. -/
def triSet {α : Type} {k : ℕ} (tri : Fin k → Fin 3 → α) (i : Fin k) : Set α :=
  Set.range (tri i)

/-- **The polytope `P_{T₁,…,T_k}(M₀)`** (p. 7): the convex hull of the vectors
`(χ^{J₀}, χ^{J'₁}, χ^{J''₁}, …, χ^{J'_k}, χ^{J''_k})` with `J₀ ⊆ E₀`, `J'ᵢ, J''ᵢ ⊆ Tᵢ`, such that
`J₀ ∪ J*₁ ∪ ⋯ ∪ J*_k` is independent in `M₀` for every choice `J*ᵢ ∈ {J'ᵢ, J''ᵢ}` (encoded by
`s : Fin k → Bool`, `true` choosing `J''ᵢ`), and for every `i`, `J'ᵢ = J''ᵢ` or
`J'ᵢ = {αᵢ, βᵢ}`, `J''ᵢ = {βᵢ, γᵢ}`. -/
noncomputable def PolyP {α : Type} (M₀ : Matroid α) {k : ℕ} (tri : Fin k → Fin 3 → α) :
    Set (PairIdx M₀ tri → ℝ) :=
  convexHull ℝ {x | ∃ (J₀ : Set α) (J' J'' : Fin k → Set α),
    J₀ ⊆ M₀.E \ ⋃ i, triSet tri i ∧ (∀ i, J' i ⊆ triSet tri i ∧ J'' i ⊆ triSet tri i) ∧
    (∀ s : Fin k → Bool, M₀.Indep (J₀ ∪ ⋃ i, if s i then J'' i else J' i)) ∧
    (∀ i, J' i = J'' i ∨ (J' i = {tri i 0, tri i 1} ∧ J'' i = {tri i 1, tri i 2})) ∧
    ∀ p : PairIdx M₀ tri, x p =
      (if p.1.1 then ⋃ i, J'' i else J₀ ∪ ⋃ i, J' i).indicator (fun _ => (1 : ℝ)) (p.1.2 : α)}

open Classical in
/-- For a choice `s : Fin k → Bool` (`true` at `i` choosing `T''ᵢ`, `false` choosing `T'ᵢ`), the
vector `(x⁰, x^{T*₁}, …, x^{T*_k}) ∈ ℝ^{E(M₀)}` read off a point `x` of the pair space. An element of
`E₀` reads `x⁰`; an element of a triangle `Tᵢ` reads the copy chosen by `s i` (for disjoint
triangles the triangle containing `e` is unique). -/
noncomputable def choiceVec {α : Type} {M₀ : Matroid α} {k : ℕ} {tri : Fin k → Fin 3 → α}
    (s : Fin k → Bool) (x : PairIdx M₀ tri → ℝ) : M₀.E → ℝ :=
  fun e => if h : ∃ i j, tri i j = (e : α) then x ⟨(s (Classical.choose h), e), fun _ => h⟩
    else x ⟨(false, e), fun h' => absurd h' Bool.false_ne_true⟩

/-- **The polytope `Q_{T₁,…,T_k}(M₀)`** (p. 7): the points `(x⁰, x^{T'₁}, x^{T''₁}, …)` such that
`(x⁰, x^{T*₁}, …, x^{T*_k}) ∈ P(M₀)` for every choice `T*ᵢ ∈ {T'ᵢ, T''ᵢ}`. -/
def PolyQ {α : Type} (M₀ : Matroid α) {k : ℕ} (tri : Fin k → Fin 3 → α) :
    Set (PairIdx M₀ tri → ℝ) :=
  {x | ∀ s : Fin k → Bool, choiceVec s x ∈ indepPolytope M₀}

/-- The finite multigraph with vertex set `V` and edges `e ∈ E(M₀)` from `tail e` to `head e` is
**connected** (its underlying simple graph is connected). -/
def MultigraphConnected {α : Type} (M₀ : Matroid α) (V : Type) (tail head : α → V) : Prop :=
  (SimpleGraph.fromRel (fun u v : V => ∃ e ∈ M₀.E, tail e = u ∧ head e = v)).Connected

end RegMatroidXC.Main


