-- Prove2me | Definitions.Def_ThinFlowSP_Breakpoints_Model
-- name    : ThinFlowSP_Breakpoints_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:47.401989+00:00
-- url     : https://prove2.me/theorems/54c8dcb8-7396-4134-aef1-86a049575b41
-- title:
--   Definition 4, (LCP), π and ϱ^{G′}, pp. 5–11 — normalized thin flows with resetting, the LCP matrix, normalization, label functions, breakpoints
-- statement:
--   Fix a network $G = (V, A')$ with source $s$ and sink $t$, a set $A^* \subseteq A'$ of **resetting arcs** and capacities $\nu \in \mathbb R^{A'}$.
--
--   1. (Definition 4.) Along an arc $a = (v, w)$ the label is propagated by
--   $$\varrho^a(\ell'_v, x'_a) = \begin{cases}\max\{\ell'_v, x'_a/\nu_a\} & a \in A'\setminus A^*,\\ x'_a/\nu_a & a \in A^*.\end{cases}$$
--   Labels $\ell' \in \mathbb R^V$ are **corresponding labels** of the flow $x'$ if $\ell' \ge 0$, $\ell'_w = \min_{a=(v,w)\in\delta^-(w)} \varrho^a(\ell'_v, x'_a)$ for every $w \ne s$ (the minimum is attained), and $\ell'_w = \varrho^a(\ell'_v, x'_a)$ for every arc $a = (v,w)$ with $x'_a > 0$. A static $s$–$t$-flow admitting corresponding labels is a **normalized thin $s$–$t$-flow with resetting**. The label at $s$ is not fixed.
--   2. A **label function** is a map $\varrho : \mathbb R \to \mathbb R^V$ such that, for every $\nu'_0 \ge 0$, $\varrho(\nu'_0)_s = 1$ and $\varrho(\nu'_0)$ are corresponding labels of some normalized thin $s$–$t$-flow with resetting of value $\nu'_0$. This is the defining property of the function $\varrho^{G'}$ of Proposition 17; a pair $(\varrho, \chi)$ is a **parametric thin flow** if moreover $\chi(\nu'_0)$ is such a flow for every $\nu'_0 \ge 0$.
--   3. A **breakpoint** of a function $f : \mathbb R \to \mathbb R^\iota$ is a point $x > 0$ such that on no open interval around $x$ are all components of $f$ affine.
--   4. (Theorem 6.) The matrix of (LCP) is indexed by $V \uplus A' \uplus (A'\setminus A^*)$ (labels, flows, slacks) and, with $D = \mathrm{diag}(\nu)$, reads
--   $$M = \begin{pmatrix} \mathbb 1_s^\top & 0 & 0\\ 0 & B_{V\setminus\{s\}} & 0\\ -(B^+)^\top & D^{-1} & \mathrm{Id}_{\bullet, A'\setminus A^*}\\ -(B^-_{\bullet,A'\setminus A^*})^\top & D^{-1}_{A'\setminus A^*,\bullet} & \mathrm{Id}\end{pmatrix};$$
--   the right-hand side of (LCP) is $\ell'_0\mathbb 1_s + \nu'_0\mathbb 1_t$.
--   5. (p. 7.) The **normalization** $\pi : \mathbb R^V \to \mathbb R^V$ sets, along a topological order, $\pi_w(\ell') = \max\{\ell'_w, \min_{v \in N^-(w)} \pi_v(\ell')\}$ if $w \ne s$ and no resetting arc enters $w$, and $\pi_w(\ell') = \ell'_w$ otherwise.
--
--   These objects carry the paper's analysis: Theorem 6 identifies normalized thin flows with solutions of (LCP), and Theorem 31 counts the breakpoints of $\varrho^{G'}$.
--
--   **Formalization Note** "min" is encoded as `IsLeast` of the set of values $\varrho^a(\ell'_v, x'_a)$ over arcs entering $w$, so a vertex $w \ne s$ without entering arcs has no corresponding labels (in a shortest path graph there is none). $A^*$ is a `Finset`. Breakpoints are counted for the whole vector, and only at points $\nu'_0 > 0$ (the paper never defines the word; the base case of Theorem 31 and the border remark in the proof of Lemma 30 fix this reading). Values of a label function at $\nu'_0 < 0$ are unconstrained and never affect breakpoints. $\pi$ is computed by $|V|$ sweeps of the update starting from $\ell'$, which equals the topological-order recursion on an acyclic graph; the minimum over an empty set of in-neighbours would be $0$, which only concerns $s$ in a shortest path graph. $\ell$, $\nu'_0$, $\ell'_0$ are written `l`, `nu0`, `l0`.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, pp. 5–7, 11, Definition 4, Theorem 6 (matrix M, display (LCP)), definition of π (p. 7), definition of ϱ^{G′} (proof of Proposition 17)

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network
import Definitions.Def_ThinFlowSP_Breakpoints_LCP

noncomputable section

namespace ThinFlowSP.Breakpoints

/-- The label update `ϱ^a` along an arc `a = (v, w)` (Definition 4): given the label `lv` of the
tail and the flow `xa` on `a`, it is `xa / ν a` if `a` is resetting (`a ∈ A*`) and
`max lv (xa / ν a)` otherwise. -/
def rhoArc {G : Net} (Astar : Finset G.A) (ν : G.A → ℝ) (a : G.A) (lv xa : ℝ) : ℝ :=
  if a ∈ Astar then xa / ν a else max lv (xa / ν a)

/-- Definition 4: `l` are corresponding labels of the normalized thin `s`–`t`-flow with
resetting `x`. The labels are non-negative; for every `w ≠ s`, `l w` is the minimum of
`ϱ^a(l v, x a)` over the arcs `a = (v, w)` entering `w`; and `l w = ϱ^a(l v, x a)` on every arc
`a = (v, w)` carrying positive flow. (That `x` is a static flow is stated separately with
`IsStaticFlow`.) -/
def IsThinFlowLabels (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ) (x : G.A → ℝ)
    (l : G.V → ℝ) : Prop :=
  (∀ v, 0 ≤ l v) ∧
  (∀ w, w ≠ G.s →
    IsLeast {r | ∃ a, G.head a = w ∧ r = rhoArc Astar ν a (l (G.tail a)) (x a)} (l w)) ∧
  (∀ a, 0 < x a → l (G.head a) = rhoArc Astar ν a (l (G.tail a)) (x a))

/-- The defining property of the label function `ϱ^{G′}` (proof of Proposition 17, p. 11): for
every flow value `ν′₀ ≥ 0`, `ρ ν′₀` are the corresponding labels of some normalized thin
`s`–`t`-flow with resetting of value `ν′₀`, with label `1` at `s`. Values at `ν′₀ < 0` are
unconstrained. -/
def IsLabelFunction (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ) (ρ : ℝ → G.V → ℝ) : Prop :=
  ∀ nu0, 0 ≤ nu0 → ρ nu0 G.s = 1 ∧
    ∃ x : G.A → ℝ, IsStaticFlow G x nu0 ∧ IsThinFlowLabels G Astar ν x (ρ nu0)

/-- The property of the pair `(ϱ^{G′}, χ^{G′})` in Proposition 17: for every `ν′₀ ≥ 0`, `χ ν′₀`
is a normalized thin `s`–`t`-flow with resetting of value `ν′₀` and `ρ ν′₀` are corresponding
labels with label `1` at `s`. -/
def IsParametricThinFlow (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ) (ρ : ℝ → G.V → ℝ)
    (χ : ℝ → G.A → ℝ) : Prop :=
  ∀ nu0, 0 ≤ nu0 →
    IsStaticFlow G (χ nu0) nu0 ∧ IsThinFlowLabels G Astar ν (χ nu0) (ρ nu0) ∧ ρ nu0 G.s = 1

/-- The breakpoints of a vector-valued function `f` of one real variable on `(0, ∞)`: the
points `x > 0` such that on no open interval around `x` every component of `f` is affine. -/
def breakpoints {ι : Type} (f : ℝ → ι → ℝ) : Set ℝ :=
  {x | 0 < x ∧ ¬ ∃ ε > 0, ∃ m c : ι → ℝ,
    ∀ y ∈ Set.Ioo (x - ε) (x + ε), ∀ i, f y i = m i * y + c i}

/-- Index set `V ⊍ A′ ⊍ (A′ \ A*)` of the rows and columns of the matrix `M` of Theorem 6:
label variables `ℓ′_v`, flow variables `x′_a`, slack variables `y′_a` for non-resetting arcs. -/
abbrev Idx (G : Net) (Astar : Finset G.A) := G.V ⊕ (G.A ⊕ {a : G.A // a ∉ Astar})

/-- The matrix `M` of Theorem 6 (p. 5), with `D = diag(ν)`:
* row `s` of the `V`-block is `𝟙_sᵀ` on the label block;
* row `v ≠ s` of the `V`-block is the incidence row `B_{v,·}` on the flow block;
* row `a ∈ A′` is `-(B⁺)ᵀ` on the label block, `D⁻¹` on the flow block and `Id_{·,A′∖A*}` on
  the slack block;
* row `a ∈ A′ ∖ A*` is `-(B⁻_{·,A′∖A*})ᵀ` on the label block, `D⁻¹_{A′∖A*,·}` on the flow block
  and `Id` on the slack block. -/
def lcpMatrix (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ) :
    Matrix (Idx G Astar) (Idx G Astar) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | Sum.inl v, Sum.inl w => if v = G.s ∧ w = G.s then 1 else 0
    | Sum.inl v, Sum.inr (Sum.inl a) => if v = G.s then 0 else incidence G v a
    | Sum.inl _, Sum.inr (Sum.inr _) => 0
    | Sum.inr (Sum.inl a), Sum.inl w => -incPos G w a
    | Sum.inr (Sum.inl a), Sum.inr (Sum.inl b) => if a = b then 1 / ν a else 0
    | Sum.inr (Sum.inl a), Sum.inr (Sum.inr b) => if a = b.1 then 1 else 0
    | Sum.inr (Sum.inr b), Sum.inl w => -incNeg G w b.1
    | Sum.inr (Sum.inr b), Sum.inr (Sum.inl a) => if b.1 = a then 1 / ν a else 0
    | Sum.inr (Sum.inr b), Sum.inr (Sum.inr c) => if b = c then 1 else 0

/-- The right-hand side `ℓ′₀ 𝟙_s + ν′₀ 𝟙_t` of (LCP). -/
def lcpRhs (G : Net) (Astar : Finset G.A) (nu0 l0 : ℝ) : Idx G Astar → ℝ :=
  Sum.elim (fun v => (if v = G.s then l0 else 0) + (if v = G.t then nu0 else 0)) 0

/-- One sweep of the normalization `π` (p. 7): at every `w ≠ s` with no resetting arc entering
it, take `max (l w) (min over the arcs a = (v, w) of p v)`; elsewhere keep `l w`. (The minimum
over an empty arc set would be `0`; in a shortest path graph only `s` has no entering arc.) -/
def normStep (G : Net) (Astar : Finset G.A) (l p : G.V → ℝ) : G.V → ℝ := fun w =>
  if w ≠ G.s ∧ ∀ a, G.head a = w → a ∉ Astar then
    max (l w) (⨅ a : {a : G.A // G.head a = w}, p (G.tail a.1))
  else l w

/-- The normalization function `π : ℝ^V → ℝ^V` (p. 7), computed by `|V|` sweeps of `normStep`
starting from `l`; on an acyclic graph this equals the recursion along a topological order. -/
def normalize (G : Net) (Astar : Finset G.A) (l : G.V → ℝ) : G.V → ℝ :=
  (normStep G Astar l)^[Fintype.card G.V] l

end ThinFlowSP.Breakpoints


