-- Prove2me | Definitions.Def_TopicalIrreducibility_Relations_Irreducibility
-- name    : TopicalIrreducibility_Relations_Irreducibility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:29.411005+00:00
-- url     : https://prove2.me/theorems/b9db260a-3840-4af5-b916-bf51c7665589
-- title:
--   Eq. (2.1), Definitions 2.1–2.3 — faces, the graph $G(f)$, facial and graphical irreducibility, indecomposability
-- statement:
--   Let $f:\mathbb R^n_{\ge0}\to\mathbb R^n_{\ge0}$ and write $[n]=\{1,\dots,n\}$. For $J\subseteq[n]$:
--
--   1. The closed **face** is $F_J=\{x\in\mathbb R^n_{\ge0}: x_i=0\text{ for all }i\notin J\}$ (Eq. (2.1)). It is **proper** if $J\ne[n]$ and **nontrivial** if $J\neq\emptyset$.
--   2. The **indicator vector** $e_J$ has $(e_J)_i=1$ for $i\in J$ and $0$ otherwise; $\mathbf 1=e_{[n]}$.
--
--   **Definition 2.1.** $f$ is **facially irreducible** if there is no nonempty proper $J$ with $f(F_J)\subseteq F_J$.
--
--   **Graph.** $G(f)$ has nodes $[n]$ and an arc from $i$ to $j$ iff
--   $$
--   \lim_{t\to\infty} f(\mathbf 1+t e_{\{j\}})_i=\infty .
--   $$
--
--   **Definition 2.2.** $f$ is **graphically irreducible** if $G(f)$ is strongly connected: for all nodes $i,j$ there is a directed path from $i$ to $j$.
--
--   **Definition 2.3.** $f$ is **decomposable** if there is a nonempty proper $J\subset[n]$ with $\lim_{t\to\infty}f(\mathbf 1+te_J)_i<\infty$ for every $i\in[n]\setminus J$, and **indecomposable** if it is not decomposable.
--
--   These are the three irreducibility notions whose relations are the subject of Theorem 2.4.
--
--   **Formalization Note** Subsets of $[n]$ are `Finset (Fin n)`. The statement "$\lim_{t\to\infty}f(\mathbf 1+te_J)_i=\infty$" is `Tendsto (fun t => f (1 + t • e_J) i) atTop atTop` over $t\in[0,\infty)$; "$<\infty$" is encoded by a finite bound $B_i\ge0$ for the entire ray, separately for each $i$. For an order-preserving $f$ the ray $t\mapsto f(\mathbf 1+te_J)_i$ is nondecreasing, so its limit exists in $[0,\infty]$ and is finite exactly when the ray is bounded above; all theorems using these predicates assume $f$ m-topical. Strong connectivity is reachability by a possibly empty directed path (`Relation.ReflTransGen`), so a single node is strongly connected. The predicates are stated for any map $f$; the source applies them to m-topical maps only.
-- source:
--   Brian Lins, Irreducibility for Topical Maps, STOC 2027 submission #201 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/201.pdf, p. 4, Eq. (2.1), Definitions 2.1, 2.2 (with the graph G(f) defined before it), 2.3; PDF page = printed page

import Mathlib
import Definitions.Def_TopicalIrreducibility_Relations_MTopical

open scoped NNReal
open Filter

namespace TopicalIrreducibility.Relations

/-- The closed face `F_J = {x ∈ ℝⁿ_{≥0} : xᵢ = 0 for all i ∉ J}`, Eq. (2.1). -/
def face {n : ℕ} (J : Finset (Fin n)) : Set (StdCone n) :=
  {x | ∀ i, i ∉ J → x i = 0}

/-- A subset `J ⊆ [n]` is nontrivial (`J ≠ ∅`) and proper (`J ≠ [n]`). -/
def IsNontrivialProper {n : ℕ} (J : Finset (Fin n)) : Prop :=
  J.Nonempty ∧ J ≠ Finset.univ

/-- Definition 2.1: `f` is facially irreducible if it leaves no nontrivial proper closed face
invariant, i.e. for no nonempty proper `J` is `f (F_J) ⊆ F_J`. -/
def FaciallyIrreducible {n : ℕ} (f : StdCone n → StdCone n) : Prop :=
  ∀ J : Finset (Fin n), IsNontrivialProper J → ¬ Set.MapsTo f (face J) (face J)

/-- The indicator vector `e_J`: `(e_J)ᵢ = 1` if `i ∈ J` and `0` otherwise. -/
def indicatorVec {n : ℕ} (J : Finset (Fin n)) : StdCone n :=
  fun i => if i ∈ J then 1 else 0

/-- `lim_{t → ∞} f(1 + t e_J)ᵢ = ∞`, with `t` ranging over the nonnegative reals. -/
def RayUnbounded {n : ℕ} (f : StdCone n → StdCone n) (J : Finset (Fin n)) (i : Fin n) :
    Prop :=
  Tendsto (fun t : ℝ≥0 => f (1 + t • indicatorVec J) i) atTop atTop

/-- The graph `G(f)` (p. 4): nodes `[n]`, with an arc from `i` to `j` iff
`lim_{t → ∞} f(1 + t e_{j})ᵢ = ∞`. -/
def graphArc {n : ℕ} (f : StdCone n → StdCone n) (i j : Fin n) : Prop :=
  RayUnbounded f {j} i

/-- Definition 2.2: `f` is graphically irreducible if `G(f)` is strongly connected: every node
reaches every node by a (possibly empty) directed path of arcs. -/
def GraphicallyIrreducible {n : ℕ} (f : StdCone n → StdCone n) : Prop :=
  ∀ i j : Fin n, Relation.ReflTransGen (graphArc f) i j

/-- Definition 2.3: `f` is decomposable if there is a nonempty proper `J ⊂ [n]` with
`lim_{t → ∞} f(1 + t e_J)ᵢ < ∞` for every `i ∉ J`. For an order-preserving `f` the ray
`t ↦ f(1 + t e_J)ᵢ` is monotone, so its limit exists in `[0, ∞]` and is finite exactly when
the entire nonnegative-real ray has a finite upper bound. Each coordinate has its own bound. -/
def Decomposable {n : ℕ} (f : StdCone n → StdCone n) : Prop :=
  ∃ J : Finset (Fin n), IsNontrivialProper J ∧
    ∀ i, i ∉ J → ∃ B : ℝ≥0, ∀ t : ℝ≥0, f (1 + t • indicatorVec J) i ≤ B

/-- Definition 2.3: `f` is indecomposable if it is not decomposable. -/
def Indecomposable {n : ℕ} (f : StdCone n → StdCone n) : Prop :=
  ¬ Decomposable f

end TopicalIrreducibility.Relations


