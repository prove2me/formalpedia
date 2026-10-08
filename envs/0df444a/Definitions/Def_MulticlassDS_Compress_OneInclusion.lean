-- Prove2me | Definitions.Def_MulticlassDS_Compress_OneInclusion
-- name    : MulticlassDS_Compress_OneInclusion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:03:21.490919+00:00
-- url     : https://prove2.me/theorems/fba6ca9c-5ccb-4930-9511-489b3671bbb5
-- title:
--   Definitions 9, 11, displays (2)–(3), Algorithms 1–3, pp. 8–21 — one-inclusion graph orientations, out-degree, the one-inclusion and list learners
-- statement:
--   **One-inclusion graph** (Definition 9). For $V \subseteq \mathcal Y^m$ the one-inclusion graph $\mathcal G(V)$ has vertex set $V$; for each direction $i \in [m]$ and each $f : [m]\setminus\{i\} \to \mathcal Y$ the set $e_{i,f}$ of words of $V$ agreeing with $f$ off $i$ is, when non-empty, an edge $(e_{i,f}, i)$. Every vertex lies in exactly one edge of each direction.
--
--   **Orientations and out-degree** (Definition 11, displays (2)–(3)). An *orientation* $\sigma$ assigns to every edge $e$ a vertex $\sigma(e) \in e$. The out-degree of $v$ is
--   $$\operatorname{outdeg}(v;\sigma) = |\{e : v \in e,\ \sigma(e) \neq v\}|,$$
--   and the maximum out-degree is $\operatorname{outdeg}(\sigma) = \sup_{v\in V}\operatorname{outdeg}(v;\sigma)$.
--
--   **The one-inclusion algorithm** (Algorithm 1, p. 10; Algorithm 3, p. 21). Given a sample $S = ((x_1,y_1),\dots,(x_n,y_n))$ and a point $x$, consider the class $V = \mathcal H|_{(x_1,\dots,x_n,x)} \subseteq \mathcal Y^{n+1}$ (for Algorithm 3, its subclass $\mathcal H'$ of words $h$ with $h(i)\in\mu(x_i)$ and $h(n+1)\in\mu(x)$), take an orientation $\sigma$ of $\mathcal G(V)$ minimizing the maximum out-degree, let $e$ be the edge of direction $n+1$ consisting of the words with $h(i) = y_i$ for $i \in [n]$, and predict $h_S(x) = \sigma((e,n+1))(n+1)$.
--
--   **The list learner** (Algorithm 2, p. 20). For $\mathcal H$ with $d_{DS}(\mathcal H) = d$ and $t\in\mathbb N$, on $S \in (\mathcal X\times\mathcal Y)^{d+t}$ it outputs the menu $\mu_S(x) = \{h_{S_1}(x),\dots,h_{S_p}(x)\}$, where $S_1,\dots,S_p$ are the $p = \binom{d+t}{t}$ subsamples of $S$ of size $d$ and $h_{S_j}$ is the one-inclusion prediction on $S_j$.
--
--   These are the learners whose guarantees (Claim 16, Propositions 32 and 34) lead to the sample compression scheme of Theorem 36.
--
--   **Formalization Note** An orientation of $\mathcal G(V)$, $V \subseteq$ `Fin m → Y`, is encoded by the map $(i, v) \mapsto \sigma(e)$, where $e$ is the edge of direction $i$ through $v$; it must land in $V$, in that edge, and depend only on the edge. The out-degree of $v$ counts the directions $i$ with $\sigma(e) \neq v$, which is display (2). A bound on the maximum out-degree is written as a bound on every vertex's out-degree. The choice in step 2 of Algorithms 1 and 3 is a parameter `OIGChoice`: one minimizing orientation per sequence of points, chosen **permutation-equivariantly** (reordering the points reorders the orientation). This is the reading under which the paper's leave-one-out proofs (Claim 16, Propositions 32, 34) are valid, since they use one orientation of $\mathcal G(\mathcal H|_{(x'_1,\dots,x'_{n+1})})$ for all $n+1$ reorderings; statements about the learners hold for every such choice. When the edge $e$ is empty (non-realizable input) the prediction is an arbitrary default label, which requires $\mathcal Y$ non-empty. Subsamples of size $d$ in Algorithm 2 are the order-preserving selections `Fin d ↪o Fin (d+t)`, $\binom{d+t}{d} = \binom{d+t}{t}$ of them.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 8 Definition 9 (display (1)), p. 9 Definition 11 and displays (2), (3), p. 10 Algorithm 1, p. 20 Algorithm 2, p. 21 Algorithm 3

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions

namespace MulticlassDS.Compress

/-- `u` and `v` agree on `[m] ∖ {i}`: they lie in the same edge of direction `i` of the
one-inclusion graph (Definition 9, p. 8). -/
def AgreeOff {Y : Type*} {m : ℕ} (i : Fin m) (u v : Fin m → Y) : Prop :=
  ∀ j, j ≠ i → u j = v j

/-- Definition 11, p. 9: an orientation of the one-inclusion graph `G(V)` of `V ⊆ Y^m`
(Definition 9, p. 8). Each vertex lies in exactly one edge of each direction `i`, so the
orientation is given as the map `(i, v) ↦` the vertex `σ(e)` that the edge of direction `i`
through `v` points to: it lies in `V` and in that edge, and depends only on the edge. -/
structure Orientation {Y : Type*} {m : ℕ} (V : Set (Fin m → Y)) where
  /-- `toFun i v` is the head `σ(e)` of the edge `e` of direction `i` containing `v`. -/
  toFun : Fin m → (Fin m → Y) → (Fin m → Y)
  mem : ∀ i, ∀ v ∈ V, toFun i v ∈ V
  agree : ∀ i, ∀ v ∈ V, AgreeOff i (toFun i v) v
  wd : ∀ i, ∀ u ∈ V, ∀ v ∈ V, AgreeOff i u v → toFun i u = toFun i v

/-- Display (2), p. 9: the out-degree `outdeg(v; σ)`, the number of edges containing `v`
that `σ` does not orient to `v`. -/
noncomputable def outdeg {Y : Type*} {m : ℕ} {V : Set (Fin m → Y)} (σ : Orientation V)
    (v : Fin m → Y) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => σ.toFun i v ≠ v).card

/-- A permutation-equivariant choice of orientations minimizing the maximum out-degree, for a
family of classes `V m xs ⊆ Y^m` indexed by unlabelled sequences `xs ∈ X^m` (step 2 of
Algorithms 1 and 3, pp. 10, 21). `minimal`: `σ xs` minimizes the maximum out-degree (3) of
`G(V m xs)`. `equivariant`: reordering the points of `xs` by `π` reorders the chosen
orientation accordingly, so all leave-one-out runs on the same `n + 1` points use one
orientation (as the proofs of Claim 16 and Propositions 32, 34 require). -/
structure OIGChoice {X Y : Type*} (V : ∀ m : ℕ, (Fin m → X) → Set (Fin m → Y)) where
  σ : ∀ {m : ℕ} (xs : Fin m → X), Orientation (V m xs)
  minimal : ∀ {m : ℕ} (xs : Fin m → X) (τ : Orientation (V m xs)) (k : ℕ),
    (∀ v ∈ V m xs, outdeg τ v ≤ k) → ∀ v ∈ V m xs, outdeg (σ xs) v ≤ k
  equivariant : ∀ {m : ℕ} (xs : Fin m → X) (π : Equiv.Perm (Fin m)) (i : Fin m),
    ∀ v ∈ V m xs, (σ (xs ∘ π)).toFun (π.symm i) (v ∘ π) = (σ xs).toFun i v ∘ π

/-- Algorithm 1, p. 10, step 1: the class `H|_{xs}` on which the one-inclusion algorithm `A_H`
works. -/
def projFamily {X Y : Type*} (H : Set (X → Y)) : ∀ m : ℕ, (Fin m → X) → Set (Fin m → Y) :=
  fun _ xs => proj H xs

/-- Algorithm 3, p. 21, step 1: the class `H' = {h ∈ H|_{xs} : h(i) ∈ μ(xs i) ∀ i}` on which
the one-inclusion algorithm `A_{H,μ}` works. -/
def menuFamily {X Y : Type*} (H : Set (X → Y)) (μ : X → Set Y) :
    ∀ m : ℕ, (Fin m → X) → Set (Fin m → Y) :=
  fun _ xs => {v ∈ proj H xs | ∀ i, v i ∈ μ (xs i)}

/-- Algorithms 1 and 3, pp. 10, 21: the one-inclusion prediction `h_S(x)`. With
`xs = (x₁, …, xₙ, x)`, take the edge `e` of direction `n + 1` of `G(V (n+1) xs)` defined by the
labels of `S`; if it is non-empty, return the `(n+1)`-st label of the vertex `σ((e, n + 1))`
chosen by `C`. If `e` is empty (`S` is not realizable) a default label is returned. -/
noncomputable def oigPredict {X Y : Type*} [Nonempty Y]
    {V : ∀ m : ℕ, (Fin m → X) → Set (Fin m → Y)} (C : OIGChoice V) {n : ℕ}
    (S : Fin n → X × Y) (x : X) : Y := by
  classical
  exact
    if h : ∃ v ∈ V (n + 1) (Fin.snoc (fun i => (S i).1) x),
        ∀ i : Fin n, v i.castSucc = (S i).2 then
      (C.σ (Fin.snoc (fun i => (S i).1) x)).toFun (Fin.last n) h.choose (Fin.last n)
    else Classical.arbitrary Y

/-- Algorithm 2, p. 20: the list learner `L_{H,t}`. On `S ∈ (X × Y)^{d+t}` it returns the menu
`μ_S(x) = {h_{S₁}(x), …, h_{S_p}(x)}`, where `S₁, …, S_p` are the `p = C(d+t, t)` subsamples of
`S` of size `d` (as order-preserving selections) and `h_{S_j}` is the one-inclusion prediction. -/
noncomputable def listMenu {X Y : Type*} [Nonempty Y]
    {V : ∀ m : ℕ, (Fin m → X) → Set (Fin m → Y)} (C : OIGChoice V) (d t : ℕ)
    (S : Fin (d + t) → X × Y) (x : X) : Set Y :=
  Set.range fun ι : Fin d ↪o Fin (d + t) => oigPredict C (fun j => S (ι j)) x

end MulticlassDS.Compress


