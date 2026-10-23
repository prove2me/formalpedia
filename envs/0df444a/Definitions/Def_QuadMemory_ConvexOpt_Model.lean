-- Prove2me | Definitions.Def_QuadMemory_ConvexOpt_Model
-- name    : QuadMemory_ConvexOpt_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:20.780928+00:00
-- url     : https://prove2.me/theorems/466f8321-bb65-4ca1-86d9-7529cc160883
-- title:
--   Definition 3 and §2, p. 5 — M-bit memory-constrained deterministic first-order algorithms, their run against a subgradient oracle, and ε-minimization over the unit ball within Q queries
-- statement:
--   This module fixes the model of computation of Theorem 1 of Blanchard, Zhang and Jaillet.
--
--   1. **Space.** $\mathbb R^d$ carries the Euclidean norm; $B_d(0,1)$ is the closed unit ball.
--   2. **Algorithms (Definition 3).** An $M$-bit memory-constrained deterministic algorithm is given by a query function $\psi_{query}:\{0,1\}^M\to B_d(0,1)$, an update function $\psi_{update}:\{0,1\}^M\times\mathbb R^d\times(\mathbb R\times\mathbb R^d)\to\{0,1\}^M$, and a stopping rule $\mathrm{halt}:\{0,1\}^M\to\{\mathrm{true},\mathrm{false}\}$. It starts from $\mathsf{Memory}_0=0^M$; at iteration $t\ge1$ it queries $q_t=\psi_{query}(\mathsf{Memory}_{t-1})$, receives $r_t=\mathcal O(q_t)$ and sets $\mathsf{Memory}_t=\psi_{update}(\mathsf{Memory}_{t-1},q_t,r_t)$.
--   3. **Instances.** An instance is a pair $(f,g)$ with $f:\mathbb R^d\to\mathbb R$ convex and $1$-Lipschitz and $g$ a subgradient selection of $f$: $f(x)+\langle g(x),y-x\rangle\le f(y)$ for all $x,y$. The first-order oracle answers a query $x$ with $(f(x),g(x))$.
--   4. **Solving.** The algorithm solves convex optimization to accuracy $\varepsilon$ with at most $Q$ queries if, on every instance, there is a time $T$ with $1\le T\le Q$ at which it stops for the first time (the stopping rule holds for $\mathsf{Memory}_T$ and for no $\mathsf{Memory}_s$, $1\le s<T$), and its final output, the last query $\tilde x=q_T$, satisfies
--   $$f(\tilde x)\le f(y)+\varepsilon\qquad\text{for every }y\in B_d(0,1),$$
--   that is, $f(\tilde x)\le\min_{B_d(0,1)}f+\varepsilon$.
--
--   These are the objects of the goal theorem; nothing else of the paper's proof enters it.
--
--   **Formalization Note.** Memory is `Fin M → Bool`, and the run is `memAt`: `memAt 0` is the all-false memory and the $t$-th query is `alg.query (memAt (t-1))`. The paper lets the algorithm "stop making queries at any iteration", with the last query as output; here this is the stopping rule, read on the memory after each update. Queries are restricted to the unit ball, while the paper's oracle accepts any point of $\mathbb R^d$: the paper's proof (Proposition 8) uses $\|x_t\|\le1$. This narrows the class of algorithms. The paper only asks that $\partial f(x)$ be a subgradient at each query point; requiring it at every point is the same, since every convex function on $\mathbb R^d$ has a subgradient everywhere and the algorithm only sees $g$ at its queries. Accuracy is written pointwise against every point of the ball, so no infimum is involved.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 5, Definition 3, the sentence after it, and the paragraph 'Convex optimization' of §2

import Mathlib

open scoped RealInnerProductSpace

namespace QuadMemory.ConvexOpt

/-- The Euclidean space `ℝ^d`, with the `ℓ₂` norm and the standard inner product. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A memory state of `M` bits, an element of `{0,1}^M` (Definition 3, p. 5). -/
abbrev State (M : ℕ) := Fin M → Bool

/-- An `M`-bit memory-constrained deterministic first-order algorithm in dimension `d`
(Blanchard–Zhang–Jaillet, arXiv:2302.04963v2, p. 5, Definition 3 and the sentence after it).

* `query s` is the query `ψ_query(s)` made from memory `s`; it lies in the closed unit ball.
* `update s q r` is the new memory `ψ_update(s, q, r)` after query `q` received response
  `r = (f(q), ∂f(q)) ∈ ℝ × ℝ^d`.
* `halt s` says that the algorithm stops after an update that produced memory `s`
  ("the algorithm can stop making queries at any iteration").

The maps are time-invariant, as in Definition 3. -/
structure MemAlg (d M : ℕ) where
  /-- the query function `ψ_query : {0,1}^M → B_d(0,1)` -/
  query : State M → E d
  /-- queries lie in the closed unit ball -/
  query_mem : ∀ s, query s ∈ Metric.closedBall (0 : E d) 1
  /-- the update function `ψ_update : {0,1}^M × ℝ^d × (ℝ × ℝ^d) → {0,1}^M` -/
  update : State M → E d → ℝ × E d → State M
  /-- the stopping rule, read on the memory after each update -/
  halt : State M → Bool

/-- An instance of convex optimization over the unit ball (p. 5): `f : ℝ^d → ℝ` is convex and
`1`-Lipschitz, and `g` is a subgradient selection for `f`: `g x` is a subgradient of `f` at every
point `x`. The first-order oracle answers a query `x` with `(f x, g x)`. -/
def IsCOInstance {d : ℕ} (f : E d → ℝ) (g : E d → E d) : Prop :=
  ConvexOn ℝ Set.univ f ∧ LipschitzWith 1 f ∧ ∀ x y : E d, f x + ⟪g x, y - x⟫ ≤ f y

/-- The memory of `alg` run against the first-order oracle `x ↦ (f x, g x)`:
`memAt alg f g 0 = 0^M`, and `memAt alg f g t` is the memory after the `t`-th query.
The `t`-th query (`t ≥ 1`) is `alg.query (memAt alg f g (t - 1))`. -/
def memAt {d M : ℕ} (alg : MemAlg d M) (f : E d → ℝ) (g : E d → E d) : ℕ → State M
  | 0 => fun _ => false
  | t + 1 =>
      alg.update (memAt alg f g t) (alg.query (memAt alg f g t))
        (f (alg.query (memAt alg f g t)), g (alg.query (memAt alg f g t)))

/-- `alg` minimizes every `1`-Lipschitz convex function over the unit ball to accuracy `ε` with at
most `Q` queries (p. 5): on every instance `(f, g)` the run stops at a time `T` with `1 ≤ T ≤ Q`
(the first time `t ≥ 1` at which `halt` holds), and its output, the last query
`x̃ = alg.query (memAt alg f g (T - 1))`, satisfies `f x̃ ≤ f y + ε` for every `y` in the unit
ball. -/
def SolvesCO {d M : ℕ} (alg : MemAlg d M) (Q : ℕ) (ε : ℝ) : Prop :=
  ∀ (f : E d → ℝ) (g : E d → E d), IsCOInstance f g →
    ∃ T : ℕ, 1 ≤ T ∧ T ≤ Q ∧ alg.halt (memAt alg f g T) = true ∧
      (∀ s : ℕ, 1 ≤ s → s < T → alg.halt (memAt alg f g s) = false) ∧
      ∀ y ∈ Metric.closedBall (0 : E d) 1, f (alg.query (memAt alg f g (T - 1))) ≤ f y + ε

end QuadMemory.ConvexOpt


