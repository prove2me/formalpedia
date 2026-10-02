-- Prove2me | Definitions.Def_ShorNonsmooth_RAlgorithm_RAlgorithm
-- name    : ShorNonsmooth_RAlgorithm_RAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:12:31.672795+00:00
-- url     : https://prove2.me/theorems/91485211-0b2a-4b0a-803c-b1a3aafc68d6
-- title:
--   The class $K$ of piecewise smooth functions, $G_f(x)$, $\bar P_{\delta,\varepsilon}(x)$ and runs of the $r_\mu(\alpha)$-algorithm
-- statement:
--   1. **The class $K$.** Let $E_n$ be partitioned into $m$ closed sets $\bar D_1, \dots, \bar D_m$, each the closure of its interior $D_i$, whose interiors $D_i$ are mutually disjoint and each homeomorphic to an open ball or to an open halfspace. Let $f_i$ be continuous, continuously differentiable functions defined on open sets $D_i^+ \supset \bar D_i$. A function $f$ belongs to $K$ (is formed from the $f_i$ on the $\bar D_i$) if
--
--      (a) $f(x) = f_i(x)$ for all $x \in D_i$, and
--
--      (b) $f(x) = f_i(x) = f_j(x)$ for all $x \in \bar D_i \cap \bar D_j$.
--
--      For such $f$ the set of almost-gradients at $x$ is the set of gradients of the incident pieces,
--   $$
--   G_f(x) = \{\, \nabla f_i(x) : x \in \bar D_i \,\},
--   $$
--      a single vector inside a piece and $\{\nabla f_{i_1}(x), \dots, \nabla f_{i_k}(x)\}$ on a common boundary of pieces $i_1, \dots, i_k$.
--
--   2. **The set $\bar P_{\delta,\varepsilon}(x)$.** For $\delta, \varepsilon > 0$, $\bar P_{\delta,\varepsilon}(x)$ is the closed convex hull of
--   $$
--   P_{\delta,\varepsilon}(x) = \Big(\bigcup_{y \in S_\delta(x)} G_f(y)\Big) \cup \Big(\bigcup_{z \in G_f(x)} S_\varepsilon(z)\Big),
--   $$
--      where $S_r(c)$ is the open ball of radius $r$ centred at $c$.
--
--   3. **The $r_\mu(\alpha)$-algorithm.** Fix $\alpha > 1$, $0 \le \mu < 1$ and $\beta = 1/\alpha$. Start from any $x_0 \in E_n$, $\tilde g_0 = 0$ and a nonsingular operator $B_0$. On iteration $k + 1$ ($k = 0, 1, \dots$), from $x_k$, $\tilde g_k$, $B_k$:
--
--      (1) choose $g_f(x_k) \in G_f(x_k)$ with $(B_k^* g_f(x_k), \tilde g_k) \le \mu \|B_k^* g_f(x_k)\|\,\|\tilde g_k\|$ and put $g_k^* = B_k^* g_f(x_k)$;
--
--      (2) $r_k = g_k^* - \tilde g_k$ (required to be nonzero, so that (3) is defined);
--
--      (3) $\xi_{k+1} = r_k / \|r_k\|$;
--
--      (4) $B_{k+1} = B_k R_\beta(\xi_{k+1})$;
--
--      (5) $\tilde g_{k+1} = R_\beta(\xi_{k+1})\, g_k^*$;
--
--      (6) $x_{k+1} = x_k - h_{k+1} B_{k+1} \tilde g_{k+1}$ (3.48), where $h_{k+1} \ge 0$ is such that (a) $\psi(h) = f(x_k - h B_{k+1}\tilde g_{k+1})$ is nonincreasing on $[0, h_{k+1}]$ and (b) some $g \in G_f(x_{k+1})$ satisfies $(B_{k+1}^* g, \tilde g_{k+1}) \le \mu \|B_{k+1}^* g\|\,\|\tilde g_{k+1}\|$ (3.49).
--
--      A run is any family of sequences $x_k, \tilde g_k, B_k, g_f(x_k), h_{k+1}$ obeying these rules. The $r(\alpha)$-algorithm is the case $\mu = 0$.
--
--   The class $K$ is the setting of the convergence theory of Section 3.7; the run predicate quantifies over every admissible choice of almost-gradients and stepsizes, not over one particular line search.
--
--   **Formalization Note** $B_k^*$ is the adjoint `ContinuousLinearMap.adjoint (B k)`, and $B_0$ is nonsingular as a unit of the operator monoid. The book's step (b) supplies the almost-gradient used in step (1) of the next iteration, so it is encoded as the condition of step (1) at index $k + 1$. The book writes the segment $[0; h_{k+1}]$, so $h_{k+1} \ge 0$ is required. $G_f(x)$ is taken relative to the chosen pieces $(\bar D_i, f_i)$, as the book does on p. 79; theorems quantify over the representation together with $f$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 78, the $r_\mu(\alpha)$-algorithm, steps (1)–(7), (3.48)–(3.49); p. 79, the class $K$ and $G_f(x)$ for $f \in K$; p. 82, $\bar P_{\delta,\varepsilon}(x)$ and the $r(\alpha)$-algorithm ($\mu = 0$)

import Mathlib
import Definitions.Def_ShorNonsmooth_RAlgorithm_Widths

open scoped InnerProductSpace

namespace ShorNonsmooth.RAlgorithm

/-- Shor (1985), p. 79: the data from which a function of the **class `K`** is formed.
A partition of `E_n` into `m` closed sets `D̄₁, …, D̄_m` (`D i`), each the closure of its
interior `D_i`, whose interiors `D_i` are homeomorphic to an open ball ("open sphere") or to an open halfspace and are mutually disjoint,
together with continuous, continuously differentiable functions `f_i` (`fi i`) defined on open
sets `D_i⁺ ⊃ D̄_i` (`U i`). The values of `fi i` outside `U i` play no role. -/
structure KRep (n : ℕ) where
  /-- the number `m` of pieces -/
  m : ℕ
  /-- the closed pieces `D̄_i` -/
  D : Fin m → Set (EuclideanSpace ℝ (Fin n))
  isClosed_D : ∀ i, IsClosed (D i)
  /-- `D̄_i` is the closure of its interior `D_i` (the book's bar notation) -/
  closure_interior_D : ∀ i, closure (interior (D i)) = D i
  /-- the pieces cover `E_n` -/
  iUnion_D : (⋃ i, D i) = Set.univ
  /-- the interiors `D_i` are mutually disjoint -/
  disjoint_interior : Pairwise fun i j => Disjoint (interior (D i)) (interior (D j))
  /-- each interior `D_i` is homeomorphic to an open ball or to an open halfspace -/
  interior_homeomorph : ∀ i,
    Nonempty (interior (D i) ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ∨
      ∃ a : EuclideanSpace ℝ (Fin n), a ≠ 0 ∧
        Nonempty (interior (D i) ≃ₜ {x : EuclideanSpace ℝ (Fin n) | 0 < ⟪a, x⟫_ℝ})
  /-- the smooth pieces `f_i` -/
  fi : Fin m → EuclideanSpace ℝ (Fin n) → ℝ
  /-- the open domains `D_i⁺` of the `f_i` -/
  U : Fin m → Set (EuclideanSpace ℝ (Fin n))
  isOpen_U : ∀ i, IsOpen (U i)
  D_subset_U : ∀ i, D i ⊆ U i
  /-- `f_i` is continuous and continuously differentiable on `D_i⁺` -/
  contDiffOn_fi : ∀ i, ContDiffOn ℝ 1 (fi i) (U i)

namespace KRep

variable {n : ℕ}

/-- Shor (1985), p. 79: `f ∈ K` is formed from the functions `f_i` on `D̄_i`:
(a) `f(x) = f_i(x)` for all `x ∈ D_i`, (b) `f(x) = f_i(x) = f_j(x)` for all `x ∈ D̄_i ∩ D̄_j`. -/
def Forms (P : KRep n) (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ i, ∀ x ∈ interior (P.D i), f x = P.fi i x) ∧
    (∀ i j, ∀ x ∈ P.D i ∩ P.D j, f x = P.fi i x ∧ f x = P.fi j x)

/-- Shor (1985), p. 79: for `f ∈ K`, the set of almost-gradients `G_f(x)` consists of the gradients
`g_{f_i}(x)` of the pieces `f_i` with `x ∈ D̄_i` (one gradient in the interior of a piece,
`{g_{f_{i₁}}(x), …, g_{f_{i_k}}(x)}` on a common boundary of pieces `i₁, …, i_k`). -/
def Gf (P : KRep n) (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {g | ∃ i, x ∈ P.D i ∧ g = gradient (P.fi i) x}

/-- Shor (1985), p. 82: `P̄_{δ,ε}(x)`, the convex closure of
`P_{δ,ε}(x) = (⋃_{y ∈ S_δ(x)} G_f(y)) ∪ (⋃_{z ∈ G_f(x)} S_ε(z))`, with `S_r(c)` the open ball of
radius `r` centred at `c`. -/
noncomputable def Pbar (P : KRep n) (δ ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  closedConvexHull ℝ ((⋃ y ∈ Metric.ball x δ, P.Gf y) ∪ (⋃ z ∈ P.Gf x, Metric.ball z ε))

end KRep

/-- The unit vector `v / ‖v‖`. -/
noncomputable def unitDir {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ‖v‖⁻¹ • v

/-- Shor (1985), p. 78, steps (1)–(7): the sequences `x_k`, `g̃_k`, `B_k`, the almost-gradients
`g_k = g_f(x_k)` chosen in step (1), and the stepsizes `h_{k+1}` form a run of the
**`r_μ(α)`-algorithm** applied to `f ∈ K` (formed from `P`). With `β = 1/α`, `A_k = B_k⁻¹`:

* `g̃₀ = 0` and `B₀` is nonsingular (`x₀` arbitrary);
* (1) `g_k ∈ G_f(x_k)` with `(B_k* g_k, g̃_k) ≤ μ ‖B_k* g_k‖ ‖g̃_k‖`, and `g_k* = B_k* g_k`;
* (2) `r_k = g_k* - g̃_k`, which must be nonzero for (3) to be defined;
* (3) `ξ_{k+1} = r_k / ‖r_k‖`;
* (4) `B_{k+1} = B_k R_β(ξ_{k+1})`;
* (5) `g̃_{k+1} = R_β(ξ_{k+1}) g_k*`;
* (6) `x_{k+1} = x_k - h_{k+1} B_{k+1} g̃_{k+1}` (3.48) with `h_{k+1} ≥ 0` such that
  (a) `ψ(h) = f(x_k - h B_{k+1} g̃_{k+1})` is nonincreasing on `[0, h_{k+1}]`, and
  (b) some `g ∈ G_f(x_{k+1})` satisfies (3.49); the book uses that `g` in step (1) of the next
  iteration, so (b) is the condition of step (1) at index `k + 1` and is encoded by `g_mem`,
  `g_angle` there.

The adjoint `B_k*` is `ContinuousLinearMap.adjoint (B k)`. -/
structure IsRun {n : ℕ} (P : KRep n) (f : EuclideanSpace ℝ (Fin n) → ℝ) (α μ : ℝ)
    (x gt g : ℕ → EuclideanSpace ℝ (Fin n))
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ) : Prop where
  gt_zero : gt 0 = 0
  isUnit_B_zero : IsUnit (B 0)
  g_mem : ∀ k, g k ∈ P.Gf (x k)
  g_angle : ∀ k, ⟪ContinuousLinearMap.adjoint (B k) (g k), gt k⟫_ℝ ≤
    μ * ‖ContinuousLinearMap.adjoint (B k) (g k)‖ * ‖gt k‖
  r_ne_zero : ∀ k, ContinuousLinearMap.adjoint (B k) (g k) - gt k ≠ 0
  B_succ : ∀ k, B (k + 1) =
    (B k).comp (dilation (1 / α) (unitDir (ContinuousLinearMap.adjoint (B k) (g k) - gt k)))
  gt_succ : ∀ k, gt (k + 1) =
    dilation (1 / α) (unitDir (ContinuousLinearMap.adjoint (B k) (g k) - gt k))
      (ContinuousLinearMap.adjoint (B k) (g k))
  h_nonneg : ∀ k, 0 ≤ h (k + 1)
  x_succ : ∀ k, x (k + 1) = x k - h (k + 1) • B (k + 1) (gt (k + 1))
  antitoneOn_step : ∀ k,
    AntitoneOn (fun t : ℝ => f (x k - t • B (k + 1) (gt (k + 1)))) (Set.Icc 0 (h (k + 1)))

end ShorNonsmooth.RAlgorithm


