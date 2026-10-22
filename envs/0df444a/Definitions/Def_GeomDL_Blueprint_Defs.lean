-- Prove2me | Definitions.Def_GeomDL_Blueprint_Defs
-- name    : GeomDL_Blueprint_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:36.262285+00:00
-- url     : https://prove2.me/theorems/f1b0ae69-1e24-42cb-aa11-44168a05b768
-- title:
--   §3.1, §3.3, §3.5 — the action (3) on signals, invariance, equivariance, element-wise maps, the G-average, ε-isometries and the blueprint
-- statement:
--   Let $\mathfrak G$ be a group acting on a set $\Omega$ (the **domain**), and write $X(\Omega, C) = \{x : \Omega \to C\}$ for the space of **signals** on $\Omega$ with values in a set of channels $C$ (equation (1)).
--
--   1. **Action on signals** (equation (3)). The action of $\mathfrak G$ on $\Omega$ induces an action on signals,
--   $$(\mathfrak g . x)(u) = x(\mathfrak g^{-1} u), \qquad \mathfrak g \in \mathfrak G,\ x \in X(\Omega, C),\ u \in \Omega.$$
--   2. **Invariance.** A function $f : X(\Omega, C) \to Y$ is $\mathfrak G$-*invariant* if $f(\mathfrak g . x) = f(x)$ for all $\mathfrak g \in \mathfrak G$ and all signals $x$.
--   3. **Equivariance.** If $\mathfrak G$ acts on two domains $\Omega$ and $\Omega'$, a map $B : X(\Omega, C) \to X(\Omega', C')$ is $\mathfrak G$-*equivariant* if $B(\mathfrak g . x) = \mathfrak g . B(x)$ for all $\mathfrak g$ and $x$.
--   4. **Element-wise map.** A map $\sigma : C \to C'$ acts on signals element-wise: $(\boldsymbol\sigma(x))(u) = \sigma(x(u))$.
--   5. **$\mathfrak G$-average.** For a finite domain $\Omega$, real signals $x : \Omega \to \mathbb R$, and a measure $\mu$ on $\mathfrak G$,
--   $$A x = \frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} (\mathfrak g . x)\, \mathrm d\mu(\mathfrak g),$$
--   a Bochner integral of a signal-valued function.
--   6. **$\varepsilon$-isometry.** A self-map $\tau$ of a metric space $(X, d)$ is an $\varepsilon$-isometry if its metric distortion is at most $\varepsilon$: $|d(\tau u, \tau v) - d(u, v)| \le \varepsilon$ for all $u, v$.
--   7. **Blueprint.** Given families of domains $\Omega_j, \Omega'_j$ and channel sets $C_j, D_j, E_j$, layers $B_j : X(\Omega_j, C_j) \to X(\Omega'_j, D_j)$, nonlinearities $\sigma_j : D_j \to E_j$, poolings $P_j : X(\Omega'_j, E_j) \to X(\Omega_{j+1}, C_{j+1})$ and a global pooling $A : X(\Omega'_n, E_n) \to Y$, the blueprint network is
--   $$f = A \circ \boldsymbol\sigma_n \circ B_n \circ P_{n-1} \circ \boldsymbol\sigma_{n-1} \circ B_{n-1} \circ \cdots \circ P_0 \circ \boldsymbol\sigma_0 \circ B_0 .$$
--
--   These are the objects of the book's Chapter 3: every invariance and equivariance statement of the mission is phrased with them.
--
--   **Formalization Note** The action on signals is a function `act`, not a `MulAction` instance on `Ω → C`, because Mathlib already has a pointwise action on function types. The $\mathfrak G$-average uses the factor `(μ univ).toReal⁻¹`, which Lean evaluates to $0$ when $\mu = 0$ or $\mu(\mathfrak G) = \infty$; every theorem using it assumes $\mu$ finite and nonzero. The $\varepsilon$-isometry condition is stated pointwise, not as a supremum, so an unbounded distortion is never read as a finite one. The book indexes the blueprint's layers from $1$ to $J$; here they run from $0$ to $n = J - 1$.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.1, (1) and (3), pp. 11, 14–15; §3.3, side-note p. 20; §4.4, metric distortion, p. 51; §3.5, G-average p. 27 and the Geometric Deep Learning Blueprint box, p. 29

import Mathlib

namespace GeomDL.Blueprint

open MeasureTheory

/-- Bronstein et al., §3.1, equation (3), p. 14: a group `G` acting on the domain `Ω` acts on
signals `x : Ω → C` by `(g.x)(u) = x(g⁻¹ u)`. Defined as a function, not as a `MulAction`
instance on `Ω → C` (Mathlib's `Pi` instance already acts through the codomain). -/
def act {G Ω C : Type*} [Group G] [MulAction G Ω] (g : G) (x : Ω → C) : Ω → C :=
  fun u => x (g⁻¹ • u)

/-- §3.1, p. 15: `f : X(Ω, C) → Y` is `G`-invariant if `f(g.x) = f(x)` for all `g` and `x`. -/
def IsInvariant {G Ω C Y : Type*} [Group G] [MulAction G Ω] (f : (Ω → C) → Y) : Prop :=
  ∀ (g : G) (x : Ω → C), f (act g x) = f x

/-- §3.1, p. 16 and §3.5, p. 27: `B : X(Ω, C) → X(Ω', C')` is `G`-equivariant if
`B(g.x) = g.B(x)` for all `g` and `x`, with `G` acting on both domains by (3). -/
def IsEquivariant {G Ω Ω' C C' : Type*} [Group G] [MulAction G Ω] [MulAction G Ω']
    (B : (Ω → C) → (Ω' → C')) : Prop :=
  ∀ (g : G) (x : Ω → C), B (act g x) = act g (B x)

/-- §3.5, p. 27: the element-wise instantiation `(σ(x))(u) := σ(x(u))` of `σ : C → C'`. -/
def pointwise {Ω C C' : Type*} (σ : C → C') : (Ω → C) → (Ω → C') :=
  fun x u => σ (x u)

/-- §3.5, p. 27: the `G`-average `A x = (1/μ(G)) ∫_G (g.x) dμ(g)` of a real signal on a finite
domain `Ω` (so `Ω → ℝ` is a finite-dimensional normed space), for a measure `μ` on `G`.
The factor is `(μ G).toReal⁻¹`, which is `0` when `μ = 0` or `μ G = ∞`; every theorem using
it assumes `μ` finite and nonzero. -/
noncomputable def groupAverage {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω]
    [MeasurableSpace G] (μ : Measure G) (x : Ω → ℝ) : Ω → ℝ :=
  (μ Set.univ).toReal⁻¹ • ∫ g, act g x ∂μ

/-- §3.3, side-note p. 20, with the metric distortion of §4.4, p. 51: a map `τ : X → X` of a
(pseudo)metric space is an `ε`-isometry if its distortion is at most `ε`, i.e.
`|d(τ u, τ v) − d(u, v)| ≤ ε` for all `u, v` (stated pointwise, without a supremum). -/
def IsEpsIsometry {X : Type*} [PseudoMetricSpace X] (ε : ℝ) (τ : X → X) : Prop :=
  ∀ u v : X, |dist (τ u) (τ v) - dist u v| ≤ ε

/-- §3.5, p. 29 (the Geometric Deep Learning Blueprint): the first `n` stages of the blueprint.
Stage `j` maps `X(Ω j, C j)` to `X(Ω (j+1), C (j+1))` as `P j ∘ σ j ∘ B j`, with an equivariant
layer `B j : X(Ω j, C j) → X(Ω' j, D j)`, the element-wise nonlinearity `σ j : D j → E j`, and a
pooling `P j : X(Ω' j, E j) → X(Ω (j+1), C (j+1))`. -/
def blueprintStages {Ω Ω' : ℕ → Type*} {C D E : ℕ → Type*}
    (B : ∀ j, (Ω j → C j) → (Ω' j → D j)) (σ : ∀ j, D j → E j)
    (P : ∀ j, (Ω' j → E j) → (Ω (j + 1) → C (j + 1))) :
    (n : ℕ) → (Ω 0 → C 0) → (Ω n → C n)
  | 0 => fun x => x
  | n + 1 => fun x => P n (pointwise (σ n) (B n (blueprintStages B σ P n x)))

/-- §3.5, p. 29: the blueprint `f = A ∘ σ_J ∘ B_J ∘ P_{J−1} ∘ … ∘ P_1 ∘ σ_1 ∘ B_1` with
`J = n + 1` equivariant layers and `n` poolings (indices shifted to start at `0`), ending in the
global pooling `A : X(Ω' n, E n) → Y`. -/
def blueprint {Ω Ω' : ℕ → Type*} {C D E : ℕ → Type*} {Y : Type*}
    (B : ∀ j, (Ω j → C j) → (Ω' j → D j)) (σ : ∀ j, D j → E j)
    (P : ∀ j, (Ω' j → E j) → (Ω (j + 1) → C (j + 1))) (n : ℕ) (A : (Ω' n → E n) → Y) :
    (Ω 0 → C 0) → Y :=
  fun x => A (pointwise (σ n) (B n (blueprintStages B σ P n x)))

end GeomDL.Blueprint


