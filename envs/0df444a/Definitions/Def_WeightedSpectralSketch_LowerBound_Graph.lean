-- Prove2me | Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
-- name    : WeightedSpectralSketch_LowerBound_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:56:22.553609+00:00
-- url     : https://prove2.me/theorems/fdbef2e1-1e56-488f-a7ec-c44de82f1194
-- title:
--   Edge slots, Laplacian form, $(1\pm\varepsilon)$-spectral sparsifiers, weight ratio, randomized linear sketches and incidence sketches
-- statement:
--   Let $V$ be a finite vertex set. An **edge slot** is an unordered pair $uv$ of distinct vertices; $\binom{V}{2}$ denotes the set of edge slots. An input graph is a real weight vector $w\in\mathbb R^{\binom V2}$; the coordinate $w_{uv}$ is the weight of the edge $uv$, and a zero coordinate is an absent edge. The **Laplacian quadratic form** of $w$ is
--
--   $$
--   x^\top L_w x=\sum_{uv\in\binom V2} w_{uv}\,(x_u-x_v)^2,\qquad L_w=\sum_{uv} w_{uv}(e_u-e_v)(e_u-e_v)^\top .
--   $$
--
--   1. A real matrix $\widehat L\in\mathbb R^{V\times V}$ is a **$(1\pm\varepsilon)$-spectral sparsifier** of $L_w$ if $\widehat L$ is symmetric and
--   $$(1-\varepsilon)\,x^\top L_w x\le x^\top \widehat L x\le (1+\varepsilon)\,x^\top L_w x\quad\text{for all }x\in\mathbb R^V.$$
--   The output need not be a Laplacian, need not be sparse and need not be supported on the edges of $w$.
--   2. A weight vector has **positive-weight ratio at most $\rho$** if there is a scale $a>0$ such that every coordinate is either $0$ or lies in $[a,\rho a]$. When some edge is present this says exactly $w_{\max}/w_{\min}\le\rho$ over the nonzero coordinates; the empty graph is admissible. There is no bound on the absolute scale of the weights.
--   3. A **randomized linear sketch of dimension $N$ with recovery** is a probability space $(\Omega,P)$ together with a measurable sketch matrix $A(\omega)\in\mathbb R^{N\times\binom V2}$ and a recovery map $D(\omega,\cdot):\mathbb R^N\to\mathbb R^{V\times V}$, jointly measurable in $(\omega,z)$. On input $w$ the algorithm draws $\omega\sim P$ independently of $w$, observes $A(\omega)w$ and outputs $D(\omega,A(\omega)w)$. Its **success probability** on $w$ (for error $\varepsilon$) is $P\{\omega: D(\omega,A(\omega)w)\text{ is a }(1\pm\varepsilon)\text{-spectral sparsifier of }L_w\}$: one event for all test vectors $x$ at once.
--   4. A matrix $B$ with columns indexed by $\binom R2$ is an **incidence sketch matrix** on $R$ if each row can be assigned to a vertex incident to every edge on which that row is nonzero (zero rows arbitrarily); equivalently, with $I_v$ the rows assigned to $v$, the column $b_{uv}$ is supported on $I_u\cup I_v$. Entries are arbitrary reals.
--
--   These are the objects of the paper's model (§1–2) and of its incidence sketches (§2, §5). The single shared seed $\omega$ covers sketch matrices drawn from any distribution and recoveries using internal randomness, possibly correlated with the matrix.
--
--   **Formalization Note.** Edge slots are `Sym2` elements off the diagonal. The Laplacian form is the published `SpectralSparsify.Sampling.lapForm` of the symmetric zero-diagonal weight function $(u,v)\mapsto w_{uv}$. The sketch matrix and the recovery output are stored as plain function arrays so that the product $\sigma$-algebras apply. `colS` extends a column family indexed by edge slots to all pairs, with the zero vector on the diagonal.
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, pp. 1–3, §1 (Laplacian, (1±ε)-spectral sparsifier, linear sketch model), p. 2 (w_max/w_min), p. 3 and p. 14 (incidence sketches), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph

open MeasureTheory Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- Edge slots: unordered pairs of distinct vertices, `binom(V, 2)` (Chen–Chen–Yang, §1, p. 1, and
§3, p. 7). An input graph is a real weight vector indexed by this type; a zero coordinate is an
absent edge. -/
abbrev EdgeSlot (V : Type*) : Type _ := {e : Sym2 V // ¬ e.IsDiag}

/-- The symmetric, zero-diagonal weight function `(u, v) ↦ w_{uv}` of an edge-weight vector `w`.
It turns `w` into the pair representation used by `SpectralSparsify.Sampling.lapForm`. -/
noncomputable def pairWeight {V : Type*} [DecidableEq V] (w : EdgeSlot V → ℝ) (u v : V) : ℝ :=
  if h : u = v then 0 else w ⟨s(u, v), by simpa using h⟩

/-- The Laplacian quadratic form `xᵀ L_w x = ∑_{uv} w_{uv} (x_u - x_v)²` of the edge-weight
vector `w` (p. 1). -/
noncomputable def laplacianForm {V : Type*} [Fintype V] [DecidableEq V] (w : EdgeSlot V → ℝ)
    (x : V → ℝ) : ℝ :=
  SpectralSparsify.Sampling.lapForm (pairWeight w) x

/-- `L` is a `(1 ± ε)`-spectral sparsifier (spectral approximation) of `L_w` (p. 1): `L` is a
symmetric real matrix and `(1 - ε) xᵀ L_w x ≤ xᵀ L x ≤ (1 + ε) xᵀ L_w x` for **all** `x ∈ ℝ^V`.
`L` need not be a Laplacian, sparse, or supported on the edges of `w`. -/
def IsSpectralApprox {V : Type*} [Fintype V] [DecidableEq V] (ε : ℝ) (w : EdgeSlot V → ℝ)
    (L : Matrix V V ℝ) : Prop :=
  L.IsSymm ∧ ∀ x : V → ℝ,
    (1 - ε) * laplacianForm w x ≤ x ⬝ᵥ (L *ᵥ x) ∧ x ⬝ᵥ (L *ᵥ x) ≤ (1 + ε) * laplacianForm w x

/-- Positive-weight ratio at most `ρ` (p. 2, `w_max / w_min`), stated without an empty minimum:
there is a scale `a > 0` such that every coordinate is either `0` or lies in `[a, ρ a]`. For a
graph with at least one edge this is exactly `w_max / w_min ≤ ρ` over the nonzero coordinates, and
the empty graph is admissible. No bound on the absolute scale of the weights is imposed. -/
def RatioAdmissible {V : Type*} (ρ : ℝ) (w : EdgeSlot V → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ e, w e = 0 ∨ (a ≤ w e ∧ w e ≤ ρ * a)

/-- The column `a_e` of a matrix with columns indexed by edge slots, extended to all of `Sym2 V`
by the zero vector on the diagonal (so that `a_{uv}` can be written for vertex pairs). -/
noncomputable def colS {V : Type*} {m : Type*} (A : Matrix m (EdgeSlot V) ℝ) (e : Sym2 V) :
    m → ℝ :=
  open Classical in if h : e.IsDiag then 0 else Aᵀ ⟨e, h⟩

/-- A randomized linear sketch of dimension `N` with a recovery algorithm, in the joint random-seed
model (p. 2): a seed `ω` drawn from a probability space independent of the input determines the
real `N × binom(V,2)` sketch matrix `A ω` and the recovery map `D ω`, which sees the input `w` only
through the measurements `A ω w` and outputs a real `V × V` matrix. The standing measurability
convention: `A` is measurable and `D` is jointly measurable in the seed and the measurements. -/
structure LinearSketch (V : Type*) (N : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The sketch matrix, rows `Fin N`, columns the edge slots. -/
  A : Ω → Fin N → EdgeSlot V → ℝ
  /-- The recovery algorithm. -/
  D : Ω → (Fin N → ℝ) → V → V → ℝ
  measurable_A : Measurable A
  measurable_D : Measurable (Function.uncurry D)

/-- The probability, over the seed, that recovery from the sketch `A ω w` of the input `w` returns
a `(1 ± ε)`-spectral approximation of `L_w`. -/
noncomputable def successProb {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (S : LinearSketch V N Ω) (ε : ℝ) (w : EdgeSlot V → ℝ) :
    ℝ≥0∞ :=
  P {ω | IsSpectralApprox ε w (Matrix.of (S.D ω (Matrix.of (S.A ω) *ᵥ w)))}

/-- An incidence sketch matrix on the vertex set `R` (p. 3, p. 14): each row can be assigned to a
vertex that is incident to every edge on which the row is nonzero (zero rows are assigned
arbitrarily). Equivalently, with `I_v` the rows assigned to `v`, the column `b_{uv}` is supported on
`I_u ∪ I_v`. The entries are arbitrary reals. -/
def IsIncidence {R : Type*} {K : Type*} (B : Matrix K (EdgeSlot R) ℝ) : Prop :=
  ∃ assign : K → R, ∀ r e, B r e ≠ 0 → assign r ∈ e.1

end WeightedSpectralSketch.LowerBound


