-- Prove2me | Definitions.Def_SimplicialIso_Cheeger_Setting
-- name    : SimplicialIso_Cheeger_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:29.992515+00:00
-- url     : https://prove2.me/theorems/330a5151-bef3-42c7-9751-1132ab628951
-- title:
--   pp. 3, 5–6, 8 — complex with complete skeleton, (d−1)-forms, ∂_d, ∂*_d, ∂_{d−1}, Δ⁺, (d−1)-cycles, F(A_0,…,A_d), Cheeger ratio
-- statement:
--   Fix integers $n$ and $d$. A **finite $d$-dimensional simplicial complex $X$ with a complete skeleton** on the vertex set $V=\{0,1,\dots,n-1\}$ is given by its set $X^d$ of $d$-cells, each a set of $d+1$ vertices; every set of at most $d$ vertices is a cell of $X$ ("every possible $j$-cell with $j<d$ belongs to $X$").
--
--   **Forms.** Every cell is oriented by the increasing order of its vertices, so a skew-symmetric function on oriented $(k-1)$-cells is the same as a real function on sets of $k$ vertices. Thus $\Omega^{d-1}$ is the space of real functions on the $d$-element subsets of $V$, with the inner product
--   $$\langle f,g\rangle=\sum_{\sigma\in X^{d-1}} f(\sigma)\,g(\sigma) \qquad (2.1).$$
--   $\Omega^d$ is modelled as the functions on $(d+1)$-element subsets, and $\Omega^{d-2}$ as the functions on $(d-1)$-element subsets.
--
--   **Sign.** For a cell $\tau$ and a vertex $v=\tau_i$, the $i$-th vertex of $\tau$ in increasing order, write $\operatorname{sgn}(\tau,v)=(-1)^i$.
--
--   **Operators** (p. 6).
--   1. The co-boundary $\partial_d^*:\Omega^{d-1}\to\Omega^d$: $(\partial_d^* f)(\tau)=\sum_{i=0}^{d}(-1)^i f(\tau\setminus\tau_i)$ for $\tau\in X^d$, and $0$ on sets of $d+1$ vertices that are not cells of $X$.
--   2. The boundary $\partial_d:\Omega^d\to\Omega^{d-1}$: $(\partial_d g)(\sigma)=\sum_{v\sim\sigma} g(v\sigma)$, where $v\sim\sigma$ means $v\notin\sigma$ and $\{v\}\cup\sigma\in X^d$, and $v\sigma=[v,\sigma_0,\dots,\sigma_{d-1}]$, which equals $\operatorname{sgn}(\{v\}\cup\sigma,v)$ times the increasingly oriented cell.
--   3. The boundary $\partial_{d-1}:\Omega^{d-1}\to\Omega^{d-2}$ on the complete skeleton: $(\partial_{d-1}f)(\rho)=\sum_{v\notin\rho} f(v\rho)$.
--   4. The upper Laplacian $\Delta^+=\partial_d\partial_d^*$ on $\Omega^{d-1}$.
--   5. The space of $(d-1)$-cycles $Z_{d-1}=\ker\partial_{d-1}$; a real $\mu$ is an eigenvalue of an operator $T$ on $Z_{d-1}$ if $Tf=\mu f$ for some nonzero $f\in Z_{d-1}$.
--
--   **Partitions and the Cheeger ratio** (Definition 1.1). For sets $A_0,\dots,A_d\subseteq V$, $F(A_0,\dots,A_d)$ is the set of $d$-cells of $X$ with exactly one vertex in each $A_i$. A partition of $V$ into nonempty sets $A_0,\dots,A_d$ has Cheeger ratio
--   $$\frac{n\cdot|F(A_0,A_1,\dots,A_d)|}{|A_0|\cdot|A_1|\cdots|A_d|},$$
--   and the Cheeger constant $h(X)$ is its minimum over all such partitions.
--
--   These are the objects of Theorem 1.2: the spectral gap $\lambda(X)$ of Definition 2.1 is the least eigenvalue of $\Delta^+$ on $Z_{d-1}$.
--
--   **Formalization Note.** Vertices are `Fin n`; the complex is the structure `Complex n d` holding its $d$-cells, which builds the complete skeleton in. Forms are `EuclideanSpace ℝ` over the subtype of $k$-element subsets, so no form has support outside cells of the right size; `ev f s` reads a form at a finset and returns $0$ on a set of the wrong size. The operators are defined by their formulas, not as adjoints of each other. $\Omega^d$ also contains values on non-cells; $\partial_d^*$ vanishes there and $\partial_d$ ignores them. A partition is a family `A : Fin (d+1) → Finset (Fin n)` of nonempty, pairwise disjoint sets covering `Fin n`; the ratio is symmetric in the blocks, so ordered families give the same minimum as unordered partitions.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, pp. 3, 5–6, 8: complete skeleton (p. 3), Definition 1.1 (p. 3), forms and inner product (2.1) (pp. 5–6), boundary and co-boundary operators and Laplacians (p. 6), Definition 2.1 (p. 8)

import Mathlib

namespace SimplicialIso.Cheeger

open Finset

/-- A finite `d`-dimensional simplicial complex on the vertex set `Fin n` **with a complete
skeleton**: every subset of at most `d` vertices is a cell, so the complex is determined by its
set `top` of `d`-cells, each a set of `d + 1` vertices. -/
structure Complex (n d : ℕ) where
  /-- the `d`-cells `X^d` -/
  top : Finset (Finset (Fin n))
  /-- every `d`-cell has `d + 1` vertices -/
  card_top : ∀ τ ∈ top, τ.card = d + 1

/-- A `(k - 1)`-cell: a set of exactly `k` vertices, oriented by the order of `Fin n`. -/
abbrev Cell (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- Forms on cells with `k` vertices (`Ω^{k-1}` on the complete skeleton), with the inner
product `⟨f, g⟩ = ∑_σ f(σ) g(σ)` of (2.1). Each cell carries the orientation given by the
increasing order of its vertices, so a skew-symmetric function on oriented cells is a function
on cells. -/
abbrev Form (n k : ℕ) := EuclideanSpace ℝ (Cell n k)

variable {n d : ℕ}

/-- The value of a form at a finite set of vertices; `0` if the set has the wrong size. -/
def ev {k : ℕ} (f : Form n k) (s : Finset (Fin n)) : ℝ :=
  if h : s.card = k then f ⟨s, h⟩ else 0

@[simp] lemma ev_add {k : ℕ} (f g : Form n k) (s : Finset (Fin n)) :
    ev (f + g) s = ev f s + ev g s := by
  unfold ev; split_ifs <;> simp

@[simp] lemma ev_smul {k : ℕ} (c : ℝ) (f : Form n k) (s : Finset (Fin n)) :
    ev (c • f) s = c * ev f s := by
  unfold ev; split_ifs <;> simp

/-- Orientation sign `(-1)^i`, where `v` is the `i`-th vertex (counting from `0`) of `τ` in
increasing order: the face `τ \ {v}` of the oriented cell `τ` carries the sign `(-1)^i`. -/
def sgn (τ : Finset (Fin n)) (v : Fin n) : ℝ := (-1 : ℝ) ^ (τ.filter (· < v)).card

/-- The co-boundary operator `∂*_d : Ω^{d-1} → Ω^d`,
`(∂*_d f)(τ) = ∑_{i=0}^{d} (-1)^i f(τ \ τ_i)` for a `d`-cell `τ ∈ X^d`, and `0` on sets of
`d + 1` vertices that are not cells of `X`. -/
def cobdTop (X : Complex n d) : Form n d →ₗ[ℝ] Form n (d + 1) where
  toFun f := WithLp.toLp 2 (fun τ =>
    if τ.1 ∈ X.top then ∑ v ∈ τ.1, sgn τ.1 v * ev f (τ.1.erase v) else 0)
  map_add' f g := by
    ext τ
    simp only [ev_add, mul_add, Finset.sum_add_distrib, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c f := by
    ext τ
    simp only [ev_smul, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    · simp

/-- The boundary operator `∂_d : Ω^d → Ω^{d-1}`,
`(∂_d g)(σ) = ∑_{v ∼ σ} g(vσ)` where `v ∼ σ` means `v ∉ σ` and `{v} ∪ σ ∈ X^d`, and `vσ` is the
oriented cell `[v, σ_0, …, σ_{d-1}]`; in increasing vertex order it carries the sign
`sgn ({v} ∪ σ) v`. -/
def bdTop (X : Complex n d) : Form n (d + 1) →ₗ[ℝ] Form n d where
  toFun g := WithLp.toLp 2 (fun σ =>
    ∑ v ∈ univ.filter (fun v => v ∉ σ.1 ∧ insert v σ.1 ∈ X.top),
      sgn (insert v σ.1) v * ev g (insert v σ.1))
  map_add' f g := by
    ext σ
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext σ
    simp [Finset.mul_sum, mul_left_comm]

/-- The boundary operator `∂_{d-1} : Ω^{d-1} → Ω^{d-2}` on the complete `(d-1)`-skeleton:
`(∂_{d-1} f)(ρ) = ∑_{v ∉ ρ} f(vρ)` for every set `ρ` of `d - 1` vertices. -/
def bdLow (n d : ℕ) : Form n d →ₗ[ℝ] Form n (d - 1) where
  toFun f := WithLp.toLp 2 (fun ρ =>
    ∑ v ∈ univ.filter (fun v => v ∉ ρ.1), sgn (insert v ρ.1) v * ev f (insert v ρ.1))
  map_add' f g := by
    ext ρ
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext ρ
    simp [Finset.mul_sum, mul_left_comm]

/-- The upper Laplacian `Δ⁺ = ∂_d ∂*_d : Ω^{d-1} → Ω^{d-1}`. -/
def upLap (X : Complex n d) : Form n d →ₗ[ℝ] Form n d := bdTop X ∘ₗ cobdTop X

/-- The space `Z_{d-1} = ker ∂_{d-1}` of `(d-1)`-cycles. -/
def cycles (n d : ℕ) : Submodule ℝ (Form n d) := LinearMap.ker (bdLow n d)

/-- `μ` is an eigenvalue of `T` restricted to the `(d-1)`-cycles: some nonzero cycle `f`
satisfies `T f = μ f`. -/
def IsCycleEigenvalue (T : Form n d →ₗ[ℝ] Form n d) (μ : ℝ) : Prop :=
  ∃ f ∈ cycles n d, f ≠ 0 ∧ T f = μ • f

/-- `F(A_0, …, A_d)`: the `d`-cells of `X` with exactly one vertex in each `A_i`. -/
def F (X : Complex n d) (A : Fin (d + 1) → Finset (Fin n)) : Finset (Finset (Fin n)) :=
  X.top.filter (fun τ => ∀ i, (τ ∩ A i).card = 1)

/-- `A_0, …, A_d` is a partition of the vertex set into `d + 1` nonempty blocks. -/
def IsPartition (A : Fin (d + 1) → Finset (Fin n)) : Prop :=
  (∀ i, (A i).Nonempty) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧ ∀ v, ∃ i, v ∈ A i

/-- The Cheeger ratio `n · |F(A_0, …, A_d)| / (|A_0| ⋯ |A_d|)` of Definition 1.1. -/
noncomputable def cheegerRatio (X : Complex n d) (A : Fin (d + 1) → Finset (Fin n)) : ℝ :=
  (n : ℝ) * ((F X A).card : ℝ) / ∏ i, ((A i).card : ℝ)

end SimplicialIso.Cheeger


