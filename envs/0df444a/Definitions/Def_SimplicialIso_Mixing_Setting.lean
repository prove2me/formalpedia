-- Prove2me | Definitions.Def_SimplicialIso_Mixing_Setting
-- name    : SimplicialIso_Mixing_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:34.252388+00:00
-- url     : https://prove2.me/theorems/2244e201-1062-4f39-9a50-db00c5eb90c8
-- title:
--   pp. 5–6, 9, 17 — complex with complete skeleton, forms, ∂, ∂*, Δ⁺, Δ⁻, Δ, Z_{d−1}, B^{d−1} and projections, D, complement complex, F(A_0,…,A_d)
-- statement:
--   Fix integers $n$ and $d$. A **finite $d$-dimensional simplicial complex $X$ with a complete skeleton** on the vertex set $V=\{0,1,\dots,n-1\}$ is given by its set $X^d$ of $d$-cells, each a set of $d+1$ vertices; every set of at most $d$ vertices is a cell of $X$. The **complement complex** $\overline X$ has the same skeleton and $\overline X^d=\binom{V}{d+1}\setminus X^d$.
--
--   **Forms.** Every cell is oriented by the increasing order of its vertices, so a skew-symmetric function on oriented $(k-1)$-cells is a real function on the $k$-element subsets of $V$. Thus $\Omega^{d-1}$ is the space of real functions on $\binom{V}{d}$, $\Omega^{d-2}$ the functions on $\binom{V}{d-1}$ (for $d=1$ this is $\Omega^{-1}=\mathbb R^{\{\varnothing\}}$), and $\Omega^d$ is modelled as the functions on $\binom{V}{d+1}$. Each carries the inner product
--   $$\langle f,g\rangle=\sum_{\sigma} f(\sigma)\,g(\sigma) \qquad (2.1).$$
--
--   **Sign.** For a set $\tau$ and a vertex $v=\tau_i$, the $i$-th vertex of $\tau$ in increasing order, $\operatorname{sgn}(\tau,v)=(-1)^i$.
--
--   **Operators** (p. 6).
--   1. The co-boundary $\partial_d^*:\Omega^{d-1}\to\Omega^d$, $(\partial_d^* f)(\tau)=\sum_{i=0}^{d}(-1)^i f(\tau\setminus\tau_i)$ for $\tau\in X^d$, and $0$ on other $(d+1)$-sets.
--   2. The boundary $\partial_d:\Omega^d\to\Omega^{d-1}$, $(\partial_d g)(\sigma)=\sum_{v\sim\sigma} g(v\sigma)$, where $v\sim\sigma$ means $v\notin\sigma$ and $\{v\}\cup\sigma\in X^d$, and $v\sigma=[v,\sigma_0,\dots,\sigma_{d-1}]$ is $\operatorname{sgn}(\{v\}\cup\sigma,v)$ times the increasingly oriented cell.
--   3. On the complete skeleton, $\partial_{d-1}:\Omega^{d-1}\to\Omega^{d-2}$, $(\partial_{d-1}f)(\rho)=\sum_{v\notin\rho} f(v\rho)$, and $\partial^*_{d-1}:\Omega^{d-2}\to\Omega^{d-1}$, $(\partial^*_{d-1}g)(\sigma)=\sum_{i=0}^{d-1}(-1)^i g(\sigma\setminus\sigma_i)$.
--   4. The upper, lower and full Laplacians $\Delta^+=\partial_d\partial_d^*$, $\Delta^-=\partial^*_{d-1}\partial_{d-1}$ and $\Delta=\Delta^++\Delta^-$ on $\Omega^{d-1}$.
--   5. The degree $\deg\sigma=\#\{\tau\in X^d\mid\sigma\subseteq\tau\}$, the degree operator $(Df)(\sigma)=\deg(\sigma)f(\sigma)$, and the average degree $k=\frac{1}{\binom nd}\sum_{\sigma}\deg\sigma$ of a $(d-1)$-cell.
--
--   **Subspaces.** The $(d-1)$-cycles $Z_{d-1}=\ker\partial_{d-1}$ and the exact forms $B^{d-1}=\operatorname{im}\partial^*_{d-1}$, with orthogonal projections $\mathbb P_{Z_{d-1}}$ and $\mathbb P_{B^{d-1}}$. A real $\mu$ is an eigenvalue of an operator $T$ on $Z_{d-1}$ if $Tf=\mu f$ for some nonzero $f\in Z_{d-1}$.
--
--   **Cells across blocks.** For sets $A_0,\dots,A_d\subseteq V$, $F(A_0,\dots,A_d)$ is the set of $d$-cells of $X$ with exactly one vertex in each $A_i$.
--
--   These are the objects of the Mixing Lemma (Theorem 1.4).
--
--   **Formalization Note.** Vertices are `Fin n`; `Complex n d` holds the $d$-cells, which builds the complete skeleton in. Forms are `EuclideanSpace ℝ` over the subtype of $k$-element subsets, so no form is supported outside cells of the right size; `ev f s` reads a form at a finset and is $0$ on a set of the wrong size. All four (co)boundary operators are defined by their formulas, not as adjoints of each other. $\Omega^d$ also contains values on non-cells; $\partial_d^*$ vanishes there and $\partial_d$ ignores them. The projections are Mathlib's `Submodule.starProjection`.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, pp. 5–6 (forms, (2.1), boundary and co-boundary operators, Z_j, B^j, Laplacians), p. 9 (complement complex, Proposition 3.2 (1)), p. 17 (degree operator D); p. 4 (average degree k, Theorem 1.4)

import Mathlib

namespace SimplicialIso.Mixing

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
on cells. `Form n 0` is `Ω^{-1} = ℝ^{∅}`. -/
abbrev Form (n k : ℕ) := EuclideanSpace ℝ (Cell n k)

variable {n d : ℕ}

/-- The complement complex `X̄` (Proposition 3.2 (1)): the same complete skeleton, with
`X̄^d = (V choose d+1) \ X^d`. -/
def Complex.compl (X : Complex n d) : Complex n d where
  top := (univ.powersetCard (d + 1)) \ X.top
  card_top _ h := (mem_powersetCard.mp (mem_sdiff.mp h).1).2

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

/-- The co-boundary operator `∂*_{d-1} : Ω^{d-2} → Ω^{d-1}` on the complete skeleton,
`(∂*_{d-1} g)(σ) = ∑_{i=0}^{d-1} (-1)^i g(σ \ σ_i)` for every set `σ` of `d` vertices. -/
def cobdLow (n d : ℕ) : Form n (d - 1) →ₗ[ℝ] Form n d where
  toFun g := WithLp.toLp 2 (fun σ => ∑ v ∈ σ.1, sgn σ.1 v * ev g (σ.1.erase v))
  map_add' f g := by
    ext σ
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext σ
    simp [Finset.mul_sum, mul_left_comm]

/-- The upper Laplacian `Δ⁺ = ∂_d ∂*_d : Ω^{d-1} → Ω^{d-1}` of `X`. -/
def upLap (X : Complex n d) : Form n d →ₗ[ℝ] Form n d := bdTop X ∘ₗ cobdTop X

/-- The lower Laplacian `Δ⁻ = ∂*_{d-1} ∂_{d-1} : Ω^{d-1} → Ω^{d-1}`; on a complex with a
complete skeleton it does not depend on the `d`-cells. -/
def lowLap (n d : ℕ) : Form n d →ₗ[ℝ] Form n d := cobdLow n d ∘ₗ bdLow n d

/-- The full Laplacian `Δ = Δ⁺ + Δ⁻` of `X`. -/
def fullLap (X : Complex n d) : Form n d →ₗ[ℝ] Form n d := upLap X + lowLap n d

/-- The degree `deg σ` of a `(d-1)`-cell: the number of `d`-cells of `X` containing it. -/
def deg (X : Complex n d) (σ : Finset (Fin n)) : ℕ := (X.top.filter (fun τ => σ ⊆ τ)).card

/-- The degree operator `(D f)(σ) = deg(σ) f(σ)` on `Ω^{d-1}`. -/
def degOp (X : Complex n d) : Form n d →ₗ[ℝ] Form n d where
  toFun f := WithLp.toLp 2 (fun σ => (deg X σ.1 : ℝ) * f σ)
  map_add' f g := by
    ext σ
    simp [mul_add]
  map_smul' c f := by
    ext σ
    simp [mul_left_comm]

/-- The average degree `k = (∑_σ deg σ) / (n choose d)` of a `(d-1)`-cell of `X`. -/
noncomputable def avgDeg (X : Complex n d) : ℝ :=
  (∑ σ : Cell n d, (deg X σ.1 : ℝ)) / (n.choose d : ℝ)

/-- The space `Z_{d-1} = ker ∂_{d-1}` of `(d-1)`-cycles. -/
def cycles (n d : ℕ) : Submodule ℝ (Form n d) := LinearMap.ker (bdLow n d)

/-- The space `B^{d-1} = im ∂*_{d-1}` of exact `(d-1)`-forms. -/
def exact (n d : ℕ) : Submodule ℝ (Form n d) := LinearMap.range (cobdLow n d)

/-- The orthogonal projection `ℙ_{B^{d-1}}` onto the exact forms. -/
noncomputable def projExact (n d : ℕ) : Form n d →L[ℝ] Form n d := (exact n d).starProjection

/-- The orthogonal projection `ℙ_{Z_{d-1}}` onto the `(d-1)`-cycles. -/
noncomputable def projCycles (n d : ℕ) : Form n d →L[ℝ] Form n d :=
  (cycles n d).starProjection

/-- `μ` is an eigenvalue of `T` restricted to the `(d-1)`-cycles: some nonzero cycle `f`
satisfies `T f = μ f`. -/
def IsCycleEigenvalue (T : Form n d →ₗ[ℝ] Form n d) (μ : ℝ) : Prop :=
  ∃ f ∈ cycles n d, f ≠ 0 ∧ T f = μ • f

/-- `F(A_0, …, A_d)`: the `d`-cells of `X` with exactly one vertex in each `A_i`. -/
def F (X : Complex n d) (A : Fin (d + 1) → Finset (Fin n)) : Finset (Finset (Fin n)) :=
  X.top.filter (fun τ => ∀ i, (τ ∩ A i).card = 1)

end SimplicialIso.Mixing


