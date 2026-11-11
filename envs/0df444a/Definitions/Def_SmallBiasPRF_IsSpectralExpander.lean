-- Prove2me | Definitions.Def_SmallBiasPRF_IsSpectralExpander
-- name    : SmallBiasPRF_IsSpectralExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:42.265431+00:00
-- url     : https://prove2.me/theorems/3db10d16-1940-4c38-8023-47d87e762a33
-- title:
--   Regular multigraphs, the transition operator $E_\Gamma$, spectral expansion, expander walks and the stationary walk law
-- statement:
--   A finite $d$-regular multigraph $\Gamma$ on a vertex set $\Omega$ whose $d$ edge incidences at each vertex are labelled by $[d]$ is described by its **neighbour function** $NB:\Omega\times[d]\to\Omega$. It is **undirected** when, for all $x,y\in\Omega$, the number of incidences at $x$ leading to $y$ equals the number at $y$ leading to $x$. The normalized adjacency operator is
--
--   $$(E_\Gamma f)(x)=\frac1d\sum_{e=1}^{d}f(NB(x,e)),$$
--
--   $U$ denotes the averaging operator (all transition entries equal to $1/|\Omega|$), and $\Gamma$ is a **$\lambda$-spectral expander** when $\|E_\Gamma-U\|_{op}\le\lambda$; for undirected $\Gamma$ the left side is the second largest singular value of $E_\Gamma$.
--
--   A key $k_e=(x_1,e_1,\dots,e_{m-1})\in\Omega\times[d]^{m-1}$ defines the **expander walk** $x_{j+1}=NB(x_j,e_j)$, $1\le j<m$. The **stationary walk distribution** on $\Omega^m$ is
--
--   $$\mu^m(y_1,\dots,y_m)=\frac1{|\Omega|}\prod_{i=1}^{m-1}E_\Gamma[y_i,y_{i+1}],$$
--
--   the law of a walk with uniform start in which each step is one transition of $E_\Gamma$; a uniform key $k_e$ produces exactly this law.
--
--   **Formalization Note** Undirectedness is the symmetry of the incidence-count matrix, which also admits an odd number of loop incidences at a vertex. $E_\Gamma$ and $U$ are real matrices and the norm is the Euclidean ($L^2$) operator norm; the paper's normalized $L^2(\Omega)$ gives the same operator norm. Walk indices are 0-based.
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.3, pp.15–16 (PDF 18–19), display (3); §6.1, p.37 (PDF 40); Theorem 32, p.38 (PDF 41)

import Mathlib

open scoped Matrix.Norms.L2Operator

namespace SmallBiasPRF

/-- A `d`-regular multigraph on a finite vertex set `Ω` with labelled incidences is given by its
neighbour function `NB : Ω × [d] → Ω` (§4.3, p.15 (PDF p.18)). It is **undirected** when, for all
vertices `x, y`, the number of incidences at `x` leading to `y` equals the number at `y` leading to
`x`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.3, p.15 (PDF p.18).

**Formalization Note.** `[d] = Fin d` (0-based). Undirectedness is encoded as the symmetry of the
incidence-count (adjacency) matrix, which is all the paper uses (`E_Γ` self-adjoint, `E_Γ 1 = 1`,
the uniform start stationary). The encoding also admits an odd number of loop incidences at a
vertex. -/
def IsUndirected {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d : ℕ} (NB : Ω → Fin d → Ω) : Prop :=
  ∀ x y : Ω, (Finset.univ.filter fun e => NB x e = y).card =
    (Finset.univ.filter fun e => NB y e = x).card

/-- The normalized adjacency (transition) operator `E_Γ` of display (3), p.16 (PDF p.19),
`(E_Γ f)(x) = (1/d) ∑_{e=1}^{d} f(NB(x, e))`, as the matrix with entries
`E_Γ[x, y] = #{e : NB(x, e) = y}/d`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (3), p.16. -/
noncomputable def adjMatrix {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d : ℕ} (NB : Ω → Fin d → Ω) :
    Matrix Ω Ω ℝ :=
  fun x y => ((Finset.univ.filter fun e => NB x e = y).card : ℝ) / (d : ℝ)

/-- The averaging operator `U` on `Ω`, whose transition matrix has every entry `1/|Ω|` (p.16
(PDF p.19)). -/
noncomputable def avgMatrix (Ω : Type*) [Fintype Ω] : Matrix Ω Ω ℝ :=
  fun _ _ => (Fintype.card Ω : ℝ)⁻¹

/-- **Spectral expansion** (p.16 (PDF p.19)): the second largest singular value of the expander is
at most `λ`, where the paper defines it as `‖E_Γ − U‖_op = λ`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.3, p.16 (PDF p.19);
Theorem 32, p.38 (PDF p.41).

**Formalization Note.** The norm is Mathlib's Euclidean (`L²`) operator norm of real matrices
(scoped `Matrix.Norms.L2Operator`). The paper's `L²(Ω)` carries the uniform probability measure; a
constant rescaling of the inner product leaves operator norms unchanged. For a symmetric `E_Γ` this
norm is the second largest singular value. -/
def IsSpectralExpander {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d : ℕ} (NB : Ω → Fin d → Ω)
    (lam : ℝ) : Prop :=
  ‖adjMatrix NB - avgMatrix Ω‖ ≤ lam

/-- Auxiliary recursion for `walk`: vertex number `j` (0-based) of the walk started at `x₁` with
incidence labels `e`. -/
def walkAux {Ω : Type*} {d : ℕ} (NB : Ω → Fin d → Ω) {m : ℕ} (x₁ : Ω) (e : Fin (m - 1) → Fin d) :
    ℕ → Ω
  | 0 => x₁
  | j + 1 => if h : j < m - 1 then NB (walkAux NB x₁ e j) (e ⟨j, h⟩) else walkAux NB x₁ e j

/-- The **expander walk** of a key `k_e = (x₁, e₁, …, e_{m−1}) ∈ Ω × [d]^{m−1}` (§4.3, p.15
(PDF p.18)): `x_{j+1} = NB(x_j, e_j)` for `1 ≤ j < m`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.3, p.15.

**Formalization Note.** 0-based: `walk NB x₁ e 0 = x₁` and `walk NB x₁ e (j+1) = NB (walk j) (e j)`
for `j + 1 < m`; `e : Fin (m − 1) → Fin d`. For `m = 1` the walk is the single vertex `x₁`. -/
def walk {Ω : Type*} {d : ℕ} (NB : Ω → Fin d → Ω) {m : ℕ} (x₁ : Ω) (e : Fin (m - 1) → Fin d) :
    Fin m → Ω :=
  fun j => walkAux NB x₁ e j.val

/-- The **stationary walk distribution** `μ^m` on `Ω^m` (§6.1, p.37 (PDF p.40); Theorem 32, p.38):
the initial vertex is uniform and each subsequent vertex is obtained by one transition of `E_Γ`,
`μ^m(y₁, …, y_m) = (1/|Ω|) ∏_{i<m} E_Γ[y_i, y_{i+1}]`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §6.1, p.37 (PDF p.40).

**Formalization Note.** 0-based; the factor at the last index is `1`. Under a uniform key
`(x₁, e)` the walk `walk NB x₁ e` has exactly this law. -/
noncomputable def walkLaw {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d : ℕ} (NB : Ω → Fin d → Ω)
    (m : ℕ) (y : Fin m → Ω) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ *
    ∏ i : Fin m, if h : i.val + 1 < m then adjMatrix NB (y i) (y ⟨i.val + 1, h⟩) else 1

end SmallBiasPRF


