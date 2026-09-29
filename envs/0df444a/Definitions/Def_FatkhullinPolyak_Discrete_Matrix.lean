-- Prove2me | Definitions.Def_FatkhullinPolyak_Discrete_Matrix
-- name    : FatkhullinPolyak_Discrete_Matrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:34:17.492007+00:00
-- url     : https://prove2.me/theorems/048c6a21-274f-40e0-a88b-aa33192810dc
-- title:
--   Matrix toolkit: Hurwitz matrices, largest real part of the spectrum, stability degree, extreme eigenvalues, Frobenius and spectral norms, Lyapunov solution
-- statement:
--   Matrix notions used throughout Fatkhullin and Polyak's analysis of static linear feedback. All matrices are real.
--
--   1. A square matrix $M\in\mathbb R^{k\times k}$ is **Hurwitz** if every complex eigenvalue $z$ of $M$ satisfies $\Re z<0$.
--   2. $\Re\lambda_n(M)$ denotes the **largest real part** of a complex eigenvalue of $M$ (the paper indexes eigenvalues by increasing real part, p. 2), and the **stability degree** is
--   $$\sigma(M) := -\max_i \Re\lambda_i(M).$$
--   3. For a symmetric matrix $M$, $\lambda_1(M)$ is its **smallest** and $\lambda_n(M)$ its **largest** eigenvalue.
--   4. The **Frobenius norm** is $\|M\|_F=\big(\sum_{i,j}M_{ij}^2\big)^{1/2}$ and the **Frobenius inner product** is $\langle M,N\rangle=\mathrm{Tr}(M^\top N)=\sum_{i,j}M_{ij}N_{ij}$.
--   5. The **spectral norm** $\|M\|$ is the largest singular value of $M$, i.e. the operator norm of $M$ between Euclidean spaces.
--   6. For square $M, W$, the **Lyapunov solution** is the matrix $X$ solving
--   $$M^\top X + X M + W = 0,$$
--   which is unique whenever $M$ is Hurwitz.
--
--   These are the basic spectral and normed quantities in which every bound of the mission (Lemmas A.4, A.5, 3.8, C.1–C.3, Theorem 3.17) is expressed.
--
--   **Formalization Note** The eigenvalues of $M$ are the elements of the spectrum of $M$ viewed as a complex matrix. $\max_i\Re\lambda_i$ is the supremum of the real parts of that finite set (nonempty when $k\ge1$). Mathlib's eigenvalues of a Hermitian matrix are not sorted, so $\lambda_1$ and $\lambda_n$ are their minimum and maximum; the value $0$ is returned for a non-symmetric matrix or $k=0$, cases no statement of the mission uses. The Lyapunov solution is "the unique solution if there is exactly one, and $0$ otherwise"; for Hurwitz $M$ it is the genuine solution.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 2 (Notation: spectral and Frobenius norms, eigenvalue ordering), p. 3 (definition of S), p. 15 (Lemma A.5: stability degree σ(A))

import Mathlib

namespace FatkhullinPolyak.Discrete

/-- A real square matrix `M` is **Hurwitz** if every complex eigenvalue of `M` has negative real
part (Fatkhullin–Polyak, p. 3: `ℜλᵢ(M) < 0` for all `i`). Eigenvalues are the elements of the
spectrum of `M` viewed as a complex matrix. -/
def IsHurwitz {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), z.re < 0

/-- The largest real part of a complex eigenvalue of `M`, i.e. `ℜλₙ(M)` in the paper's ordering
of eigenvalues by increasing real part (p. 2). The spectrum is finite, and nonempty when `n ≥ 1`. -/
noncomputable def maxRe {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (Complex.re '' spectrum ℂ (M.map (algebraMap ℝ ℂ)))

/-- The **stability degree** `σ(M) := −maxᵢ ℜλᵢ(M)` (Lemma A.5, p. 15). -/
noncomputable def stabDegree {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  - maxRe M

/-- `λ₁(M)`: the smallest eigenvalue of a symmetric matrix `M` (the paper indexes eigenvalues in
increasing order, p. 2). Mathlib's `IsHermitian.eigenvalues` are unsorted, so this is their
minimum. Junk value `0` if `M` is not symmetric or `n = 0`. -/
noncomputable def lamMin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  if h : M.IsHermitian then
    if hn : 0 < n then Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ h.eigenvalues else 0
  else 0

/-- `λₙ(M)`: the largest eigenvalue of a symmetric matrix `M`. Junk value `0` if `M` is not
symmetric or `n = 0`. -/
noncomputable def lamMax {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  if h : M.IsHermitian then
    if hn : 0 < n then Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ h.eigenvalues else 0
  else 0

/-- The Frobenius norm `‖M‖_F = √(∑ᵢⱼ Mᵢⱼ²)`. -/
noncomputable def frobNorm {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The Frobenius inner product `⟨M, N⟩ = Tr(MᵀN) = ∑ᵢⱼ Mᵢⱼ Nᵢⱼ`. -/
def frobInner {p q : ℕ} (M N : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * N i j

/-- The spectral norm `‖M‖` (largest singular value): the operator norm of `M` as a linear map
between Euclidean spaces (Mathlib's `Matrix.instL2OpNormedAddCommGroup`). -/
noncomputable def specNorm {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  @Norm.norm _ (Matrix.instL2OpNormedAddCommGroup (m := Fin p) (n := Fin q) (𝕜 := ℝ)).toNorm M

open Classical in
/-- The solution of the Lyapunov equation `Mᵀ X + X M + W = 0`, when it is unique (which is the
case whenever `M` is Hurwitz); junk value `0` otherwise. -/
noncomputable def lyapSol {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : ∃! X : Matrix (Fin n) (Fin n) ℝ, M.transpose * X + X * M + W = 0 then h.choose else 0

end FatkhullinPolyak.Discrete


