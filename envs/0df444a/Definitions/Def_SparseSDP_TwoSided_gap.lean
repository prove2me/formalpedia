-- Prove2me | Definitions.Def_SparseSDP_TwoSided_gap
-- name    : SparseSDP_TwoSided_gap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:30.4415+00:00
-- url     : https://prove2.me/theorems/2df35ea9-6fb1-47ab-8e47-c945a2e67c86
-- title:
--   The saddle-point gap $\mathrm{Gap}(X,y)=R\lambda_{\max}(A^*y)-r\min_j\langle A_j,X\rangle$, and the matrix notions under it
-- statement:
--   Matrix and game notation of §2.1 and §2.5, over $\mathbb R$ or $\mathbb C$.
--
--   1. The **Hilbert–Schmidt inner product** $\langle A,B\rangle=\operatorname{Tr}(A^\dagger B)$, Eq. (22), real part.
--   2. $\lambda_{\max}(A)$, the largest eigenvalue of a Hermitian matrix.
--   3. The Euclidean norm $\|x\|_2$ and the minimum $\min_{j\in[k]}f(j)$ over a nonempty index.
--   4. The **spectrahedron** $R\mathcal S_n=\{X\succeq0:\operatorname{Tr}X=R\}$, Eq. (30), and the **scaled simplex** $r\Delta_k=\{y\ge0:\|y\|_1=r\}$, Eq. (31).
--   5. The adjoint map $A^*y=\sum_j y_jA_j$, Eq. (32), and the **saddle-point gap**
--   $$
--   \mathrm{Gap}(X,y)=R\,\lambda_{\max}(A^*y)-r\min_{j}\langle A_j,X\rangle,
--   $$
--   Eq. (36).
--   6. The game value $s=\max_{X\in R\mathcal S_n}\min_{y\in r\Delta_k}L(X,y)$, Eq. (34), with the inner minimum written as $r\min_j\langle A_j,X\rangle$.
--   7. **$s$-row-sparsity**: every row has at most $s$ nonzero entries.
--
--   Gap at most $\varepsilon$ certifies an additive-$\varepsilon$ approximate saddle point; all of §7 is about this quantity.
--
--   **Formalization Note** $\lambda_{\max}$ is the real supremum of the eigenvalue set, which is finite and nonempty for a Hermitian matrix on a nonempty index. The game value is a real supremum over a compact nonempty set when $R>0$ and the index is nonempty.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, §2.1, Eq. (22), p. 15; §2.5, Eqs. (30)–(36), pp. 16–17

import Mathlib

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- The Hilbert–Schmidt inner product `⟨A, B⟩ = Tr(A†B)` of Eq. (22), real part.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
§2.1, Eq. (22), p. 15.

**Formalization Note.** Every use in the paper has `A`, `B` Hermitian, where the trace is real; the
real part is taken so that the value is a real number. The definition works over `ℝ` and `ℂ`. -/
noncomputable def hs (A B : Matrix ι ι 𝕜) : ℝ := RCLike.re (Matrix.trace (Aᴴ * B))

/-- `λmax(A)`: the largest eigenvalue of a Hermitian matrix (§2.1, p. 15).

**Formalization Note.** The set of real eigenvalues of a Hermitian matrix on a nonempty finite index
is finite and nonempty, so the real `sSup` is its maximum. On an empty index it is `0`; every use has
a nonempty index. -/
noncomputable def lamMax (A : Matrix ι ι 𝕜) : ℝ :=
  sSup {μ : ℝ | ∃ v : ι → 𝕜, v ≠ 0 ∧ A *ᵥ v = (μ : 𝕜) • v}

/-- The Euclidean norm `‖x‖₂`. -/
noncomputable def l2 (x : ι → 𝕜) : ℝ := √(∑ i, ‖x i‖ ^ 2)

/-- `min_{j ∈ [k]} f j`, over the nonempty index `Fin k`. -/
noncomputable def minOver {k : ℕ} [NeZero k] (f : Fin k → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

/-- The radius-`R` spectrahedron `RSₙ = {X ⪰ 0 : Tr X = R}`, Eq. (30), p. 16. -/
def Spect (R : ℝ) : Set (Matrix ι ι 𝕜) :=
  {X | X.PosSemidef ∧ RCLike.re (Matrix.trace X) = R}

/-- The radius-`r` scaled simplex `r∆ₖ = {y ≥ 0 : ‖y‖₁ = r}`, Eq. (31), p. 16. -/
def Simplex (k : ℕ) (r : ℝ) : Set (Fin k → ℝ) :=
  {y | (∀ j, 0 ≤ y j) ∧ ∑ j, y j = r}

/-- The adjoint map `A*y = ∑ⱼ yⱼ Aⱼ`, Eq. (32), p. 17. -/
noncomputable def adj {k : ℕ} (A : Fin k → Matrix ι ι 𝕜) (y : Fin k → ℝ) : Matrix ι ι 𝕜 :=
  ∑ j, y j • A j

/-- The saddle-point gap in the form of Eq. (36), p. 17:
`Gap(X, y) = R λmax(A*y) − r minⱼ ⟨Aⱼ, X⟩`. -/
noncomputable def gap {k : ℕ} [NeZero k] (A : Fin k → Matrix ι ι 𝕜) (R r : ℝ)
    (X : Matrix ι ι 𝕜) (y : Fin k → ℝ) : ℝ :=
  R * lamMax (adj A y) - r * minOver fun j => hs (A j) X

/-- The value `s = max_{X ∈ RSₙ} min_{y ∈ r∆ₖ} L(X, y)` of the game, Eq. (34), p. 17, with the inner
minimum written `r minⱼ ⟨Aⱼ, X⟩` (the minimum of a linear function on `r∆ₖ`, cf. Eq. (238)).

**Formalization Note.** For `R > 0` on a nonempty index, `RSₙ` is compact and nonempty and the
function is continuous, so the real `sSup` is an attained maximum. -/
noncomputable def saddleValue {k : ℕ} [NeZero k] (A : Fin k → Matrix ι ι 𝕜) (R r : ℝ) : ℝ :=
  sSup {v | ∃ X ∈ (Spect R : Set (Matrix ι ι 𝕜)), v = r * minOver fun j => hs (A j) X}

/-- `M` is `s`-row-sparse: every row has at most `s` nonzero entries (§1, p. 1; Definition 2.1). -/
def RowSparse [DecidableEq 𝕜] (M : Matrix ι ι 𝕜) (s : ℕ) : Prop :=
  ∀ i, (Finset.univ.filter fun c => M i c ≠ 0).card ≤ s

end SparseSDP.TwoSided


