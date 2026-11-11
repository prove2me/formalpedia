-- Prove2me | Definitions.Def_ProdMixedTomo_TestNorms
-- name    : ProdMixedTomo_TestNorms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:13:48.491457+00:00
-- url     : https://prove2.me/theorems/5ee4243c-7cd3-4942-b36e-af7eb49e2b52
-- title:
--   Test sets $T_\mu$, $\mathcal T_\mu$, the dual norms $\|\cdot\|_\mu$ and $\Pi_{\mathrm{off}}$
-- statement:
--   For $\mu\in[0,1]^n$ (Definition 4.6),
--   $$
--   T_\mu=\Bigl\{y\in\mathbb R^n:\ \|y\|_\infty\le1,\ \sum_i\mu_iy_i^2\le1\Bigr\},\qquad \|x\|_\mu=\sup_{y\in T_\mu}\langle y,x\rangle .
--   $$
--   Its convex relaxation (Equation (1)) is
--   $$
--   \mathcal T_\mu=\Bigl\{M\in S^n_{\ge0}:\ M_{ii}\le1,\ \sum_i\mu_iM_{ii}\le1\Bigr\},\qquad \|A\|_\mu=\sup_{M\in\mathcal T_\mu}|\langle A,M\rangle| ,
--   $$
--   with $S^n_{\ge0}$ the real symmetric positive semidefinite matrices and $\langle A,M\rangle=\operatorname{tr}(A^\top M)$. Finally $\Pi_{\mathrm{off}}(A)=A-\operatorname{diag}(A)$ (Definition 4.13).
--
--   $\|\cdot\|_\mu$ characterizes total variation between product distributions (Theorem 4.7), and $\mathcal T_\mu$ is the set over which the filter of Algorithm 2 optimizes.
--
--   **Formalization Note** Both suprema are over nonempty bounded sets, so the real supremum is the true one. The vector norm and the matrix norm are separate definitions (`vnorm`, `mnorm`). The definitions are total in $\mu$; theorems use them for $\mu\in[0,1]^n$.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Definition 4.6, p.23 (PDF p.25); Equation (1), p.25 (PDF p.27); Definition 4.13, p.27 (PDF p.29)

import Mathlib

namespace ProdMixedTomo

/-!
# The test sets `T_μ`, `𝒯_μ`, their dual norms and `Π_off`

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…):
* Definition 4.6, p.23 (PDF p.25): for `μ ∈ [0,1]ⁿ`,
  `T_μ = {y ∈ ℝⁿ : ‖y‖_∞ ≤ 1, Σᵢ μᵢ yᵢ² ≤ 1}` and `‖x‖_μ = sup_{y ∈ T_μ} ⟨y, x⟩`;
* Equation (1), p.25 (PDF p.27): `𝒯_μ = {M ∈ S^n_{≥0} : M_ii ≤ 1, Σᵢ μᵢ M_ii ≤ 1}` and, for a
  symmetric `A`, `‖A‖_μ = sup_{M ∈ 𝒯_μ} |⟨A, M⟩|`;
* Definition 4.13, p.27 (PDF p.29): `Π_off(A) = A − diag(A)`.

**Formalization Note.** `S^n_{≥0}` is the set of real symmetric positive semidefinite matrices
(`Matrix.PosSemidef` over `ℝ`, which includes symmetry). `⟨A, M⟩ = tr(AᵀM) = Σᵢⱼ Aᵢⱼ Mᵢⱼ`. Both
suprema are of nonempty sets (they contain `0`) that are bounded (`|yᵢ| ≤ 1`, `|Mᵢⱼ| ≤ 1`), so
the real `sSup` is the true supremum. The vector norm `vnorm` and the matrix norm `mnorm` are
different suprema and carry different names. The definitions are total in `μ`; the paper and the
theorems use them for `μ ∈ [0,1]ⁿ`.
-/

/-- `T_μ` (Definition 4.6). -/
def Tset {n : ℕ} (μ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, |y i| ≤ 1) ∧ ∑ i, μ i * y i ^ 2 ≤ 1}

/-- The dual norm `‖x‖_μ = sup_{y ∈ T_μ} ⟨y, x⟩` (Definition 4.6). -/
noncomputable def vnorm {n : ℕ} (μ x : Fin n → ℝ) : ℝ :=
  sSup ((fun y => y ⬝ᵥ x) '' Tset μ)

/-- `𝒯_μ` (Equation (1)). -/
def TTset {n : ℕ} (μ : Fin n → ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | M.PosSemidef ∧ (∀ i, M i i ≤ 1) ∧ ∑ i, μ i * M i i ≤ 1}

/-- The Frobenius inner product `⟨A, M⟩ = tr(AᵀM)`. -/
def frob {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j * M i j

/-- The dual norm `‖A‖_μ = sup_{M ∈ 𝒯_μ} |⟨A, M⟩|` on matrices. -/
noncomputable def mnorm {n : ℕ} (μ : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun M => |frob A M|) '' TTset μ)

/-- `Π_off(A) = A − diag(A)` (Definition 4.13). -/
def offDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A - Matrix.diagonal (fun i => A i i)

end ProdMixedTomo


