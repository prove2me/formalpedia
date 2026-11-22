-- Prove2me | Definitions.Def_SKHessianAscent_FreeModel
-- name    : SKHessianAscent_FreeModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T19:59:29.786827+00:00
-- url     : https://prove2.me/theorems/78873be1-2861-4378-9d73-07405b32f8cc
-- title:
--   The free model of §5.3: a semicircular element $S$ free from $M_n(\mathbb C)$, the conditional expectation $\mathbf E_{M_n}$, and $\mathrm{GUE}(n)$
-- statement:
--   Let $(\mathcal A,\tau)$ be a tracial $C^*$-probability space, $\mathcal M_n=M_n(\mathbb C)\otimes\mathcal A$ with $\tau_n=\mathrm{tr}_n\otimes\tau$.
--
--   - `GueIdx n` indexes the orthonormal basis $(K_\gamma)$ (`gueBasis`) of Hermitian $n\times n$ matrices: $E_{ii}/\sqrt n$, and $(E_{ij}+E_{ji})/\sqrt{2n}$, $\mathrm i(E_{ij}-E_{ji})/\sqrt{2n}$ for $i<j$.
--   - `gue n` is the law $\mathrm{GUE}(n)$ of $A_{\mathrm{GUE}}=\sum_\gamma g_\gamma K_\gamma$ with $g_\gamma$ i.i.d. $N(0,1)$: a Hermitian matrix with $\mathbf E|A_{ij}|^2=1/n$.
--   - For a standard free semicircular family $(s_\gamma)$ in $\mathcal A$, the element $S=\sum_\gamma K_\gamma\otimes s_\gamma\in\mathcal M_n$ is a standard semicircular element free from $M_n(\mathbb C)\otimes1$, since $\sum_\gamma K_\gamma MK_\gamma=\mathrm{tr}_n(M)I_n$. `gueOp V L R s` is $V\otimes1+LSR$ for scalar matrices $V,L,R$; in particular `gueOp 0 1 1 s` is $S$ and `gueOp V 0 1 s` is $V\otimes1$.
--   - The trace-preserving conditional expectation $\mathbf E_{M_n}=\mathrm{id}\otimes\tau$ is the published `FreeWeaver.Walk.slice`.
--   - `cBlock β a w A` is the block matrix $\begin{pmatrix}0&I_n+W(aI_n-\beta A)\\I_n+(aI_n-\beta A)W&0\end{pmatrix}$ of (5.11) for a complex matrix $A$ and $W=\mathrm{diag}(w)$, and `blockPencil β a w` is the same block matrix with $A$ replaced by $S$.
--   - `SpecGe X c` is $X\succeq c\cdot1$: $X$ is self-adjoint with spectrum in $[c,\infty)$.
--
--   **Formalization Note** The paper takes "a semicircular element free from $(M_n(\mathbb C),\mathrm{tr}_n)$" abstractly and remarks that the coefficient-defined free model of the GUE "has exactly the $M_n$-valued law of $S$"; $S$ is realized here by that model. The free semicircular family, $M_n(\mathcal A)$, and elements $V\otimes1+\sum_\gamma K_\gamma\otimes s_\gamma$ are the published `FreeWeaver.Walk.IsStdFreeSemicircular`, `CStarMatrix` and `FreeWeaver.Walk.Pencil.op`.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §5.3, p. 31

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil

open FreeWeaver.Walk MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKHessianAscent

/-!
# The free model: a semicircular element free from `M_n(ℂ)`, and the GUE

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, §5.3 (p. 31): "Let `S` be a semicircular element free from `(M_n(ℂ), tr_n)` in
`(𝓜_n, τ_n)`, and let `E_{M_n}` be the trace-preserving conditional expectation onto `M_n(ℂ)`",
and "We introduce the GUE as an intermediate ensemble because its coefficient-defined free model
has exactly the `M_n`-valued law of `S`".

**Formalization Note.** `S` is realized as the paper describes, by the coefficient-defined free
model of the GUE: with `(K_γ)` the orthonormal basis of Hermitian matrices for which
`A_GUE = Σ_γ g_γ K_γ` (`g_γ` i.i.d. `N(0,1)`, so `E|A_ij|² = 1/n`), and `(s_γ)` a standard free
semicircular family in a tracial `C*`-probability space `(𝒜, τ)`,
`S = Σ_γ K_γ ⊗ s_γ ∈ M_n(ℂ) ⊗ 𝒜 = 𝓜_n`, `τ_n = tr_n ⊗ τ`. Its covariance map is
`Σ_γ K_γ M K_γ = tr_n(M) I_n`, so `S` is a standard semicircular element free from `M_n(ℂ) ⊗ 1`,
and `E_{M_n} = id ⊗ τ`. The free semicircular family, the algebra `M_n(𝒜)` (as `CStarMatrix`),
elements `V ⊗ 1 + Σ_γ K_γ ⊗ s_γ` (`Pencil.op`), and `id ⊗ τ` (`slice`) are the published
`FreeWeaver.Walk` definitions.
-/

noncomputable section

/-- The index set of the GUE basis: diagonal entries, and real and imaginary parts of the entries
above the diagonal. -/
abbrev GueIdx (n : ℕ) : Type :=
  Fin n ⊕ ({p : Fin n × Fin n // p.1 < p.2} ⊕ {p : Fin n × Fin n // p.1 < p.2})

/-- The GUE basis `(K_γ)`: `E_ii/√n`; `(E_ij + E_ji)/√(2n)` and `i(E_ij − E_ji)/√(2n)` for
`i < j`. -/
def gueBasis (n : ℕ) : GueIdx n → Matrix (Fin n) (Fin n) ℂ
  | Sum.inl i => ((Real.sqrt n)⁻¹ : ℂ) • Matrix.single i i 1
  | Sum.inr (Sum.inl p) =>
      ((Real.sqrt (2 * n))⁻¹ : ℂ) • (Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1)
  | Sum.inr (Sum.inr p) =>
      ((Real.sqrt (2 * n))⁻¹ : ℂ) •
        (Complex.I • (Matrix.single p.1.1 p.1.2 1 - Matrix.single p.1.2 p.1.1 1))

/-- The law `GUE(n)` of `A_GUE = Σ_γ g_γ K_γ`, `g_γ` i.i.d. `N(0,1)`: Hermitian, with
`E|A_ij|² = 1/n`. -/
def gue (n : ℕ) : Measure (Fin n → Fin n → ℂ) :=
  (Measure.pi fun _ : GueIdx n => gaussianReal 0 1).map
    fun g i j => (∑ γ, (g γ : ℂ) • gueBasis n γ) i j

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The element `V ⊗ 1 + L S R` of `M_n(𝒜)`, where `S = Σ_γ K_γ ⊗ s_γ` and `V`, `L`, `R` are scalar
matrices: `gueOp 0 1 1 s` is `S`, and `gueOp V 0 1 s` is `V ⊗ 1`. -/
def gueOp {n : ℕ} (V L R : Matrix (Fin n) (Fin n) ℂ) (s : GueIdx n → H →L[ℂ] H) :
    CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) :=
  (Pencil.mk V fun γ => L * gueBasis n γ * R).op s

/-- The block matrix `[[0, I_n + W(aI_n − βA)], [I_n + (aI_n − βA)W, 0]]` of (5.11) for a complex
matrix `A`, `W = diag(w)`. -/
def cBlock {n : ℕ} (β a : ℝ) (w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 0
    (1 + Matrix.diagonal (fun i => (w i : ℂ)) * ((a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (β : ℂ) • A))
    (1 + ((a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (β : ℂ) • A) * Matrix.diagonal (fun i => (w i : ℂ)))
    0

/-- The same block matrix with `A` replaced by the free element `S`, as a pencil:
`[[0, I_n + W(aI_n − βS)], [I_n + (aI_n − βS)W, 0]]`. -/
def blockPencil {n : ℕ} (β a : ℝ) (w : Fin n → ℝ) : Pencil (Fin n ⊕ Fin n) (GueIdx n) :=
  ⟨Matrix.fromBlocks 0
      (1 + (a : ℂ) • Matrix.diagonal (fun i => (w i : ℂ)))
      (1 + (a : ℂ) • Matrix.diagonal (fun i => (w i : ℂ))) 0,
    fun γ => Matrix.fromBlocks 0
      (-(β : ℂ) • (Matrix.diagonal (fun i => (w i : ℂ)) * gueBasis n γ))
      (-(β : ℂ) • (gueBasis n γ * Matrix.diagonal (fun i => (w i : ℂ)))) 0⟩

/-- `X ⪰ c·1` for an element of a real-spectrum algebra: `X` is self-adjoint and its spectrum lies
in `[c, ∞)`. -/
def SpecGe {B : Type*} [Ring B] [StarRing B] [Algebra ℝ B] (X : B) (c : ℝ) : Prop :=
  IsSelfAdjoint X ∧ ∀ x ∈ spectrum ℝ X, c ≤ x

end

end SKHessianAscent


