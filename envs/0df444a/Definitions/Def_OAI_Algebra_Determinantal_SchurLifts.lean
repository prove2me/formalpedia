-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
-- name    : OAI_Algebra_Determinantal_SchurLifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:04:24.318056+00:00
-- url     : https://prove2.me/theorems/985dabff-4556-4fd3-822e-73941f89033e
-- title:
--   Directional derivative matrices, pivot reindexing and kernel-lift systems for bordered matrix families
-- statement:
--   This module assembles, for a family of bordered matrices depending on parameters, the square system that lifts a simple zero of the polar pair of the determinant to a simple zero of a kernel system. Let $\iota$ and $\kappa$ be finite sets and $T$ a complex normed space. Matrices indexed by $\{\ast\}\sqcup\iota$ have the block form
--   $$
--   \begin{pmatrix}a&\beta^{\mathsf T}\\ \gamma&N\end{pmatrix},\qquad a\in\mathbb C,\ \beta,\gamma\in\mathbb C^{\iota},\ N\in\mathbb C^{\iota\times\iota},
--   $$
--   and $\hat p=(1,p)$ denotes the normalized vector of $p\in\mathbb C^{\iota}$.
--
--   1. **Directional derivative matrix.** For a matrix-valued map $y\mapsto\mathcal M(y)$ on $T$ and $x,h\in T$, $\partial_h\mathcal M(x)$ is the matrix whose $(i,j)$ entry is the derivative of $y\mapsto\mathcal M(y)_{ij}$ at $x$ in the direction $h$.
--
--   2. **Remaining kernel equations.** Let $a:T\to\mathbb C$, $\beta,\gamma:T\to\mathbb C^{\iota}$, $N:T\to\mathbb C^{\iota\times\iota}$, let $\mathcal M(y)$ be the bordered matrix with these blocks, let $\psi:\mathbb C\times\mathbb C^{\kappa}\to T$ be a parametrization and $h_k\in T$ ($k\in\kappa$) directions. For $z=\bigl(x,(p,q)\bigr)$ with $x\in\mathbb C\times\mathbb C^{\kappa}$ and $p,q\in\mathbb C^{\iota}$,
--   $$
--   \mathcal R(z)=\Bigl(a(\psi(x))+\beta(\psi(x))^{\mathsf T}p,\ \ \bigl(\hat q^{\mathsf T}\,\partial_{h_k}\mathcal M(\psi(x))\,\hat p\bigr)_{k\in\kappa}\Bigr)\in\mathbb C\times\mathbb C^{\kappa},
--   $$
--   the first entry of $\mathcal M(\psi(x))\,\hat p$ followed by the polar conditions.
--
--   3. **Dot-product functional.** For a finite set $I$ and $v\in\mathbb C^{I}$, the linear functional $f\mapsto\sum_{i\in I}f_iv_i$ on $\mathbb C^{I}$.
--
--   4. **Determinant as a multilinear map.** For a finite set $I$, the determinant of $I\times I$ matrices regarded as a continuous multilinear function of the $|I|$ rows.
--
--   5. **Pivot reindexing.** For $i\in\{0,\dots,n\}$, the bijection $\{\ast\}\sqcup\{0,\dots,n-1\}\to\{0,\dots,n\}$ sending $\ast$ to $i$ and $j$ to the $j$-th element (counting from $0$) of $\{0,\dots,n\}\setminus\{i\}$ in increasing order. Reindexing the rows of an $(n+1)\times(n+1)$ matrix $M$ by the bijection for $r$ and its columns by the bijection for $i$ produces a bordered matrix with corner entry $M_{ri}$ whose lower-right block is the minor of $M$ with row $r$ and column $i$ removed.
--
--   6. **Matrix kernel system.** For a family $\mathcal F:T\to\mathbb C^{(\{\ast\}\sqcup\iota)\times(\{\ast\}\sqcup\iota)}$, let $a,\beta,\gamma,N$ be its corner entry, the rest of its first row, the rest of its first column and its lower-right block. The matrix kernel system is the map
--   $$
--   \mathcal S(z)=\Bigl(\mathcal R(z),\ \bigl(\gamma(\psi(x))+N(\psi(x))\,p,\ \ \beta(\psi(x))^{\mathsf T}+q^{\mathsf T}N(\psi(x))\bigr)\Bigr),\qquad z=\bigl(x,(p,q)\bigr),
--   $$
--   from $(\mathbb C\times\mathbb C^{\kappa})\times(\mathbb C^{\iota}\times\mathbb C^{\iota})$ to itself, with $\mathcal R$ as in item 2 for $\mathcal M=\mathcal F$. Its zeros are exactly the points where $\mathcal F(\psi(x))\,\hat p=0$, $\hat q^{\mathsf T}\mathcal F(\psi(x))=0$ and $\hat q^{\mathsf T}\,\partial_{h_k}\mathcal F(\psi(x))\,\hat p=0$ for all $k$ (the corner entry of the left condition follows from the other equations).
--
--   7. **Kernel point.** For $x\in\mathbb C\times\mathbb C^{\kappa}$, the point $\Bigl(x,\ \bigl(-N(\psi(x))^{-1}\gamma(\psi(x)),\ -\beta(\psi(x))^{\mathsf T}N(\psi(x))^{-1}\bigr)\Bigr)$.
--
--   If the entries of $\mathcal F$ are twice continuously differentiable, $\psi$ is differentiable at $x$, the lower-right block of $\mathcal F(\psi(x))$ is invertible, and $x$ is a simple zero of the polar pair $y\mapsto\bigl(\det\mathcal F(\psi(y)),\ (D\det\mathcal F(\psi(y))\,h_k)_{k}\bigr)$, then the kernel point is a simple zero of the matrix kernel system. For finitely many such zeros of an $(n+1)\times(n+1)$ family, right multiplication by one suitable invertible matrix followed by pivot reindexing (with a common column pivot and a row pivot depending on the zero) makes the lower-right block invertible at each of them; the multilinear determinant gives Jacobi's formula $D\det(M)[H]=\sum_{i,j}\operatorname{adj}(M)_{ji}H_{ij}$, and the dot-product functional is used to find one functional that is nonzero on finitely many nonzero vectors.
--
--   **Formalization Note** The definitions are `PolarAnalysis.Schur.dirMatrix`, `Schur.kernelRemaining`, `PolarAnalysis.dotLinear`, `PolarAnalysis.determinantMultilinear`, `PolarAnalysis.unitSumOptionEquiv` (the bijection between `Unit ⊕ α` and `Option α`, pure plumbing), `PolarAnalysis.pivotEquiv i` (sending the corner index to `i` and `j` to `i.succAbove j`, with `simp` lemmas `pivotEquiv_inl`, `pivotEquiv_inr`), `Schur.matrixKernelSystem` and `Schur.matrixKernelPoint`. Inverses are Mathlib matrix inverses ($0$ for a singular matrix) and derivatives are `fderiv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SchurLifts.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SchurLifts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SmoothInitialForm mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials

namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

noncomputable def dirMatrix (A : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) (x h : T) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  Matrix.of fun i j => fderiv ℂ (fun y => A y i j) x h

noncomputable def kernelRemaining
    (a : T → ℂ) (β γ : T → ι → ℂ) (E : T → Matrix ι ι ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (z : (ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) : ℂ × (κ → ℂ) :=
  (a (ψ z.1) + β (ψ z.1) ⬝ᵥ z.2.1,
    fun i => normalized z.2.2 ⬝ᵥ
      (dirMatrix (fun y => block (a y) (β y) (γ y) (E y)) (ψ z.1) (h i)
        *ᵥ normalized z.2.1))

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype σ]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Finite J]

noncomputable def dotLinear (v : I → ℂ) : (I → ℂ) →ₗ[ℂ] ℂ where
  toFun f := f ⬝ᵥ v
  map_add' := by intros; apply add_dotProduct
  map_smul' := by intros; simp [smul_dotProduct]

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def determinantMultilinear :
    ContinuousMultilinearMap ℂ (fun _ : I => I → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix
open scoped Topology
variable {V E W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {I J : Type*} [Fintype I] [DecidableEq I] [Finite J]

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix

 def unitSumOptionEquiv (α : Type*) : Unit ⊕ α ≃ Option α where
  toFun := Sum.elim (fun _ => none) some
  invFun := fun o => o.elim (Sum.inl ()) Sum.inr
  left_inv := by
    rintro (u|a)
    · cases u; rfl
    · rfl
  right_inv := by rintro (_|a) <;> rfl

noncomputable def pivotEquiv {n : ℕ} (i : Fin (n+1)) : Unit ⊕ Fin n ≃ Fin (n+1) :=
  (unitSumOptionEquiv (Fin n)).trans (finSuccEquiv' i).symm

@[simp] theorem pivotEquiv_inl {n : ℕ} (i : Fin (n+1)) :
    pivotEquiv i (Sum.inl ()) = i := rfl
@[simp] theorem pivotEquiv_inr {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    pivotEquiv i (Sum.inr j) = i.succAbove j := rfl

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

noncomputable def matrixKernelSystem
    (F : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (z : (ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) :=
  (kernelRemaining (fun y => F y (.inl ()) (.inl ()))
      (fun y j => F y (.inl ()) (.inr j)) (fun y i => F y (.inr i) (.inl ()))
      (fun y => (F y).submatrix Sum.inr Sum.inr) ψ h z,
    auxiliary (fun y j => F (ψ y) (.inl ()) (.inr j))
      (fun y i => F (ψ y) (.inr i) (.inl ()))
      (fun y => (F (ψ y)).submatrix Sum.inr Sum.inr) z)

noncomputable def matrixKernelPoint
    (F : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (x : ℂ × (κ → ℂ)) :=
  (x, graphKernels (fun y j => F (ψ y) (.inl ()) (.inr j))
      (fun y i => F (ψ y) (.inr i) (.inl ()))
      (fun y => (F (ψ y)).submatrix Sum.inr Sum.inr) x)

end PermanentBorder.PolarAnalysis.Schur

end OAI


