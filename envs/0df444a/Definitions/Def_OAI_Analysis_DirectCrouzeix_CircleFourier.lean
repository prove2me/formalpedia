-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
-- name    : OAI_Analysis_DirectCrouzeix_CircleFourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:30:29.141156+00:00
-- url     : https://prove2.me/theorems/707775a2-47cc-4663-8202-5627f857aa19
-- title:
--   The circle $\mathbb{R}/\mathbb{Z}$ with Haar measure and continuous linear maps on matrix spaces
-- statement:
--   Throughout, $\|M\|_{\mathrm{HS}}^{2}=\sum_{i,j}|M_{ij}|^{2}$ denotes the squared Hilbert–Schmidt norm of a complex matrix and $M^{*}$ its conjugate transpose. The module introduces:
--
--   1. **The boundary circle and its measure.** The circle $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ with its normalized Haar measure $dt$, of total mass $1$ (Lebesgue measure on $[0,1)$ transported to $\mathbb{T}$). For an integrable function $f$ on $\mathbb{T}$ with values in a complex Banach space, its Fourier coefficients are
--   $$
--   \widehat f(k)=\int_{\mathbb{T}}e^{-2\pi ikt}f(t)\,dt,\qquad k\in\mathbb{Z}.
--   $$
--
--   2. **Entry-vector map.** For finite index sets $I,J$, the complex-linear map $\operatorname{vec}:\mathbb{C}^{I\times J}\to\ell^{2}(I\times J)$, $\operatorname{vec}(M)_{(i,j)}=M_{ij}$, from matrices to the Euclidean space indexed by $I\times J$, packaged as a continuous linear map.
--
--   3. **Compression map.** For $n,m\in\mathbb{N}$ and $X,Y\in\mathbb{C}^{n\times m}$, the continuous complex-linear map
--   $$
--   M_n(\mathbb{C})\to M_m(\mathbb{C}),\qquad R\mapsto Y^{*}RX .
--   $$
--
--   4. **Conjugate transpose.** For finite index sets $I,J$, the map $\mathbb{C}^{I\times J}\to\mathbb{C}^{J\times I}$, $M\mapsto M^{*}$, packaged as a continuous real-linear map (it is conjugate-linear over $\mathbb{C}$).
--
--   Each map comes with its evaluation rule as a simplification lemma.
--
--   Continuous linear maps commute with Bochner integrals, hence with Fourier coefficients. Packaging these operations in this way yields, for continuous matrix-valued $f$ and $R$ on $\mathbb{T}$, the matrix Parseval identity $\sum_{k\in\mathbb{Z}}\|\widehat f(k)\|_{\mathrm{HS}}^{2}=\int_{\mathbb{T}}\|f(t)\|_{\mathrm{HS}}^{2}\,dt$, the compression rule $\widehat{Y^{*}RX}(k)=Y^{*}\,\widehat R(k)\,X$ and the reflection rule $\widehat{f^{*}}(k)=\widehat f(-k)^{*}$, which convert boundary integrals of matrix-valued functions into sums over Fourier coefficients.
--
--   **Formalization Note** `BoundaryCircle` is `AddCircle (1 : ℝ)` and `circleMeasure` is `AddCircle.haarAddCircle`. The maps `hsCLM`, `compressionCLM X Y` and `conjugateTransposeCLM` are obtained from linear maps by `LinearMap.toContinuousLinearMap` (continuity is automatic in finite dimension); the last one is a continuous map over the real scalars. The evaluation rules are the definitional lemmas `hsCLM_apply`, `compressionCLM_apply` and `conjugateTransposeCLM_apply`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/CircleFourier.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/CircleFourier.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness

namespace OAI

universe u_47 u_48 u_49 u_50 u_51 u_52 u_53 u_54 u_55 u_56 u_57 u_58 u_59 u_60 u_61 u_62 u_63 u_64
  u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

abbrev BoundaryCircle := AddCircle (1 : ℝ)

abbrev circleMeasure : Measure BoundaryCircle := AddCircle.haarAddCircle

def hsCLM {ι : Type u_57} {κ : Type u_58} [Fintype ι] [Fintype κ] :
    Matrix ι κ ℂ →L[ℂ] EuclideanSpace ℂ (ι × κ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hsVector
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }

@[simp] theorem hsCLM_apply {ι : Type u_59} {κ : Type u_60} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : hsCLM A = hsVector A := rfl

def compressionCLM {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin m) (Fin m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun R => Yᴴ * R * X
      map_add' := by intros; simp [Matrix.mul_add,Matrix.add_mul]
      map_smul' := by intros; simp [Matrix.mul_smul,Matrix.smul_mul] }

@[simp] theorem compressionCLM_apply {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ)
    (R : Matrix (Fin n) (Fin n) ℂ) : compressionCLM X Y R = Yᴴ * R * X := rfl

def conjugateTransposeCLM {ι : Type u_67} {κ : Type u_68} [Fintype ι] [Fintype κ] :
    Matrix ι κ ℂ →L[ℝ] Matrix κ ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := by intros; simp
      map_smul' := by intros; simp }

@[simp] theorem conjugateTransposeCLM_apply {ι : Type u_69} {κ : Type u_70} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : conjugateTransposeCLM A = Aᴴ := rfl

end DirectCrouzeix

end

end OAI


