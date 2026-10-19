-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
-- name    : OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T04:05:53.418994+00:00
-- url     : https://prove2.me/theorems/5790df94-6841-4d99-aebf-a2c1aa94307d
-- title:
--   Arrays over $\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$ as tensors of augmented vectors, and affine row evaluation
-- statement:
--   This file gives a tensor-product presentation of the real arrays that appear in the real tensor criterion for point configurations, and the row evaluation attached to each point.
--
--   Fix $d\in\mathbb{N}$ and use the augmented index set $\{0,1,\dots,d\}$, where $0$ is an extra index for the constant term. A real array is a matrix $(P_{\alpha\beta})_{\alpha,\beta\in\{0,\dots,d\}}$ with entries in $\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$, the tensor product of $\mathbb{R}$ with itself over $\mathbb{Q}$.
--
--   1. **Augmented vectors.** $\mathbb{R}^{1+d}$ denotes the space of real functions $w$ on $\{0,1,\dots,d\}$, written $w=(w_0,w_1,\dots,w_d)$.
--   2. **Array presentation.** The $\mathbb{Q}$-linear isomorphism
--   $$\Theta:\ \mathbb{R}^{1+d}\otimes_{\mathbb{Q}}\mathbb{R}^{1+d}\ \xrightarrow{\ \sim\ }\ \{\text{real arrays}\},\qquad \Theta(w\otimes z)_{\alpha\beta}=w_\alpha\otimes z_\beta ,$$
--   obtained by distributing the tensor product over the two finite products; the formula on pure tensors is recorded as a simplification rule.
--   3. **Row evaluation.** For points $a_1,\dots,a_s\in\mathbb{R}^d$ with coordinates $a_{ij}$ and an index $i$, $\rho_i:\mathbb{R}^{1+d}\to\mathbb{R}$ is the $\mathbb{Q}$-linear map
--   $$\rho_i(w)=\sum_{\alpha=0}^{d}\tilde a_i(\alpha)\,w_\alpha=w_0+\sum_{j=1}^{d}a_{ij}w_j ,$$
--   where $\tilde a_i=(1,a_{i1},\dots,a_{id})$ is the augmented point.
--
--   Under $\Theta$, the array evaluation of the real criterion becomes a tensor square of the row evaluation: if $E_i(P)=\sum_{\alpha,\beta}(\tilde a_i(\alpha)\otimes1)\,P_{\alpha\beta}\,(1\otimes\tilde a_i(\beta))$, then $E_i(\Theta(t))=(\rho_i\otimes\rho_i)(t)$ for every $t\in\mathbb{R}^{1+d}\otimes_{\mathbb{Q}}\mathbb{R}^{1+d}$. Writing a symmetrized tensor as $\sum_{j,l}C_{jl}\,w_j\otimes w_l$ with finitely many vectors $w_1,\dots,w_k\in\mathbb{R}^{1+d}$ and a symmetric rational matrix $C$, this turns a solution of the real criterion into a statement about the lattice kernels $\{\gamma\in\mathbb{Z}^k:\rho_i(\sum_j\gamma_jw_j)=0\}$, which is how the criterion is moved to the lattice setting.
--
--   **Formalization Note** `AffineVector d` is `Option (Fin d) → ℝ`, with `none` as the index $0$. `affineArray : (AffineVector d ⊗[ℚ] AffineVector d) ≃ₗ[ℚ] RealArray d` is built from `TensorProduct.piLeft` and `TensorProduct.piRight`, with simp lemma `affineArray_tmul`; `rowEvaluation a i` uses `realAugmented` and is declared as a $\mathbb{Q}$-linear map. The identities quoted above are proved separately, and the remaining sections of the file are empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorPresentation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/TensorPresentation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyTransitive mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive

-- TensorProduct.inductionOn (the Lean 4.34 two-case eliminator) is already backported in the imported
-- module OAI.Combinatorics.EuclideanRamsey.TensorDescent.

namespace OAI

universe uVector

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

open scoped TensorProduct RealInnerProductSpace
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open scoped TensorProduct BigOperators

abbrev AffineVector (d : ℕ) := Option (Fin d) → ℝ

def affineArray {d : ℕ} :
    (AffineVector d ⊗[ℚ] AffineVector d) ≃ₗ[ℚ] RealArray d :=
  (TensorProduct.piLeft ℚ (AffineVector d) (fun _ : Option (Fin d) => ℝ)).trans
    (LinearEquiv.piCongrRight (fun _ => TensorProduct.piRight ℚ ℚ ℝ (fun _ : Option (Fin d) => ℝ)))

@[simp] lemma affineArray_tmul {d : ℕ} (w z : AffineVector d) (α β : Option (Fin d)) :
    affineArray (w ⊗ₜ[ℚ] z) α β = w α ⊗ₜ[ℚ] z β := by
  rfl

def rowEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : AffineVector d →ₗ[ℚ] ℝ where
  toFun w := ∑ α,realAugmented a i α * w α
  map_add' x y := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' q x := by
    simp only [Pi.smul_apply,RingHom.id_apply,Rat.smul_def,mul_left_comm,Finset.mul_sum]

end EuclideanRamsey

open scoped TensorProduct BigOperators
namespace EuclideanRamsey

end EuclideanRamsey

open scoped TensorProduct
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open scoped TensorProduct

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

end EuclideanRamsey

end

end OAI


