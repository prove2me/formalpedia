-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
-- name    : OAI_Probability_EntangledGames_RelativeEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:08:33.204547+00:00
-- url     : https://prove2.me/theorems/da9c87ed-b1d1-4150-af8b-2fc8cc80fa3d
-- title:
--   Born weights as real-linear functionals of one local operator
-- statement:
--   Let $m,n$ be finite index sets. A matrix $C\in\mathbb{C}^{m\times n}$ encodes the bipartite vector $\operatorname{vec}(C)\in\mathbb{C}^m\otimes\mathbb{C}^n$ with $\operatorname{vec}(C)_{(i,j)}=C_{ij}$, and for $A\in\mathbb{C}^{m\times m}$ and $B\in\mathbb{C}^{n\times n}$ its Born weight is
--   $$\operatorname{pr}(C;A,B)=\operatorname{Re}\bigl\langle\operatorname{vec}(C),(A\otimes B)\operatorname{vec}(C)\bigr\rangle ,$$
--   where $\otimes$ is the Kronecker product.
--
--   The file shows that $\operatorname{pr}$ is homogeneous for real scalars in each operator, $\operatorname{pr}(C;rA,B)=r\operatorname{pr}(C;A,B)$ and $\operatorname{pr}(C;A,rB)=r\operatorname{pr}(C;A,B)$ for $r\in\mathbb{R}$, and, together with additivity in each operator, packages it as two $\mathbb{R}$-linear functionals on the real vector spaces $\mathbb{C}^{m\times m}$ and $\mathbb{C}^{n\times n}$:
--
--   1. **Left functional.** For fixed $C$ and $B$: $\Lambda^{\mathrm L}_{C,B}:\mathbb{C}^{m\times m}\to\mathbb{R}$, $A\mapsto\operatorname{pr}(C;A,B)$.
--   2. **Right functional.** For fixed $C$ and $A$: $\Lambda^{\mathrm R}_{C,A}:\mathbb{C}^{n\times n}\to\mathbb{R}$, $B\mapsto\operatorname{pr}(C;A,B)$.
--
--   Viewing a Born weight as a linear functional of one player's operator, with the other player's operator frozen, lets general facts about linear functionals (commuting with averages of matrix-valued functions, entropy inequalities for functionals evaluated on the operator entropy $X\log X$) be applied to one side of a bipartite strategy at a time.
--
--   **Formalization Note** The functionals are `probLeft C B : Matrix m m ℂ →ₗ[ℝ] ℝ` and `probRight C A : Matrix n n ℂ →ₗ[ℝ] ℝ`; additivity comes from `prob_add_left` and `prob_add_right`, homogeneity from `prob_smul_left` and `prob_smul_right`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/RelativeEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/RelativeEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability

namespace OAI

universe u_ι u_α u_β u_n u_m

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ThresholdParallelRepetition
namespace ScalarEntropy

open FiniteProbability
variable {α : Type u_α} {β : Type u_β} [Fintype α] [Fintype β]

end ScalarEntropy
namespace OperatorEntropy
open Resolvent QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

variable {m : Type u_m} [Fintype m] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
lemma prob_smul_left (C : Matrix m n ℂ) (r : ℝ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (r • A) B = r*prob C A B := by
  simp [prob, eval_eq_trace, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul]
omit [DecidableEq n] [DecidableEq m] in
lemma prob_smul_right (C : Matrix m n ℂ) (r : ℝ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C A (r • B) = r*prob C A B := by
  simp [prob, eval_eq_trace, Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul]

def probLeft (C : Matrix m n ℂ) (B : Matrix n n ℂ) : Matrix m m ℂ →ₗ[ℝ] ℝ where
  toFun A := prob C A B
  map_add' A A' := prob_add_left C A A' B
  map_smul' r A := prob_smul_left C r A B

def probRight (C : Matrix m n ℂ) (A : Matrix m m ℂ) : Matrix n n ℂ →ₗ[ℝ] ℝ where
  toFun B := prob C A B
  map_add' B B' := prob_add_right C A B B'
  map_smul' r B := prob_smul_right C r A B

end OperatorEntropy
end ThresholdParallelRepetition

end

end OAI


