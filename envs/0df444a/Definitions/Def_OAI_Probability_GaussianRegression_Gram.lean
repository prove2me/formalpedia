-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Gram
-- name    : OAI_Probability_GaussianRegression_Gram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:03:24.253029+00:00
-- url     : https://prove2.me/theorems/8ab55226-d095-4dcb-a49b-8cff36b02ed6
-- title:
--   Upper unitriangular coefficient matrix of Gram–Schmidt orthogonalization
-- statement:
--   Let $E$ be a real inner product space, let $n\in\mathbb{N}$, and let $v=(v_0,\dots,v_{n-1})\in E^{n}$. The (unnormalized) Gram–Schmidt vectors $u_0,\dots,u_{n-1}$ of $v$ are defined recursively by
--   $$u_j=v_j-\sum_{i<j}\frac{\langle u_i,v_j\rangle}{\|u_i\|^{2}}\,u_i ,$$
--   where a term with $u_i=0$ is $0$. The file defines the $n\times n$ real matrix $R(v)$ with entries
--   $$R(v)_{ij}=\begin{cases}1, & i=j,\\ \dfrac{\langle u_i,v_j\rangle}{\|u_i\|^{2}}, & i<j,\\ 0, & i>j,\end{cases}$$
--   with the convention that the fraction is $0$ when $u_i=0$.
--
--   The matrix $R(v)$ is upper unitriangular, hence has determinant $1$, and its $j$-th column lists the coefficients of $v_j$ in the orthogonal family: $v_j=\sum_i R(v)_{ij}\,u_i$. Writing the Gram matrix of $v$ as $R(v)^{\mathsf T}\,G(u)\,R(v)$, where the Gram matrix $G(u)$ of the orthogonal family is diagonal, gives
--   $$\det G(v)=\prod_{i=0}^{n-1}\|u_i\|^{2}.$$
--   This is how squared volumes of parallelotopes are expressed as products of distances of each vector to the span of the previous ones.
--
--   **Formalization Note** The Lean name is `gsUpper n v`, a `Matrix (Fin n) (Fin n) ℝ`; the Gram–Schmidt vectors are Mathlib's `gramSchmidt ℝ v`, and the convention for $u_i=0$ is Lean's $x/0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Gram.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Gram.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets

namespace OAI

/-!
Gram determinants, orthogonal distances, and product integration.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
variable (n : ℕ)
def gsUpper (v : Fin n → E) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if i = j then 1 else 0) +
    if i < j then ⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2 else 0

end GramFactorization

section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
variable [MeasurableSpace E] [BorelSpace E]
end GramDistances

variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
end NoiselessRegression

end

end OAI


