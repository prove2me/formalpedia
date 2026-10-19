-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
-- name    : OAI_Probability_Subsphere_Regression_Gram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:29:51.283368+00:00
-- url     : https://prove2.me/theorems/8faf39d4-995e-4c75-8dca-8b023c749aae
-- title:
--   Gram–Schmidt coefficient matrix and inverse-volume replica weights
-- statement:
--   Throughout, $E$ is a real inner product space. For vectors $v_0,\dots,v_{n-1}\in E$ let $u_0,\dots,u_{n-1}$ be their unnormalized Gram–Schmidt orthogonalization,
--
--   $$
--   u_i=v_i-\sum_{k<i}\frac{\langle u_k,v_i\rangle}{\|u_k\|^2}\,u_k ,
--   $$
--
--   with the convention $0/0=0$ (a term with $u_k=0$ vanishes). Thus $\|u_i\|$ is the distance from $v_i$ to the linear span of $v_0,\dots,v_{i-1}$.
--
--   1. **Gram–Schmidt coefficient matrix.** For $n\in\mathbb{N}$ and $v\in E^n$, $R(v)$ is the $n\times n$ real matrix
--   $$R(v)_{ij}=\begin{cases}1, & i=j,\\ \langle u_i,v_j\rangle/\|u_i\|^2, & i<j,\\ 0, & i>j,\end{cases}$$
--   a unit upper triangular matrix whose row $i$ vanishes off the diagonal when $u_i=0$. It records the coefficients of $v_j=\sum_{i\le j}R(v)_{ij}\,u_i$, the triangular factor relating the Gram matrix of $v$ to the diagonal Gram matrix of $u$.
--   2. **Replica weight.** For an exponent $m\in\mathbb{N}$, a base point $p\in E$ and $v\in E^n$, let $u_0(p),\dots,u_{n-1}(p)$ be the Gram–Schmidt vectors of the translated family $v_0-p,\dots,v_{n-1}-p$, and set
--   $$W_{m,p}(v)=\prod_{i=0}^{n-1}\|u_i(p)\|^{-m}\in[0,\infty].$$
--   Here $\|u_i(p)\|$ is the distance from $v_i$ to the affine span of $p,v_0,\dots,v_{i-1}$, so for affinely independent points $W_{m,p}(v)$ is the $(-m)$-th power of the $n$-dimensional volume of the parallelepiped spanned by $v_0-p,\dots,v_{n-1}-p$.
--   3. **Replica constant.** For a measure $\nu$ on $E$ (for a $\sigma$-algebra on $E$), $a\in\mathbb{R}$ and $m\in\mathbb{N}$,
--   $$K(\nu,a,m)=\nu(E)+3^{\dim E}\,4^{a}\,2^{m+1}\in[0,\infty].$$
--
--   The weight $W_{m,p}$ is integrated against $n$ independent samples ("replicas") from a measure $\nu$ on $E$, and $K(\nu,a,m)$ is the per-replica constant of the resulting bound when $\nu$ satisfies a local mass bound with exponent $a$; such inverse-volume moments drive the moment estimates for observation laws in the regression lower bound.
--
--   **Formalization Note** The objects are `gsUpper n v`, `replicaWeight m p v` and `replicaConstant ν a m`, built on Mathlib's `gramSchmidt ℝ`. Each factor of `replicaWeight` is `ENNReal.ofReal (‖u_i‖⁻¹ ^ m)` with Lean's real inverse, for which $0^{-1}=0$: a degenerate factor $u_i(p)=0$ contributes $0$ when $m\ge1$ and $1$ when $m=0$, not $+\infty$. In `replicaConstant`, $\dim E$ is `Module.finrank ℝ E` (which is $0$ for an infinite-dimensional space) and $4^a$ is a real power. Only the inner-product structure (and, for the constant, the measurable structure) of $E$ is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gram.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Gram.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
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

section PiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
end PiLast

section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def replicaWeight (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal ((‖gramSchmidt ℝ (fun j => v j - p) i‖)⁻¹ ^ m)

def replicaConstant (ν : Measure E) (a : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ν Set.univ + ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ E * (4 : ℝ) ^ a) *
    (2 : ℝ≥0∞) ^ (m+1)

end ReplicaMoments
section AePiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
end AePiLast

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SubsphereRegression

end

end OAI


