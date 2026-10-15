-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
-- name    : OAI_Probability_GaussianRegression_ReplicaMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:03:58.180603+00:00
-- url     : https://prove2.me/theorems/bf93753a-998f-42f1-9ede-e10af7c02304
-- title:
--   Inverse Gram–Schmidt weight of a replica configuration and its moment constant
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra. For a family $w=(w_0,\dots,w_{n-1})\in E^{n}$ write $u_0(w),\dots,u_{n-1}(w)$ for its Gram–Schmidt vectors,
--   $$u_j(w)=w_j-\sum_{i<j}\frac{\langle u_i(w),w_j\rangle}{\|u_i(w)\|^{2}}\,u_i(w)\qquad(\text{terms with }u_i(w)=0\text{ omitted}).$$
--   The file defines two quantities with values in $[0,\infty]$.
--
--   1. **Replica weight.** For $m\in\mathbb{N}$, a base point $p\in E$ and $v=(v_0,\dots,v_{n-1})\in E^{n}$,
--      $$W_{m,p}(v)=\prod_{i=0}^{n-1}\big\|u_i(v_0-p,\dots,v_{n-1}-p)\big\|^{-m},$$
--      with the convention $0^{-1}=0$, so that a vanishing Gram–Schmidt vector contributes the factor $0$ when $m\ge1$ (and $1$ when $m=0$). Geometrically, $\|u_i(v-p)\|$ is the distance from $v_i$ to the affine hull of $p,v_0,\dots,v_{i-1}$; for affinely independent $p,v_0,\dots,v_{n-1}$, $W_{m,p}(v)$ is the $(-m)$-th power of the $n$-dimensional volume of the parallelotope spanned by $v_0-p,\dots,v_{n-1}-p$.
--
--   2. **Replica constant.** For a measure $\nu$ on $E$, $a\in\mathbb{R}$ and $m\in\mathbb{N}$,
--      $$K(\nu,a,m)=\nu(E)+3^{\dim E}\,4^{a}\,2^{m+1}.$$
--
--   Independent samples ("replicas") from a measure that does not concentrate near low-dimensional affine subspaces rarely span a small volume. This is quantified by the moment bound $\int W_{m,p}\,d\nu^{\otimes n}\le K(\nu,a,m)^{n}$, valid for finite measures $\nu$ supported in the closed unit ball with a local mass bound of exponent $a\ge n+m$; it controls moments of noise-smoothed densities of Gaussian projections of $\nu$.
--
--   **Formalization Note** The Lean names are `replicaWeight m p v`, a product over `Fin n` of `ENNReal.ofReal` of the $m$-th power of the real inverse of the Gram–Schmidt norm (Lean's convention $0^{-1}=0$), and `replicaConstant ν a m`, in which the real number $3^{\dim E}4^{a}$ (real power $4^{a}$) is embedded by `ENNReal.ofReal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/ReplicaMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/ReplicaMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram

namespace OAI

/-!
Inverse Gram moments and almost-everywhere replica independence.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

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

end NoiselessRegression

end

end OAI


