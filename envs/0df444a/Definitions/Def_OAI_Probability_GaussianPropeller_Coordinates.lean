-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
-- name    : OAI_Probability_GaussianPropeller_Coordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:39:09.472227+00:00
-- url     : https://prove2.me/theorems/8337c4c0-6f37-46ba-87fb-124679744389
-- title:
--   Splitting off the first coordinate
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Splitting and joining.** The maps between $\mathbb R^{n+1}$ and $\mathbb R\times\mathbb R^n$,
--   $$
--   x\mapsto\bigl(x_0,(x_1,\dots,x_n)\bigr),\qquad (t,y)\mapsto(t,y_1,\dots,y_n),
--   $$
--   which are mutually inverse and continuous. Together they form a measurable equivalence, used to write Gaussian integrals over cones around the first axis as iterated integrals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Coordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Coordinates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianPropeller mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Coords
abbrev CS (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def split (n : ℕ) (x : CS (n+1)) : ℝ × CS n :=
  (x 0, WithLp.toLp 2 (fun i => x i.succ))
noncomputable def join (n : ℕ) (y : ℝ × CS n) : CS (n+1) :=
  WithLp.toLp 2 (Fin.cons y.1 y.2.ofLp)

lemma split_join (n : ℕ) (y : ℝ × CS n) : split n (join n y)=y := by
  rcases y with ⟨s,y⟩
  simp [split,join]

lemma join_split (n : ℕ) (x : CS (n+1)) : join n (split n x)=x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [join,split]

lemma continuous_split (n : ℕ) : Continuous (split n) := by
  unfold split
  apply Continuous.prodMk (by fun_prop)
  exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)

lemma continuous_join (n : ℕ) : Continuous (join n) := by
  unfold join
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero, Fin.cons_succ]
  · fun_prop
  · fun_prop

noncomputable def splitEquiv (n : ℕ) : CS (n+1) ≃ᵐ ℝ × CS n where
  toFun := split n
  invFun := join n
  left_inv := join_split n
  right_inv := split_join n
  measurable_toFun := (continuous_split n).measurable
  measurable_invFun := (continuous_join n).measurable

end GaussianPropeller.Coords

end OAI


