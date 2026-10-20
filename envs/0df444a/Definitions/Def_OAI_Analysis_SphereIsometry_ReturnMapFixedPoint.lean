-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapFixedPoint
-- name    : OAI_Analysis_SphereIsometry_ReturnMapFixedPoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:14:08.661846+00:00
-- url     : https://prove2.me/theorems/4ac0b1bc-3f43-4f0b-a801-4ced1a12e0c9
-- title:
--   A fixed point of the return map
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $C$ be a nonempty closed bounded convex subset of a Banach space and $g:C\to C$ continuous.
--
--   1. **Return-estimate fixed point.** Suppose scalar functions $p,s,u,r$ on $C$ take values in $[1-t,1+t]$ with $0<t<1$, satisfy $s=p+M$ and $r=u+M$ for some $M>0$, and $g$ obeys
--   $$
--   \|g(v)-g(v')\|\le\frac{u(v)p(v)}{r(v)s(v)}\|v-v'\|+\frac{2|u(v)-u(v')|}{r(v)}+\frac{2u(v)|p(v)-p(v')|}{r(v)s(v)} .
--   $$
--   Then $g$ has a fixed point. Scalar binning gives $\chi(g(H))\le(1-\frac M{1+t})^2\chi(H)$, and the condensing fixed point theorem applies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ReturnMapFixedPoint.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ReturnMapFixedPoint.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TingleySphereIsometry mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_TingleySphereIsometry
import Definitions.Def_OAI_Analysis_SphereIsometry_Basic
import Definitions.Def_OAI_Analysis_SphereIsometry_UnitRepresentatives
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraRealLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraNormed
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraSphere
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectSequence
import Definitions.Def_OAI_Analysis_SphereIsometry_SphereCompletion
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectAttainment
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialContact
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMap
import Definitions.Def_OAI_Analysis_SphereIsometry_Supports
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveConvexFace
import Definitions.Def_OAI_Analysis_SphereIsometry_ExtremalPropagation
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveScheduling
import Definitions.Def_OAI_Analysis_SphereIsometry_InvariantConvexSet
import Definitions.Def_OAI_Analysis_SphereIsometry_AlignmentSet
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapEstimate
import Definitions.Def_OAI_Analysis_SphereIsometry_DiameterBounds
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiBasic
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapBounds
import Definitions.Def_OAI_Analysis_SphereIsometry_ScalarBins
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapNoncompactness
import Definitions.Def_OAI_Analysis_SphereIsometry_ProbabilitySimplex
import Definitions.Def_OAI_Analysis_SphereIsometry_SimplexLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_FiniteComplex
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricFlags
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionData
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricBasic
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricSupport
import Definitions.Def_OAI_Analysis_SphereIsometry_ConvexDiameter
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricMesh
import Definitions.Def_OAI_Analysis_SphereIsometry_IteratedPoints
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerFacet
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerBoundary
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricRestriction
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionRestriction
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricZero
import Definitions.Def_OAI_Analysis_SphereIsometry_Sperner
import Definitions.Def_OAI_Analysis_SphereIsometry_SimplexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactApproximation
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactConvexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CoefficientBins
import Definitions.Def_OAI_Analysis_SphereIsometry_ConvexCoverRegroup
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiConvexHull
import Definitions.Def_OAI_Analysis_SphereIsometry_CondensingIteration
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiTotalBounded
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiNested
import Definitions.Def_OAI_Analysis_SphereIsometry_CondensingFixedPoint

namespace OAI

/-!
# A fixed point from the return map's radius estimates

The finite-bin noncompactness estimate and the proved condensing fixed-point
theorem discharge the analytic step from the elementary geometric data.
Continuity is needed only on the actual invariant closed convex set.
-/

namespace Tingley

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [CompleteSpace X]

/-- The radius bounds and two-point estimate imply an actual fixed point.
The hypotheses contain neither a noncompactness estimate nor a fixed-point
principle: both are supplied by the preceding constructive proofs. -/
theorem exists_fixedPoint_of_return_estimate
    {C : Set X} {g : X → X} {p s u r : X → ℝ} {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCb : Bornology.IsBounded C) (hCconvex : Convex ℝ C)
    (hg : ContinuousOn g C) (hgC : Set.MapsTo g C C)
    (hbounds : ∀ v ∈ C,
      (1 - t ≤ p v ∧ p v ≤ 1 + t) ∧
      (1 - t ≤ s v ∧ s v ≤ 1 + t) ∧
      (1 - t ≤ u v ∧ u v ≤ 1 + t) ∧
      (1 - t ≤ r v ∧ r v ≤ 1 + t))
    (hs : ∀ v ∈ C, s v = p v + M)
    (hr : ∀ v ∈ C, r v = u v + M)
    (hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤
        (u v * p v / (r v * s v)) * dist v v' +
        2 * |u v - u v'| / r v +
        2 * u v * |p v - p v'| / (r v * s v)) :
    ∃ x ∈ C, g x = x := by
  have hfactor := return_contraction_factor_mem_Ico ht0 ht1 hM hCne
    (fun v hv => (hbounds v hv).1.1)
    (fun v hv => (hbounds v hv).2.1.2) hs
  apply exists_fixedPoint_of_kuratowski_contraction hCne hCclosed hCb
    hCconvex hg hgC hfactor.1 hfactor.2
  intro H hHC
  exact chi_return_image_le ht0 ht1 hM hCne hCb hgC hbounds hs hr hpair hHC

end Tingley

end OAI


