-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ChordContradiction
-- name    : OAI_Analysis_SphereIsometry_ChordContradiction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:24:18.542848+00:00
-- url     : https://prove2.me/theorems/2f55ab50-938b-4dfd-8fb1-bd5ab2e17abc
-- title:
--   Aligned configurations cannot exist
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $C$ be an aligned configuration for $f$ with defect bound $M>0$ at $(y,t)$, $0<t<1$: $x=ty+pv$, $z=ty-rv$, $f(x)=tf(y)+sw$, $f(z)=tf(y)-uw$ with $s-p=r-u=M$, $d=p+r\le2$, $A=p/d$, $B=u/d$.
--
--   1. **Impossibility.** No aligned configuration exists for a sphere isometry with defect bound $M>0$ at $t\in(0,1)$:
--   $$
--   \text{AlignedConfiguration}(f,y,t,M)=\varnothing .
--   $$
--   The large-ratio regime is excluded for the configuration and its inverse. This gives $A,B\le1-t$, and the secant bounds give $1-t\le dA(1-B)$ and $1-t\le dB(1-A)$. The small-chord argument then contradicts the isometry property.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ChordContradiction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ChordContradiction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_AlignedConfiguration
import Definitions.Def_OAI_Analysis_SphereIsometry_Alignment
import Definitions.Def_OAI_Analysis_SphereIsometry_ChordSecant
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialPerturbation
import Definitions.Def_OAI_Analysis_SphereIsometry_LargeChord
import Definitions.Def_OAI_Analysis_SphereIsometry_SmallChord

namespace OAI

/-! A genuinely aligned positive-defect configuration is impossible. -/

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}

/-- The global bound and the actual aligned chords contradict one another.
The two small-regime inequalities are proved from the original and literal
inverse configurations; neither is an additional caller premise. -/
theorem alignedConfiguration_impossible (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (C : AlignedConfiguration f y t M) : False := by
  obtain ⟨hA, hB⟩ := C.small_ratios hM ht hb
  have heA := C.small_secant_product hM ht hb hB
  have heB : 1 - t ≤ C.d * C.B * (1 - C.A) := by
    have hA' : C.inverse.B ≤ 1 - t := by
      simpa only [AlignedConfiguration.inverse_B] using hA
    have h := C.inverse.small_secant_product hM ht hb.symm hA'
    simpa only [AlignedConfiguration.inverse_d, AlignedConfiguration.inverse_A,
      AlignedConfiguration.inverse_B] using h
  have hx : ‖t • (y : X) + C.p • (C.v : X)‖ = 1 := by
    rw [← C.x_eq]
    exact C.x.property
  have hfx : ‖t • (f y : Y) + C.s • (C.w : Y)‖ = 1 := by
    rw [← C.fx_eq]
    exact (f C.x).property
  have hleft : (1 - t) • (y : X) + C.r • (C.v : X) = (y : X) - (C.z : X) := by
    rw [C.z_eq]
    module
  have hright : (1 - t) • (f y : Y) + C.u • (C.w : Y) =
      (f y : Y) - (f C.z : Y) := by
    rw [C.fz_eq]
    module
  have hiso : ‖(1 - t) • (y : X) + C.r • (C.v : X)‖ =
      ‖(1 - t) • (f y : Y) + C.u • (C.w : Y)‖ := by
    rw [hleft, hright]
    exact (sphere_norm_sub f y C.z).symm
  exact smallChord_contradiction (y : X) (C.v : X) (f y : Y) (C.w : Y)
    (t := t) (ε := 1 - t) (d := C.d) (A := C.A) (B := C.B)
    ht.2 rfl C.p_pos C.r_pos C.s_pos C.u_pos rfl C.chord_sum C.chord_le_two
    rfl rfl (C.A_add_B_lt_one hM) hA hB heA heB y.property (f y).property hx hfx hiso

end Tingley

end OAI


