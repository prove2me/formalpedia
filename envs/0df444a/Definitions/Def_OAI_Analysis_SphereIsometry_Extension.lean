-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_Extension
-- name    : OAI_Analysis_SphereIsometry_Extension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:28:54.437398+00:00
-- url     : https://prove2.me/theorems/ea8753bb-b108-4170-98ab-155a94e6f9be
-- title:
--   Vanishing defects and the linear extension
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $f:S_X\to S_Y$ be a bijective isometry.
--
--   1. **No attained defect.** In Banach spaces, a defect bound $M>0$ cannot be attained, i.e. $\delta_t(x,y)=M$ with $t\in(0,1)$ is impossible: it would produce an aligned configuration.
--   2. **Zero maximal defect.** For nontrivial spaces $M_f=0$, since a positive value would be attained in completed ultrapowers. Hence $f$ has defect bound $0$ in general.
--   3. **Extension.** The radial extension is a linear isometry $T$ with
--   $$
--   T(u)=f(u),\qquad T(x)=\|x\|f(x/\|x\|) .
--   $$
--   4. **Sphere equivalence.** An onto isometry $S_X\to S_Y$ is a bijective isometry.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/Extension.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/Extension.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_ChordContradiction
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialExtension

namespace OAI

/-!
# The unique real-linear extension of an onto sphere isometry

The intermediate hypotheses of the separate constructions are discharged here:
positive original defect produces an actual attained defect in completed normed
quotients, alignment produces actual opposite chords, and the chord theorem
rules them out. The original radial extension consequently preserves distance.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem no_attained_positive_defect
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (t M : ℝ)
    (ht : 0 < t ∧ t < 1) (hM : 0 < M) (hb : HasDefectBound f M)
    (x y : UnitSphere X) (hatt : signedDefect f t x y = M) : False := by
  obtain ⟨C⟩ := exists_alignedConfiguration f y x t M ht hM hb hatt
  exact alignedConfiguration_impossible hM ht hb C

variable [Nontrivial X] [Nontrivial Y]

theorem maxDefect_eq_zero
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [Nontrivial X] [Nontrivial Y]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : maxDefect f = 0 := by
  apply le_antisymm ?_ (maxDefect_nonneg f)
  by_contra hn
  have hM : 0 < maxDefect f := lt_of_not_ge hn
  obtain ⟨hb, hi, t, ht, ha⟩ := positive_maxDefect_attained_or_inverse f hM
  rcases ha with ⟨x, y, hxy⟩ | ⟨x, y, hxy⟩
  · exact no_attained_positive_defect _ t (maxDefect f) ⟨ht.1, ht.2⟩ hM hb x y hxy
  · exact no_attained_positive_defect _ t (maxDefect f) ⟨ht.1, ht.2⟩ hM hi x y hxy

theorem hasDefectBound_zero (f : UnitSphere X ≃ᵢ UnitSphere Y) : HasDefectBound f 0 := by
  simpa only [maxDefect_eq_zero] using hasDefectBound_maxDefect f

/-- The actual unconditional extension, with the original radial function. -/
def extension (f : UnitSphere X ≃ᵢ UnitSphere Y) : X ≃ₗᵢ[ℝ] Y :=
  radialLinearIsometryEquiv f (hasDefectBound_zero f)

@[simp] theorem extension_apply (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) :
    extension f x = radialExtension f x := rfl

@[simp] theorem extension_zero (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    extension f 0 = 0 := radialExtension_zero f

@[simp] theorem extension_unit (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : UnitSphere X) :
    extension f (x : X) = (f x : Y) := radialExtension_unit f x

/-- An ordinary onto sphere isometry is a genuine sphere isometry equivalence. -/
def sphereIsometryEquiv (f : UnitSphere X → UnitSphere Y)
    (hf : Isometry f) (hs : Function.Surjective f) : UnitSphere X ≃ᵢ UnitSphere Y where
  toEquiv := Equiv.ofBijective f ⟨hf.injective, hs⟩
  isometry_toFun := hf

end Tingley

end

end OAI


