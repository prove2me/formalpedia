-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_Alignment
-- name    : OAI_Analysis_SphereIsometry_Alignment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:18:06.708762+00:00
-- url     : https://prove2.me/theorems/531f43d2-1675-430d-990a-b5bbc162b50b
-- title:
--   Attained defects produce aligned configurations
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $X$ be complete, $f$ a sphere isometry with defect bound $M>0$, and suppose $\delta_t(x_0,y)=M$ for some $x_0,y$ and $t\in(0,1)$.
--
--   1. **From a return fixed point.** If an extremal direction $v$ satisfies $R(v)=v$, then $x=ty+p(v)v$, $z=z(v)$ and $w=w(v)$ form an aligned configuration.
--   2. **Existence.** An aligned configuration for $(f,y,t,M)$ exists:
--   $$
--   \text{AlignedConfiguration}(f,y,t,M)\neq\varnothing .
--   $$
--   The positive schedule gives a return-invariant closed convex set of extremal directions. The return map estimate and the condensing fixed point theorem give a fixed point there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/Alignment.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/Alignment.lean by skeleton subtraction
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

namespace OAI

/-!
# Alignment from an attained positive defect

The actual positive schedule supplies the invariant convex set; the actual
return-map estimate and the proved fixed-point theorem supply its fixed point.
The original center and scalar remain unchanged throughout the construction.
-/

noncomputable section

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A fixed point of the genuine sphere return map gives the exact four chords. -/
def aligned_of_return_fixed
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t M : ℝ) (ht : 0 < t ∧ t < 1) (hb : HasDefectBound f M)
    (v : UnitSphere X) (hv : v ∈ extremalSphere f y t ht M)
    (hfixed : returnSphere f y t ht v = v) : AlignedConfiguration f y t M where
  x := xPoint f y t ht v
  z := zPoint f y t ht v
  v := v
  w := wDirection f y t ht v
  p := pRadius f y t ht v
  r := rRadius f y t ht v
  s := sRadius f y t ht v
  u := uRadius f y t ht v
  p_pos := pRadius_pos f y t ht v
  r_pos := rRadius_pos f y t ht v
  s_pos := sRadius_pos f y t ht v
  u_pos := uRadius_pos f y t ht v
  x_eq := xPoint_eq f y t ht v
  z_eq := by simpa only [hfixed] using zPoint_eq f y t ht v
  fx_eq := fxPoint_eq f y t ht v
  fz_eq := fzPoint_eq f y t ht v
  s_sub_p := hv
  r_sub_u := (extremal_radius_identities f y t ht M hb hv).1
  chord_sum := (extremal_radius_identities f y t ht M hb hv).2.1
  chord_le_two := by
    calc
      pRadius f y t ht v + rRadius f y t ht v =
          ‖pRadius f y t ht v • (v : X) +
            rRadius f y t ht v • (returnSphere f y t ht v : X)‖ :=
        (extremal_radius_identities f y t ht M hb hv).2.2.symm
      _ = ‖(xPoint f y t ht v : X) - (zPoint f y t ht v : X)‖ :=
        (norm_xPoint_sub_zPoint f y t ht v).symm
      _ ≤ ‖(xPoint f y t ht v : X)‖ + ‖(zPoint f y t ht v : X)‖ := norm_sub_le _ _
      _ = 2 := by rw [UnitSphere.norm_coe, UnitSphere.norm_coe]; norm_num

/-- Alignment has no supplied invariant-set, contraction or fixed-point premise. -/
theorem exists_alignedConfiguration [CompleteSpace X]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y x₀ : UnitSphere X)
    (t M : ℝ) (ht : 0 < t ∧ t < 1) (hM : 0 < M)
    (hb : HasDefectBound f M) (hatt : signedDefect f t x₀ y = M) :
    Nonempty (AlignedConfiguration f y t M) := by
  obtain ⟨C, hCne, hCclosed, hCb, hCconvex, hCE, hg, hgC⟩ :=
    exists_return_invariant_convex f y x₀ t M ht hb hatt
  have hbounds : ∀ v ∈ C,
      (1 - t ≤ pAmbient f y t ht v ∧ pAmbient f y t ht v ≤ 1 + t) ∧
      (1 - t ≤ sAmbient f y t ht v ∧ sAmbient f y t ht v ≤ 1 + t) ∧
      (1 - t ≤ uAmbient f y t ht v ∧ uAmbient f y t ht v ≤ 1 + t) ∧
      (1 - t ≤ rAmbient f y t ht v ∧ rAmbient f y t ht v ≤ 1 + t) := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := hCE hv
    simpa only [pAmbient_coe, sAmbient_coe, uAmbient_coe, rAmbient_coe, Set.mem_Icc] using
      radii_bounds f y t ht a
  have hs : ∀ v ∈ C, sAmbient f y t ht v = pAmbient f y t ht v + M := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hCE hv
    simpa only [sAmbient_coe, pAmbient_coe] using sRadius_eq_add f y t ht M ha
  have hr : ∀ v ∈ C, rAmbient f y t ht v = uAmbient f y t ht v + M := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hCE hv
    simpa only [rAmbient_coe, uAmbient_coe] using rRadius_eq_add f y t ht M hb ha
  have hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (returnAmbient f y t ht v) (returnAmbient f y t ht v') ≤
        (uAmbient f y t ht v * pAmbient f y t ht v /
          (rAmbient f y t ht v * sAmbient f y t ht v)) * dist v v' +
        2 * |uAmbient f y t ht v - uAmbient f y t ht v'| / rAmbient f y t ht v +
        2 * uAmbient f y t ht v * |pAmbient f y t ht v - pAmbient f y t ht v'| /
          (rAmbient f y t ht v * sAmbient f y t ht v) := by
    intro v hv v' hv'
    simpa only [dist_eq_norm] using
      returnAmbient_pair_estimate_on f y t ht M hb C hCE hv hv'
  obtain ⟨v, hv, hfixed⟩ := exists_fixedPoint_of_return_estimate
    ht.1 ht.2 hM hCne hCclosed hCb hCconvex hg hgC hbounds hs hr hpair
  obtain ⟨a, ha, rfl⟩ := hCE hv
  have hfixedSphere : returnSphere f y t ht a = a := by
    apply Subtype.ext
    simpa only [returnAmbient_coe] using hfixed
  exact ⟨aligned_of_return_fixed f y t M ht hb a ha hfixedSphere⟩

end Tingley

end

end OAI


