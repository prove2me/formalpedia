-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_LargeChord
-- name    : OAI_Analysis_SphereIsometry_LargeChord
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:22:00.478019+00:00
-- url     : https://prove2.me/theorems/e59c0bef-637d-4a1a-875e-09e8dc61bf0d
-- title:
--   Ruling out the large-ratio regime
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $C$ be an aligned configuration for $f$ with defect bound $M>0$ at $(y,t)$, $0<t<1$: $x=ty+pv$, $z=ty-rv$, $f(x)=tf(y)+sw$, $f(z)=tf(y)-uw$ with $s-p=r-u=M$, $d=p+r\le2$, $A=p/d$, $B=u/d$.
--
--   1. **Large-$B$ bounds.** If $B>1-t$, then $1-t\le Au$ and $\theta\le1-B$. Moreover $A>1-t$, and every support $L$ at $v$ has $L(y)<0$.
--   2. **Signs.** Applying the same reasoning to the inverse configuration, every support $K$ at $w$ has $K(f(y))>0$.
--   3. **Impossibility.** A small radial perturbation then shortens one side and lengthens the other, so the signed defect exceeds $M$. Hence $B>1-t$ is impossible, and by the inverse configuration
--   $$
--   A\le1-t,\qquad B\le1-t .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/LargeChord.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/LargeChord.lean by skeleton subtraction
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

namespace OAI

/-!
# Excluding large aligned-chord ratios

The secant estimate holds for every support. Reusing a support in the equality
case makes the sign strict, and the literal inverse configuration gives the
opposite image sign. A small radial perturbation then violates the actual defect
bound. No compactness assumption on either ambient space is used here.
-/

noncomputable section

namespace Tingley
namespace AlignedConfiguration

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}
variable (C : AlignedConfiguration f y t M)

/-- The large-ratio secant bound controls both the product and the size of the
support perturbation. All quantities come from the given configuration. -/
theorem largeB_product_bounds (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hlarge : 1 - t < C.B) :
    1 - t ≤ C.A * C.u ∧ C.secantTheta ≤ 1 - C.B := by
  obtain ⟨φ, hφ⟩ := exists_support ((C.v : X) + C.secantTheta • (y : X))
  have hs := C.secant_bounds hM ht hb φ hφ
  have hle : (1 - t) / C.p ≤ C.B :=
    hs.1.trans (hs.2.1.trans (hs.2.2.2 hlarge))
  have hproduct : 1 - t ≤ C.A * C.u := by
    calc
      1 - t ≤ C.B * C.p := (div_le_iff₀ C.p_pos).mp hle
      _ = C.A * C.u := by unfold A B; ring
  refine ⟨hproduct, ?_⟩
  rw [secantTheta, C.secantStep_eq_largeB ht hlarge, C.one_sub_B]
  apply (div_le_iff₀ C.p_pos).mpr
  calc
    ((1 - t) / C.u) * C.s ≤ C.A * C.s :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ C.u_pos).mpr hproduct) C.s_pos.le
    _ = (C.s / C.d) * C.p := by unfold A; ring

/-- A large `B` makes every support at the original chord direction strictly
negative on the base vector, and forces `A` into the same large regime. -/
theorem largeB_forces_largeA_and_negative_support
    (hM : 0 < M) (ht : 0 < t ∧ t < 1) (hb : HasDefectBound f M)
    (hlarge : 1 - t < C.B) :
    1 - t < C.A ∧
      ∀ L : X →L[ℝ] ℝ, SupportAt L (C.v : X) → L (y : X) < 0 := by
  obtain ⟨hproduct, hθB⟩ := C.largeB_product_bounds hM ht hb hlarge
  have hθ : 0 < C.secantTheta := C.secantTheta_pos ht
  have hnegative : ∀ L : X →L[ℝ] ℝ,
      SupportAt L (C.v : X) → L (y : X) < 0 := by
    intro L hL
    have hLv : L (C.v : X) = 1 := hL.2.trans C.v.property
    obtain ⟨φ, hφ⟩ := exists_support ((C.v : X) + C.secantTheta • (y : X))
    have hs := C.secant_bounds hM ht hb φ hφ
    have hφv : φ (C.v : X) ≤ C.B := hs.2.1.trans (hs.2.2.2 hlarge)
    have hφy : φ (y : X) ≤ 1 := by
      simpa only [UnitSphere.norm_coe] using apply_le_norm hφ.1 (y : X)
    have hφeval : φ (C.v : X) + C.secantTheta * φ (y : X) =
        ‖(C.v : X) + C.secantTheta • (y : X)‖ := by
      simpa only [map_add, map_smul, smul_eq_mul] using hφ.2
    have hleft : 1 + C.secantTheta * L (y : X) ≤
        ‖(C.v : X) + C.secantTheta • (y : X)‖ := by
      simpa only [map_add, map_smul, smul_eq_mul, hLv] using
        apply_le_norm hL.1 ((C.v : X) + C.secantTheta • (y : X))
    have hφterm : C.secantTheta * φ (y : X) ≤ C.secantTheta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hφy hθ.le
    have hnorm : ‖(C.v : X) + C.secantTheta • (y : X)‖ ≤
        C.B + C.secantTheta := by
      linarith only [hφeval, hφv, hφterm]
    have hstrict : 1 + C.secantTheta * L (y : X) - C.secantTheta < C.B := by
      by_contra hnot
      have hLperturbed : SupportAt L ((C.v : X) + C.secantTheta • (y : X)) := by
        refine ⟨hL.1, ?_⟩
        simp only [map_add, map_smul, smul_eq_mul, hLv]
        have hreverse := le_of_not_gt hnot
        linarith only [hleft, hnorm, hreverse]
      have hsL := C.secant_bounds hM ht hb L hLperturbed
      have hbad : 1 ≤ C.B := by
        simpa only [hLv] using hsL.2.1.trans (hsL.2.2.2 hlarge)
      exact (not_le_of_gt C.B_lt_one) hbad
    have hmul : C.secantTheta * L (y : X) < C.secantTheta * 0 := by
      linarith only [hstrict, hθB]
    exact (mul_lt_mul_iff_right₀ hθ).mp hmul
  refine ⟨?_, hnegative⟩
  obtain ⟨L, hL⟩ := exists_support (C.v : X)
  have hj : L (y : X) < 0 := hnegative L hL
  have hLv : L (C.v : X) = 1 := hL.2.trans C.v.property
  have hz : C.r • (C.v : X) - t • (y : X) = -(C.z : X) := by
    rw [C.z_eq]
    abel
  have hznorm : ‖C.r • (C.v : X) - t • (y : X)‖ = 1 := by
    rw [hz, norm_neg, UnitSphere.norm_coe]
  have hr : C.r - t * L (y : X) ≤ 1 := by
    simpa only [map_sub, map_smul, smul_eq_mul, hLv, mul_one, hznorm] using
      apply_le_norm hL.1 (C.r • (C.v : X) - t • (y : X))
  have htj : t * L (y : X) < 0 := mul_neg_of_pos_of_neg ht.1 hj
  have hr1 : C.r < 1 := by linarith only [hr, htj]
  have hu1 : C.u < 1 := by linarith only [hr1, C.r_sub_u, hM]
  have hproduct_lt : C.A * C.u < C.A := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hu1 C.A_pos
  exact hproduct.trans_lt hproduct_lt

/-- The inverse uses literal negated directions. In particular, obtaining the
positive image sign does not assume that the sphere map preserves antipodes. -/
theorem largeB_support_signs (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hlarge : 1 - t < C.B) :
    (∀ L : X →L[ℝ] ℝ, SupportAt L (C.v : X) → L (y : X) < 0) ∧
      (∀ K : Y →L[ℝ] ℝ, SupportAt K (C.w : Y) → 0 < K (f y : Y)) := by
  obtain ⟨hA, hnegative⟩ :=
    C.largeB_forces_largeA_and_negative_support hM ht hb hlarge
  have hlarge_inverse : 1 - t < C.inverse.B := by
    simpa only [inverse_B] using hA
  have hinverse :=
    (C.inverse.largeB_forces_largeA_and_negative_support hM ht hb.symm
      hlarge_inverse).2
  refine ⟨hnegative, ?_⟩
  intro K hK
  have hKneg : SupportAt (-K) (C.inverse.v : Y) := by
    simpa only [inverse_v_coe] using hK.neg
  have h := hinverse (-K) hKneg
  change -(K (f y : Y)) < 0 at h
  linarith only [h]

/-- A small decrease of the radius strictly increases both contributions to the
signed defect, contradicting its global bound. -/
theorem largeB_impossible (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hlarge : 1 - t < C.B) : False := by
  obtain ⟨hnegative, hpositive⟩ := C.largeB_support_signs hM ht hb hlarge
  obtain ⟨η, hη, hηt, hshort⟩ :=
    exists_radial_perturbation_lt_with_cap C.v.property C.p_pos ht.1 hnegative
  obtain ⟨K, hK⟩ := exists_support (C.w : Y)
  have hKw : K (C.w : Y) = 1 := hK.2.trans C.w.property
  have hKb : 0 < K (f y : Y) := hpositive K hK
  have hlong : C.s < ‖C.s • (C.w : Y) + η • (f y : Y)‖ := by
    have hle := apply_le_norm hK.1 (C.s • (C.w : Y) + η • (f y : Y))
    simp only [map_add, map_smul, smul_eq_mul, hKw, mul_one] at hle
    have hterm : 0 < η * K (f y : Y) := mul_pos hη hKb
    linarith only [hle, hterm]
  have hq : t - η ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact (sub_pos.mpr hηt).le
    · linarith only [ht.2, hη]
  have hx : (C.x : X) - (t - η) • (y : X) =
      C.p • (C.v : X) + η • (y : X) := by
    rw [C.x_eq, sub_smul]
    abel
  have hfx : (f C.x : Y) - (t - η) • (f y : Y) =
      C.s • (C.w : Y) + η • (f y : Y) := by
    rw [C.fx_eq, sub_smul]
    abel
  have hbound := (abs_le.mp (hb (t - η) hq C.x y)).2
  rw [signedDefect, hfx, hx] at hbound
  linarith only [hbound, hshort, hlong, C.s_sub_p]

/-- Both ratios lie in the small regime. The first component is obtained by
applying the already-proved contradiction to the exact inverse configuration. -/
theorem small_ratios (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) : C.A ≤ 1 - t ∧ C.B ≤ 1 - t := by
  constructor
  · have h : C.inverse.B ≤ 1 - t :=
      le_of_not_gt (C.inverse.largeB_impossible hM ht hb.symm)
    simpa only [inverse_B] using h
  · exact le_of_not_gt (C.largeB_impossible hM ht hb)

end AlignedConfiguration
end Tingley

end

end OAI


