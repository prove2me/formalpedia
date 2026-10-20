-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_SmallChord
-- name    : OAI_Analysis_SphereIsometry_SmallChord
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:23:26.481932+00:00
-- url     : https://prove2.me/theorems/597c022b-1eed-4001-b096-87ad1c1eea5c
-- title:
--   Ruling out the small-ratio regime
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Write $\varepsilon=1-t$.
--
--   1. **Scalar bound.** If $A,B>0$, $A+B<1$, $d\le2$, $\varepsilon\le dA(1-B)$ and $\varepsilon\le dB(1-A)$, then $\varepsilon<\frac12$.
--   2. **Coefficients.** With $d=p+r=s+u$ and $\varepsilon+t=1$, these give $rt-p\varepsilon>0$, $s\varepsilon-ut\ge0$ and $p<s$.
--   3. **Norm contradiction.** Two exact identities express $y$ and $z$ (and $f(y)$, $f(z)$) as combinations of the chord vectors with these coefficients. The triangle inequality then gives
--   $$
--   \|f(y)-f(z)\|\neq\|y-z\| ,
--   $$
--   which is impossible for an isometry.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/SmallChord.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/SmallChord.lean by skeleton subtraction
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

namespace OAI

/-!
# The small-chord contradiction

The scalar estimates imply nonnegative coefficients in two exact identities
between the actual chord vectors. Applying the norm triangle inequality to
those identities contradicts preservation of the distance between the base
point and the opposite endpoint. No convexity or monotonicity property of an
abstract auxiliary function is assumed.
-/

namespace Tingley

/-- The two small-regime estimates and the strict chord imbalance force the
radial deficit to be strictly below one half. -/
theorem smallChord_epsilon_lt_half {A B d ε : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A + B < 1) (hd : d ≤ 2)
    (heA : ε ≤ d * A * (1 - B)) (heB : ε ≤ d * B * (1 - A)) :
    ε < 1 / 2 := by
  have step (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hsum : a + b < 1)
      (he : ε ≤ d * a * (1 - b)) : ε < 1 / 2 := by
    have hahalf : a < 1 / 2 := by linarith
    have hb1 : b < 1 := by linarith
    have hprod0 : 0 ≤ a * (1 - b) :=
      mul_nonneg ha.le (sub_nonneg.mpr hb1.le)
    have hprod : a * (1 - b) ≤ a * (1 - a) :=
      mul_le_mul_of_nonneg_left (by linarith) ha.le
    have hsquare : 0 < (1 / 2 - a) ^ 2 :=
      sq_pos_of_pos (by linarith)
    have hquarter : a * (1 - b) < 1 / 4 := by nlinarith
    have hscale : d * (a * (1 - b)) ≤ 2 * (a * (1 - b)) :=
      mul_le_mul_of_nonneg_right hd hprod0
    nlinarith [he, hscale, hquarter]
  rcases le_total A B with h | h
  · exact step A B hA h hAB heA
  · exact step B A hB h (by linarith) heB

/-- The scalar conclusions needed by the two actual vector identities.
The second coefficient is permitted to vanish. -/
theorem smallChord_coefficients {A B d ε t p r s u : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A + B < 1)
    (hd : 0 < d) (hd2 : d ≤ 2) (hεt : ε + t = 1)
    (hdr : d = p + r) (hds : d = s + u)
    (hpA : p = d * A) (huB : u = d * B)
    (hAe : A ≤ ε) (hBe : B ≤ ε)
    (heA : ε ≤ d * A * (1 - B)) (heB : ε ≤ d * B * (1 - A)) :
    ε < 1 / 2 ∧ 0 < r * t - p * ε ∧ 0 ≤ s * ε - u * t ∧ p < s := by
  have hehalf := smallChord_epsilon_lt_half hA hB hAB hd2 heA heB
  have hAt : A < t := by linarith
  have hr : r = d - p := by linarith
  have hs : s = d - u := by linarith
  have he : ε = 1 - t := by linarith
  have ht : t = 1 - ε := by linarith
  have hα : r * t - p * ε = d * (t - A) := by
    rw [hr, hpA, he]
    ring
  have hβ : s * ε - u * t = d * (ε - B) := by
    rw [hs, huB, ht]
    ring
  have hgap : s - p = d * (1 - A - B) := by
    rw [hs, hpA, huB]
    ring
  refine ⟨hehalf, ?_, ?_, ?_⟩
  · rw [hα]
    exact mul_pos hd (sub_pos.mpr hAt)
  · rw [hβ]
    exact mul_nonneg hd.le (sub_nonneg.mpr hBe)
  · have hgap_pos : 0 < s - p := by
      rw [hgap]
      exact mul_pos hd (by linarith)
    linarith

/-- Two norm triangle inequalities on the actual chord vectors are incompatible
with the chord imbalance and the preserved base-to-endpoint distance. -/
theorem smallChord_norm_contradiction
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (y v : X) (b w : Y) {t ε p r s u d : ℝ}
    (hεt : ε + t = 1) (hε : 0 < ε) (hd : 0 < d)
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hu : 0 < u)
    (hdr : d = p + r) (hds : d = s + u) (hps : p < s)
    (hy : ‖y‖ = 1) (hb : ‖b‖ = 1)
    (hx : ‖t • y + p • v‖ = 1) (hfx : ‖t • b + s • w‖ = 1)
    (hα : 0 ≤ r * t - p * ε) (hβ : 0 ≤ s * ε - u * t)
    (hiso : ‖ε • y + r • v‖ = ‖ε • b + u • w‖) : False := by
  let V : X := ε • y + r • v
  let W : Y := ε • b + u • w
  have hVW : ‖V‖ = ‖W‖ := hiso
  have hleftId : r • (t • y + p • v) = p • V + (r * t - p * ε) • y := by
    dsimp only [V]
    module
  have hrightId : s • W = u • (t • b + s • w) + (s * ε - u * t) • b := by
    dsimp only [W]
    module
  have hleft : r ≤ p * ‖V‖ + (r * t - p * ε) := by
    calc
      r = ‖r • (t • y + p • v)‖ := by
        rw [norm_smul_of_nonneg hr.le, hx, mul_one]
      _ = ‖p • V + (r * t - p * ε) • y‖ := congrArg norm hleftId
      _ ≤ ‖p • V‖ + ‖(r * t - p * ε) • y‖ := norm_add_le _ _
      _ = p * ‖V‖ + (r * t - p * ε) := by
        rw [norm_smul_of_nonneg hp.le, norm_smul_of_nonneg hα, hy, mul_one]
  have hright : s * ‖W‖ ≤ u + (s * ε - u * t) := by
    calc
      s * ‖W‖ = ‖s • W‖ := (norm_smul_of_nonneg hs.le W).symm
      _ = ‖u • (t • b + s • w) + (s * ε - u * t) • b‖ := congrArg norm hrightId
      _ ≤ ‖u • (t • b + s • w)‖ + ‖(s * ε - u * t) • b‖ := norm_add_le _ _
      _ = u + (s * ε - u * t) := by
        simp only [norm_smul_of_nonneg hu.le, norm_smul_of_nonneg hβ, hfx, hb, mul_one]
  have ht : t = 1 - ε := by linarith
  have hrearrange : r - (r * t - p * ε) = ε * d := by
    rw [ht, hdr]
    ring
  have hurearrange : u + (s * ε - u * t) = ε * d := by
    rw [ht, hds]
    ring
  have hlower : ε * d ≤ p * ‖V‖ := by linarith
  have hupper : s * ‖V‖ ≤ ε * d := by rw [hVW]; linarith
  have hpositive : 0 < ε * d := mul_pos hε hd
  have hVpos : 0 < ‖V‖ := by
    by_contra h
    have hVnonpos : ‖V‖ ≤ 0 := le_of_not_gt h
    have hpV : p * ‖V‖ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le hVnonpos
    linarith
  exact (not_lt_of_ge (hupper.trans hlower)) (mul_lt_mul_of_pos_right hps hVpos)

/-- The small regime contradicts preservation of the actual opposite-endpoint
distance. All scalar guards of the norm argument are derived here. -/
theorem smallChord_contradiction
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (y v : X) (b w : Y) {t ε p r s u d A B : ℝ}
    (ht1 : t < 1) (he : ε = 1 - t)
    (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hu : 0 < u)
    (hdr : d = p + r) (hds : d = s + u) (hd2 : d ≤ 2)
    (hA : A = p / d) (hB : B = u / d) (hAB : A + B < 1)
    (hAe : A ≤ ε) (hBe : B ≤ ε)
    (heA : ε ≤ d * A * (1 - B)) (heB : ε ≤ d * B * (1 - A))
    (hy : ‖y‖ = 1) (hb : ‖b‖ = 1)
    (hx : ‖t • y + p • v‖ = 1) (hfx : ‖t • b + s • w‖ = 1)
    (hiso : ‖ε • y + r • v‖ = ‖ε • b + u • w‖) : False := by
  have hd : 0 < d := by rw [hdr]; exact add_pos hp hr
  have hApos : 0 < A := by rw [hA]; exact div_pos hp hd
  have hBpos : 0 < B := by rw [hB]; exact div_pos hu hd
  have hpA : p = d * A := by rw [hA, mul_div_cancel₀ p (ne_of_gt hd)]
  have huB : u = d * B := by rw [hB, mul_div_cancel₀ u (ne_of_gt hd)]
  have hεt : ε + t = 1 := by linarith
  have hε : 0 < ε := by linarith
  obtain ⟨_, hα, hβ, hps⟩ := smallChord_coefficients hApos hBpos hAB hd hd2 hεt
    hdr hds hpA huB hAe hBe heA heB
  exact smallChord_norm_contradiction y v b w hεt hε hd hp hr hs hu hdr hds hps
    hy hb hx hfx hα.le hβ hiso

end Tingley

end OAI


