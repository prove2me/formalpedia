-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapBounds
-- name    : OAI_Analysis_SphereIsometry_ReturnMapBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:18:27.362645+00:00
-- url     : https://prove2.me/theorems/658a0899-85ad-4c8b-98a6-4b5451b3732b
-- title:
--   Scalar bounds for the return map contraction factor
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. These are the scalar inequalities behind the return map estimate.
--
--   1. **Radius ratio.** If $s=p+M$, $0<s\le U$ and $M\ge0$, then $p/s\le1-M/U$.
--   2. **Coefficients.** With all radii in $[1-t,1+t]$, $s=p+M$ and $r=u+M$, the factor satisfies
--   $$
--   \frac{up}{rs}\le\Bigl(1-\frac M{1+t}\Bigr)^2 ,
--   $$
--   and the error terms satisfy $\frac{2du}r+\frac{2u\,dp}{rs}\le\frac2a(du+dp)$ for a lower bound $a$ on the radii.
--   3. **Contraction factor.** For $0<M<1+t$, $(1-\frac M{1+t})^2\in[0,1)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ReturnMapBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ReturnMapBounds.lean by skeleton subtraction
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

namespace OAI

/-! Scalar estimates for the return map, before taking finite diameter covers. -/

namespace Tingley

theorem radius_ratio_le_factor {p s M U : ℝ} (hs : 0 < s)
    (hM : 0 ≤ M) (hsU : s ≤ U) (hsp : s = p + M) :
    p / s ≤ 1 - M / U := by
  calc
    p / s = (s - M) / s := congrArg (fun q : ℝ => q / s) (by linarith)
    _ = 1 - M / s := by rw [sub_div, div_self (ne_of_gt hs)]
    _ ≤ 1 - M / U :=
      sub_le_sub_left (div_le_div_of_nonneg_left hM hs hsU) 1

theorem return_coefficient_le {p s u r M U : ℝ}
    (hp : 0 ≤ p) (_hu : 0 ≤ u) (hr : 0 < r) (hs : 0 < s)
    (hM : 0 ≤ M) (hrU : r ≤ U) (hsU : s ≤ U)
    (hrm : r = u + M) (hsm : s = p + M) :
    u * p / (r * s) ≤ (1 - M / U) ^ 2 := by
  have hpq := radius_ratio_le_factor hs hM hsU hsm
  have huq := radius_ratio_le_factor hr hM hrU hrm
  have hp0 : 0 ≤ p / s := div_nonneg hp hs.le
  have hq0 : 0 ≤ 1 - M / U := hp0.trans hpq
  calc
    u * p / (r * s) = (u / r) * (p / s) := by rw [div_mul_div_comm]
    _ ≤ (1 - M / U) * (1 - M / U) := mul_le_mul huq hpq hp0 hq0
    _ = (1 - M / U) ^ 2 := by ring

theorem return_pair_error_le {a r s u du dp : ℝ}
    (ha : 0 < a) (har : a ≤ r) (has : a ≤ s)
    (hur : u ≤ r) (hdu : 0 ≤ du) (hdp : 0 ≤ dp) :
    2 * du / r + 2 * u * dp / (r * s) ≤ (2 / a) * (du + dp) := by
  have hr : 0 < r := ha.trans_le har
  have hs : 0 < s := ha.trans_le has
  have he₁ : 2 * du / r ≤ 2 * du / a :=
    div_le_div_of_nonneg_left (mul_nonneg zero_le_two hdu) ha har
  have he₂ : 2 * u * dp / (r * s) ≤ 2 * dp / a := by
    calc
      2 * u * dp / (r * s) = (u / r) * (2 * dp / s) := by
        field_simp [ne_of_gt hr, ne_of_gt hs]
      _ ≤ 1 * (2 * dp / s) :=
        mul_le_mul_of_nonneg_right ((div_le_one₀ hr).mpr hur)
          (div_nonneg (mul_nonneg zero_le_two hdp) hs.le)
      _ = 2 * dp / s := one_mul _
      _ ≤ 2 * dp / a :=
        div_le_div_of_nonneg_left (mul_nonneg zero_le_two hdp) ha has
  calc
    2 * du / r + 2 * u * dp / (r * s) ≤ 2 * du / a + 2 * dp / a :=
      add_le_add he₁ he₂
    _ = (2 / a) * (du + dp) := by ring

theorem return_pair_uniform_bound {a U M p s u r D Dg du dp : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hp : 0 ≤ p) (hu : 0 ≤ u)
    (har : a ≤ r) (has : a ≤ s) (hrU : r ≤ U) (hsU : s ≤ U)
    (hrm : r = u + M) (hsm : s = p + M)
    (hD : 0 ≤ D) (hdu : 0 ≤ du) (hdp : 0 ≤ dp)
    (hpair : Dg ≤ (u * p / (r * s)) * D +
      2 * du / r + 2 * u * dp / (r * s)) :
    Dg ≤ (1 - M / U) ^ 2 * D + (2 / a) * (du + dp) := by
  have hr : 0 < r := ha.trans_le har
  have hs : 0 < s := ha.trans_le has
  have hur : u ≤ r := by linarith
  have hcoeff := return_coefficient_le hp hu hr hs hM hrU hsU hrm hsm
  have herr := return_pair_error_le ha har has hur hdu hdp
  calc
    Dg ≤ (u * p / (r * s)) * D +
        2 * du / r + 2 * u * dp / (r * s) := hpair
    _ = (u * p / (r * s)) * D +
        (2 * du / r + 2 * u * dp / (r * s)) := by ring
    _ ≤ (1 - M / U) ^ 2 * D + (2 / a) * (du + dp) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoeff hD) herr

/-- The exact square factor, with its strict upper bound. -/
theorem return_factor_mem_Ico {t M : ℝ} (ht0 : 0 < t)
    (hM : 0 < M) (hMU : M < 1 + t) :
    (1 - M / (1 + t)) ^ 2 ∈ Set.Ico (0 : ℝ) 1 := by
  have hU : 0 < 1 + t := by linarith
  have hq0 : 0 < M / (1 + t) := div_pos hM hU
  have hq1 : M / (1 + t) < 1 := by
    apply (div_lt_iff₀ hU).mpr
    simpa using hMU
  have hprod : 0 < (1 - M / (1 + t)) * (M / (1 + t)) :=
    mul_pos (by linarith) hq0
  exact ⟨sq_nonneg _, by nlinarith⟩

/-- Nonemptiness is used only to bound M by one actual positive radius. -/
theorem return_contraction_factor_mem_Ico {X : Type*}
    {C : Set X} {p s : X → ℝ} {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M) (hCne : C.Nonempty)
    (hp : ∀ v ∈ C, 1 - t ≤ p v)
    (hsU : ∀ v ∈ C, s v ≤ 1 + t)
    (hsm : ∀ v ∈ C, s v = p v + M) :
    (1 - M / (1 + t)) ^ 2 ∈ Set.Ico (0 : ℝ) 1 := by
  obtain ⟨v, hv⟩ := hCne
  have hpv := hp v hv
  have hsv := hsU v hv
  have heq := hsm v hv
  apply return_factor_mem_Ico ht0 hM
  linarith

end Tingley

end OAI


