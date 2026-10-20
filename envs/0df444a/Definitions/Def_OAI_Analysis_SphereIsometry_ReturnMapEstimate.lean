-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapEstimate
-- name    : OAI_Analysis_SphereIsometry_ReturnMapEstimate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:12:44.680273+00:00
-- url     : https://prove2.me/theorems/69887175-d9d7-4e93-8d80-e18c9a9f8396
-- title:
--   Two-point estimate for the return map
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Fix a bijective sphere isometry $f$ with defect bound $M$, a base point $y$ and $t\in(0,1)$; for a direction $v$ the return map uses the contact radii $p(v),s(v),u(v),r(v)\in[1-t,1+t]$ and returns $R(v)\in S_X$, and the extremal set consists of the directions with $s(v)-p(v)=M$.
--
--   1. **Scalar comparisons.** For $a\ge0$ and unit vectors $v,w$: $\|av-bw\|\le a\|v-w\|+|a-b|$, and conversely $a\|v-w\|$ is controlled by $\|av-bw\|+|a-b|$.
--   2. **Return estimate.** For extremal $v,v'$,
--   $$
--   \|R(v)-R(v')\|\le\frac{u(v)p(v)}{r(v)s(v)}\|v-v'\|+\frac{2|u(v)-u(v')|}{r(v)}+\frac{2u(v)|p(v)-p(v')|}{r(v)s(v)} .
--   $$
--   The same holds for the totalized map on any subset of the extremal set. The factor $\frac{up}{rs}$ is strictly less than $1$ because $s=p+M$ and $r=u+M$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ReturnMapEstimate.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ReturnMapEstimate.lean by skeleton subtraction
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

namespace OAI

/-!
# The actual return map's two-point estimate

The two triangle-inequality comparisons retain the unprimed radius multiplying
both direction differences. The sphere isometry connects the actual endpoints;
no pairwise estimate for an arbitrary map is assumed.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Changing both the scalar and a unit vector, retaining the first scalar
in front of the direction difference. -/
theorem norm_smul_sub_smul_le_first (a b : ℝ) (ha : 0 ≤ a)
    (v w : UnitSphere X) :
    ‖a • (v : X) - b • (w : X)‖ ≤ a * ‖(v : X) - (w : X)‖ + |a - b| := by
  have he : a • (v : X) - b • (w : X) =
      a • ((v : X) - (w : X)) + (a - b) • (w : X) := by
    simp only [smul_sub, sub_smul]
    abel
  calc
    ‖a • (v : X) - b • (w : X)‖ =
        ‖a • ((v : X) - (w : X)) + (a - b) • (w : X)‖ := congrArg norm he
    _ ≤ ‖a • ((v : X) - (w : X))‖ + ‖(a - b) • (w : X)‖ := norm_add_le _ _
    _ = a * ‖(v : X) - (w : X)‖ + |a - b| := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_eq_abs,
        w.property, mul_one]

/-- Recovering the direction difference from two differently scaled unit
vectors, again retaining the first scalar. -/
theorem first_mul_norm_sub_le_smul_sub (a b : ℝ) (ha : 0 ≤ a)
    (v w : UnitSphere X) :
    a * ‖(v : X) - (w : X)‖ ≤ ‖a • (v : X) - b • (w : X)‖ + |a - b| := by
  have he : a • ((v : X) - (w : X)) =
      (a • (v : X) - b • (w : X)) + (b - a) • (w : X) := by
    simp only [smul_sub, sub_smul]
    abel
  calc
    a * ‖(v : X) - (w : X)‖ = ‖a • ((v : X) - (w : X))‖ := by
      rw [norm_smul, Real.norm_of_nonneg ha]
    _ = ‖(a • (v : X) - b • (w : X)) + (b - a) • (w : X)‖ :=
      congrArg norm he
    _ ≤ ‖a • (v : X) - b • (w : X)‖ + ‖(b - a) • (w : X)‖ := norm_add_le _ _
    _ = ‖a • (v : X) - b • (w : X)‖ + |a - b| := by
      rw [norm_smul, Real.norm_eq_abs, w.property, mul_one, abs_sub_comm b a]

/-- The scalar elimination used after the two actual endpoint comparisons.
Only the radii by which we divide require strict positivity. -/
theorem return_pair_scalar_elimination
    (r s u p A B Dg Dw Dv : ℝ) (hr : 0 < r) (hs : 0 < s) (hu : 0 ≤ u)
    (hg : r * Dg ≤ 2 * A + u * Dw)
    (hw : s * Dw ≤ 2 * B + p * Dv) :
    Dg ≤ (u * p / (r * s)) * Dv + 2 * A / r + 2 * u * B / (r * s) := by
  have hw' : Dw ≤ (2 * B + p * Dv) / s := by
    apply (le_div_iff₀ hs).2
    simpa only [mul_comm Dw s] using hw
  calc
    Dg ≤ (2 * A + u * Dw) / r := by
      apply (le_div_iff₀ hr).2
      simpa only [mul_comm Dg r] using hg
    _ ≤ (2 * A + u * ((2 * B + p * Dv) / s)) / r :=
      div_le_div_of_nonneg_right
        (add_le_add_right (mul_le_mul_of_nonneg_left hw' hu) _) hr.le
    _ = (u * p / (r * s)) * Dv + 2 * A / r + 2 * u * B / (r * s) := by
      field_simp [ne_of_gt hr, ne_of_gt hs]
      ring

/-- The exact two-point estimate for the constructed return map on its actual
extremal sphere set. Both endpoint comparisons use the original sphere isometry. -/
theorem returnSphere_pair_estimate
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (M : ℝ) (hb : HasDefectBound f M)
    {v v' : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M)
    (hv' : v' ∈ extremalSphere f y t ht M) :
    ‖(returnSphere f y t ht v : X) - (returnSphere f y t ht v' : X)‖ ≤
      (uRadius f y t ht v * pRadius f y t ht v /
        (rRadius f y t ht v * sRadius f y t ht v)) * ‖(v : X) - (v' : X)‖ +
      2 * |uRadius f y t ht v - uRadius f y t ht v'| / rRadius f y t ht v +
      2 * uRadius f y t ht v * |pRadius f y t ht v - pRadius f y t ht v'| /
        (rRadius f y t ht v * sRadius f y t ht v) := by
  let p := pRadius f y t ht
  let s := sRadius f y t ht
  let u := uRadius f y t ht
  let r := rRadius f y t ht
  let g := returnSphere f y t ht
  let w := wDirection f y t ht
  let x := xPoint f y t ht
  let z := zPoint f y t ht
  have hx (a : UnitSphere X) : (x a : X) = t • (y : X) + p a • (a : X) :=
    xPoint_eq f y t ht a
  have hz (a : UnitSphere X) : (z a : X) = t • (y : X) - r a • (g a : X) :=
    zPoint_eq f y t ht a
  have hfx (a : UnitSphere X) : (f (x a) : Y) =
      t • (f y : Y) + s a • (w a : Y) := fxPoint_eq f y t ht a
  have hfz (a : UnitSphere X) : (f (z a) : Y) =
      t • (f y : Y) - u a • (w a : Y) := fzPoint_eq f y t ht a
  have hr : 0 < r v := rRadius_pos f y t ht v
  have hs : 0 < s v := sRadius_pos f y t ht v
  have hu : 0 ≤ u v := (uRadius_pos f y t ht v).le
  have hp : 0 ≤ p v := (pRadius_pos f y t ht v).le
  have hrdiff : r v - r v' = u v - u v' := by
    have h := rRadius_eq_add f y t ht M hb hv
    have h' := rRadius_eq_add f y t ht M hb hv'
    change r v = u v + M at h
    change r v' = u v' + M at h'
    linarith
  have hsdiff : s v - s v' = p v - p v' := by
    have h := sRadius_eq_add f y t ht M hv
    have h' := sRadius_eq_add f y t ht M hv'
    change s v = p v + M at h
    change s v' = p v' + M at h'
    linarith
  have hR : ‖r v • (g v : X) - r v' • (g v' : X)‖ =
      ‖u v • (w v : Y) - u v' • (w v' : Y)‖ := by
    calc
      ‖r v • (g v : X) - r v' • (g v' : X)‖ = ‖(z v' : X) - (z v : X)‖ := by
        congr 1
        rw [hz v', hz v]
        abel
      _ = ‖(f (z v') : Y) - (f (z v) : Y)‖ :=
        (sphere_norm_sub f (z v') (z v)).symm
      _ = ‖u v • (w v : Y) - u v' • (w v' : Y)‖ := by
        congr 1
        rw [hfz v', hfz v]
        abel
  have hS : ‖s v • (w v : Y) - s v' • (w v' : Y)‖ =
      ‖p v • (v : X) - p v' • (v' : X)‖ := by
    calc
      ‖s v • (w v : Y) - s v' • (w v' : Y)‖ =
          ‖(f (x v) : Y) - (f (x v') : Y)‖ := by
        congr 1
        rw [hfx v, hfx v']
        abel
      _ = ‖(x v : X) - (x v' : X)‖ := sphere_norm_sub f (x v) (x v')
      _ = ‖p v • (v : X) - p v' • (v' : X)‖ := by
        congr 1
        rw [hx v, hx v']
        abel
  have hG : r v * ‖(g v : X) - (g v' : X)‖ ≤
      2 * |u v - u v'| + u v * ‖(w v : Y) - (w v' : Y)‖ := by
    have h₁ := first_mul_norm_sub_le_smul_sub (r v) (r v') hr.le (g v) (g v')
    have h₂ := norm_smul_sub_smul_le_first (u v) (u v') hu (w v) (w v')
    rw [hR, hrdiff] at h₁
    linarith
  have hW : s v * ‖(w v : Y) - (w v' : Y)‖ ≤
      2 * |p v - p v'| + p v * ‖(v : X) - (v' : X)‖ := by
    have h₁ := first_mul_norm_sub_le_smul_sub (s v) (s v') hs.le (w v) (w v')
    have h₂ := norm_smul_sub_smul_le_first (p v) (p v') hp v v'
    rw [hS, hsdiff] at h₁
    linarith
  exact return_pair_scalar_elimination (r v) (s v) (u v) (p v)
    |u v - u v'| |p v - p v'| ‖(g v : X) - (g v' : X)‖
    ‖(w v : Y) - (w v' : Y)‖ ‖(v : X) - (v' : X)‖ hr hs hu hG hW

/-- The same estimate for the totalized ambient map. Membership in the actual
extremal set ensures that every ambient function takes its sphere branch. -/
theorem returnAmbient_pair_estimate
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (M : ℝ) (hb : HasDefectBound f M)
    {v v' : X} (hv : v ∈ extremalSet f y t ht M)
    (hv' : v' ∈ extremalSet f y t ht M) :
    ‖returnAmbient f y t ht v - returnAmbient f y t ht v'‖ ≤
      (uAmbient f y t ht v * pAmbient f y t ht v /
        (rAmbient f y t ht v * sAmbient f y t ht v)) * ‖v - v'‖ +
      2 * |uAmbient f y t ht v - uAmbient f y t ht v'| / rAmbient f y t ht v +
      2 * uAmbient f y t ht v * |pAmbient f y t ht v - pAmbient f y t ht v'| /
        (rAmbient f y t ht v * sAmbient f y t ht v) := by
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb', rfl⟩ := hv'
  simpa only [returnAmbient_coe, pAmbient_coe, sAmbient_coe, uAmbient_coe,
    rAmbient_coe] using returnSphere_pair_estimate f y t ht M hb ha hb'

/-- Restriction to any subset of the actual extremal set, including the closed
invariant convex set constructed from the positive schedule. -/
theorem returnAmbient_pair_estimate_on
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (M : ℝ) (hb : HasDefectBound f M)
    (C : Set X) (hC : C ⊆ extremalSet f y t ht M)
    {v v' : X} (hv : v ∈ C) (hv' : v' ∈ C) :
    ‖returnAmbient f y t ht v - returnAmbient f y t ht v'‖ ≤
      (uAmbient f y t ht v * pAmbient f y t ht v /
        (rAmbient f y t ht v * sAmbient f y t ht v)) * ‖v - v'‖ +
      2 * |uAmbient f y t ht v - uAmbient f y t ht v'| / rAmbient f y t ht v +
      2 * uAmbient f y t ht v * |pAmbient f y t ht v - pAmbient f y t ht v'| /
        (rAmbient f y t ht v * sAmbient f y t ht v) :=
  returnAmbient_pair_estimate f y t ht M hb (hC hv) (hC hv')

end Tingley

end

end OAI


