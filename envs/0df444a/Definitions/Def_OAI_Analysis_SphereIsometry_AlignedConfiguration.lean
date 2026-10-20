-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_AlignedConfiguration
-- name    : OAI_Analysis_SphereIsometry_AlignedConfiguration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:15:01.293999+00:00
-- url     : https://prove2.me/theorems/7fc306c3-189e-4d24-8c6e-fd59dc338062
-- title:
--   Aligned chord configurations
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Fix a sphere isometry $f$, a point $y$, $t\in(0,1)$ and $M$.
--
--   1. **Aligned configuration.** Unit vectors $x,z,v\in S_X$, $w\in S_Y$ and positive radii $p,r,s,u$ with
--   $$
--   x=ty+pv,\quad z=ty-rv,\quad f(x)=tf(y)+sw,\quad f(z)=tf(y)-uw,
--   $$
--   together with $s-p=M$, $r-u=M$, $p+r=s+u$ and $p+r\le2$. So the chord $[z,x]$ through $ty$ is mapped to a chord through $tf(y)$ with the defect $M$ at both ends.
--   2. **Derived quantities.** $d=p+r$, $A=p/d$ and $B=u/d$, with $A+B=1-M/d<1$ and $sr-up=Md$.
--   3. **Inverse configuration.** For $f^{-1}$, exchange the endpoints and negate both directions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/AlignedConfiguration.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/AlignedConfiguration.lean by skeleton subtraction
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

namespace OAI

/-!
# Aligned sphere chords

The record retains the four actual endpoint equations. Its inverse exchanges the
endpoints and negates the two direction vectors literally; it uses no oddness
property of the sphere isometry.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

structure AlignedConfiguration
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X) (t M : ℝ) where
  x : UnitSphere X
  z : UnitSphere X
  v : UnitSphere X
  w : UnitSphere Y
  p : ℝ
  r : ℝ
  s : ℝ
  u : ℝ
  p_pos : 0 < p
  r_pos : 0 < r
  s_pos : 0 < s
  u_pos : 0 < u
  x_eq : (x : X) = t • (y : X) + p • (v : X)
  z_eq : (z : X) = t • (y : X) - r • (v : X)
  fx_eq : (f x : Y) = t • (f y : Y) + s • (w : Y)
  fz_eq : (f z : Y) = t • (f y : Y) - u • (w : Y)
  s_sub_p : s - p = M
  r_sub_u : r - u = M
  chord_sum : p + r = s + u
  chord_le_two : p + r ≤ 2

namespace AlignedConfiguration

variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}
variable (C : AlignedConfiguration f y t M)

def d : ℝ := C.p + C.r

def A : ℝ := C.p / C.d

def B : ℝ := C.u / C.d

theorem d_pos : 0 < C.d := add_pos C.p_pos C.r_pos

theorem d_ne_zero : C.d ≠ 0 := ne_of_gt C.d_pos

theorem d_eq_s_add_u : C.d = C.s + C.u := C.chord_sum

theorem A_pos : 0 < C.A := div_pos C.p_pos C.d_pos

theorem B_lt_one : C.B < 1 := by
  apply (div_lt_one C.d_pos).2
  rw [C.d_eq_s_add_u]
  linarith [C.s_pos]

theorem A_add_B : C.A + C.B = 1 - M / C.d := by
  dsimp only [A, B]
  rw [← add_div, eq_sub_iff_add_eq, ← add_div]
  have hsum : C.p + C.u + M = C.d := by
    dsimp only [d]
    linarith [C.r_sub_u]
  rw [hsum, div_self C.d_ne_zero]

theorem A_add_B_lt_one (hM : 0 < M) : C.A + C.B < 1 := by
  rw [C.A_add_B]
  have hMd := div_pos hM C.d_pos
  linarith

theorem one_sub_B : 1 - C.B = C.s / C.d := by
  apply (eq_div_iff C.d_ne_zero).2
  dsimp only [B]
  rw [sub_mul, one_mul, div_mul_cancel₀ _ C.d_ne_zero, C.d_eq_s_add_u]
  ring

theorem p_eq_d_mul_A : C.p = C.d * C.A := by
  simpa only [A, mul_comm] using (div_mul_cancel₀ C.p C.d_ne_zero).symm

theorem chord_identity : C.s * C.r - C.u * C.p = M * C.d := by
  calc
    C.s * C.r - C.u * C.p = (C.s - C.p) * C.r + C.p * (C.r - C.u) := by ring
    _ = M * C.r + C.p * M := by rw [C.s_sub_p, C.r_sub_u]
    _ = M * C.d := by dsimp only [d]; ring

/-- Exchange the endpoints and literally negate both chord directions. -/
def inverse : AlignedConfiguration f.symm (f y) t M where
  x := f C.z
  z := f C.x
  v := ⟨-(C.w : Y), by simp⟩
  w := ⟨-(C.v : X), by simp⟩
  p := C.u
  r := C.s
  s := C.r
  u := C.p
  p_pos := C.u_pos
  r_pos := C.s_pos
  s_pos := C.r_pos
  u_pos := C.p_pos
  x_eq := by simpa only [smul_neg, sub_eq_add_neg] using C.fz_eq
  z_eq := by simpa only [smul_neg, sub_neg_eq_add] using C.fx_eq
  fx_eq := by
    simpa only [IsometryEquiv.symm_apply_apply, smul_neg, sub_eq_add_neg] using C.z_eq
  fz_eq := by
    simpa only [IsometryEquiv.symm_apply_apply, smul_neg, sub_neg_eq_add] using C.x_eq
  s_sub_p := C.r_sub_u
  r_sub_u := C.s_sub_p
  chord_sum := by linarith [C.chord_sum]
  chord_le_two := by linarith [C.chord_sum, C.chord_le_two]

@[simp] theorem inverse_x : C.inverse.x = f C.z := rfl

@[simp] theorem inverse_z : C.inverse.z = f C.x := rfl

@[simp] theorem inverse_v_coe : (C.inverse.v : Y) = -(C.w : Y) := rfl

@[simp] theorem inverse_w_coe : (C.inverse.w : X) = -(C.v : X) := rfl

@[simp] theorem inverse_p : C.inverse.p = C.u := rfl

@[simp] theorem inverse_r : C.inverse.r = C.s := rfl

@[simp] theorem inverse_s : C.inverse.s = C.r := rfl

@[simp] theorem inverse_u : C.inverse.u = C.p := rfl

@[simp] theorem inverse_d : C.inverse.d = C.d := by
  change C.u + C.s = C.p + C.r
  linarith [C.chord_sum]

@[simp] theorem inverse_A : C.inverse.A = C.B := by
  simp only [A, B, inverse_p, inverse_d]

@[simp] theorem inverse_B : C.inverse.B = C.A := by
  simp only [A, B, inverse_u, inverse_d]

end AlignedConfiguration

end Tingley

end

end OAI


