-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMap
-- name    : OAI_Analysis_SphereIsometry_ReturnMap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:05:57.7087+00:00
-- url     : https://prove2.me/theorems/b3603991-eca5-411b-a7f5-77fad5b29b0b
-- title:
--   The return map of a sphere isometry
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Fix a bijective sphere isometry $f$, a base point $y\in S_X$ and $t\in(0,1)$; the interior centers are $ty$ and $tf(y)$. For a unit direction $v\in S_X$:
--
--   1. **First contact.** $x(v)=ty+p(v)\,v\in S_X$, with $p(v)$ the contact radius from $ty$.
--   2. **Image side.** $s(v)=\|f(x(v))-tf(y)\|$ and $w(v)=\bigl(f(x(v))-tf(y)\bigr)/s(v)$.
--   3. **Second contact.** $u(v)$ is the contact radius from $tf(y)$ in the direction $-w(v)$, and $z(v)=f^{-1}\bigl(tf(y)-u(v)\,w(v)\bigr)$.
--   4. **Return.** $r(v)=\|z(v)-ty\|$ and
--   $$
--   R(v)=\frac{ty-z(v)}{\|ty-z(v)\|}\in S_X .
--   $$
--   All four radii lie in $[1-t,1+t]$, $x$ is onto $S_X$, and $R$ is continuous on the sphere. Total extensions to $X$, equal to $0$ off the sphere, are also defined.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ReturnMap.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ReturnMap.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
# The actual radial return map

For fixed `f`, `y` and `0 < t < 1`, the two interior centers are `t • y`
and `t • f y`. The map follows the two radial contacts.
The opposite direction is literal vector negation, with no antipodality
assumption on `f`. The ambient extensions are continuous on the unit sphere;
no continuity away from that sphere is asserted.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Literal negation of a unit vector. -/
def sphereNeg (v : UnitSphere X) : UnitSphere X :=
  ⟨-(v : X), by simpa only [norm_neg] using v.property⟩

omit [NormedSpace ℝ X] in
@[simp] theorem sphereNeg_coe (v : UnitSphere X) :
    (sphereNeg v : X) = -(v : X) := rfl

omit [NormedSpace ℝ X] in
theorem continuous_sphereNeg : Continuous (sphereNeg : UnitSphere X → UnitSphere X) :=
  continuous_subtype_val.neg.subtype_mk _

theorem norm_smul_unitSphere (y : UnitSphere X) (t : ℝ) (ht : 0 ≤ t) :
    ‖t • (y : X)‖ = t := by
  rw [norm_smul, Real.norm_of_nonneg ht, y.property, mul_one]

theorem returnCenter_lt_one (y : UnitSphere X) (t : ℝ) (ht : 0 < t ∧ t < 1) :
    ‖t • (y : X)‖ < 1 := by
  rw [norm_smul_unitSphere y t ht.1.le]
  exact ht.2

/-- Distances from any unit point to either interior center have uniform bounds. -/
theorem norm_unit_sub_center_bounds (x y : UnitSphere X) (t : ℝ) (ht : 0 ≤ t) :
    1 - t ≤ ‖(x : X) - t • (y : X)‖ ∧
      ‖(x : X) - t • (y : X)‖ ≤ 1 + t := by
  constructor
  · simpa only [x.property, norm_smul_unitSphere y t ht] using
      norm_sub_norm_le (x : X) (t • (y : X))
  · simpa only [x.property, norm_smul_unitSphere y t ht] using
      norm_sub_le (x : X) (t • (y : X))

theorem unit_sub_center_ne_zero (x y : UnitSphere X) (t : ℝ)
    (ht : 0 < t ∧ t < 1) : (x : X) - t • (y : X) ≠ 0 := by
  intro h
  have hbound := (norm_unit_sub_center_bounds x y t ht.1.le).1
  rw [h, norm_zero] at hbound
  linarith [ht.2]

theorem center_sub_unit_ne_zero (x y : UnitSphere X) (t : ℝ)
    (ht : 0 < t ∧ t < 1) : t • (y : X) - (x : X) ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (unit_sub_center_ne_zero x y t ht)))

/-- The first radial radius. The isometry is an explicit common parameter even
though this first contact only uses the domain center. -/
def pRadius (_f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (v : UnitSphere X) : ℝ :=
  radialRadius (t • (y : X)) (returnCenter_lt_one y t ht) v

variable (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
variable (t : ℝ) (ht : 0 < t ∧ t < 1)

/-- The first contact point `t y + p v`. -/
def xPoint (v : UnitSphere X) : UnitSphere X :=
  ⟨t • (y : X) + pRadius f y t ht v • (v : X),
    norm_radialRadius (t • (y : X)) (returnCenter_lt_one y t ht) v⟩

def sRadius (v : UnitSphere X) : ℝ :=
  ‖(f (xPoint f y t ht v) : Y) - t • (f y : Y)‖

/-- The image-side outward unit direction. -/
def wDirection (v : UnitSphere X) : UnitSphere Y :=
  normalize ((f (xPoint f y t ht v) : Y) - t • (f y : Y))
    (unit_sub_center_ne_zero (f (xPoint f y t ht v)) (f y) t ht)

/-- The second radial contact uses the negative of the actual direction `w`. -/
def uRadius (v : UnitSphere X) : ℝ :=
  radialRadius (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
    (sphereNeg (wDirection f y t ht v))

def zPoint (v : UnitSphere X) : UnitSphere X :=
  f.symm (radialContact (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
    (sphereNeg (wDirection f y t ht v)))

def rRadius (v : UnitSphere X) : ℝ :=
  ‖(zPoint f y t ht v : X) - t • (y : X)‖

/-- The genuine return map on the unit sphere. -/
def returnSphere (v : UnitSphere X) : UnitSphere X :=
  normalize (t • (y : X) - (zPoint f y t ht v : X))
    (center_sub_unit_ne_zero (zPoint f y t ht v) y t ht)

omit [NormedSpace ℝ Y] in
theorem pRadius_pos (v : UnitSphere X) : 0 < pRadius f y t ht v :=
  radialRadius_pos (t • (y : X)) (returnCenter_lt_one y t ht) v

omit [NormedSpace ℝ Y] in
theorem pRadius_bounds (v : UnitSphere X) :
    1 - t ≤ pRadius f y t ht v ∧ pRadius f y t ht v ≤ 1 + t := by
  simpa only [pRadius, norm_smul_unitSphere y t ht.1.le] using
    radialRadius_bounds (t • (y : X)) (returnCenter_lt_one y t ht) v

theorem sRadius_bounds (v : UnitSphere X) :
    1 - t ≤ sRadius f y t ht v ∧ sRadius f y t ht v ≤ 1 + t :=
  norm_unit_sub_center_bounds (f (xPoint f y t ht v)) (f y) t ht.1.le

theorem sRadius_pos (v : UnitSphere X) : 0 < sRadius f y t ht v :=
  (sub_pos.mpr ht.2).trans_le (sRadius_bounds f y t ht v).1

theorem uRadius_pos (v : UnitSphere X) : 0 < uRadius f y t ht v :=
  radialRadius_pos (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
    (sphereNeg (wDirection f y t ht v))

theorem uRadius_bounds (v : UnitSphere X) :
    1 - t ≤ uRadius f y t ht v ∧ uRadius f y t ht v ≤ 1 + t := by
  simpa only [uRadius, norm_smul_unitSphere (f y) t ht.1.le] using
    radialRadius_bounds (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
      (sphereNeg (wDirection f y t ht v))

theorem rRadius_bounds (v : UnitSphere X) :
    1 - t ≤ rRadius f y t ht v ∧ rRadius f y t ht v ≤ 1 + t :=
  norm_unit_sub_center_bounds (zPoint f y t ht v) y t ht.1.le

theorem rRadius_pos (v : UnitSphere X) : 0 < rRadius f y t ht v :=
  (sub_pos.mpr ht.2).trans_le (rRadius_bounds f y t ht v).1

theorem radii_bounds (v : UnitSphere X) :
    pRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) ∧
      sRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) ∧
      uRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) ∧
      rRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) :=
  ⟨pRadius_bounds f y t ht v, sRadius_bounds f y t ht v,
    uRadius_bounds f y t ht v, rRadius_bounds f y t ht v⟩

omit [NormedSpace ℝ Y] in
theorem xPoint_eq (v : UnitSphere X) :
    (xPoint f y t ht v : X) = t • (y : X) + pRadius f y t ht v • (v : X) := rfl

theorem fxPoint_eq (v : UnitSphere X) :
    (f (xPoint f y t ht v) : Y) =
      t • (f y : Y) + sRadius f y t ht v • (wDirection f y t ht v : Y) := by
  have h : sRadius f y t ht v • (wDirection f y t ht v : Y) =
      (f (xPoint f y t ht v) : Y) - t • (f y : Y) :=
    norm_smul_normalize _ _
  rw [h]
  abel

theorem fzPoint_eq (v : UnitSphere X) :
    (f (zPoint f y t ht v) : Y) =
      t • (f y : Y) - uRadius f y t ht v • (wDirection f y t ht v : Y) := by
  simp only [zPoint, IsometryEquiv.apply_symm_apply, radialContact_coe,
    sphereNeg_coe, smul_neg, sub_eq_add_neg, uRadius]

theorem zPoint_eq (v : UnitSphere X) :
    (zPoint f y t ht v : X) =
      t • (y : X) - rRadius f y t ht v • (returnSphere f y t ht v : X) := by
  have h : ‖t • (y : X) - (zPoint f y t ht v : X)‖ •
      (returnSphere f y t ht v : X) = t • (y : X) - (zPoint f y t ht v : X) :=
    norm_smul_normalize _ _
  rw [norm_sub_rev] at h
  change rRadius f y t ht v • (returnSphere f y t ht v : X) = _ at h
  rw [h]
  abel

omit [NormedSpace ℝ Y] in
theorem norm_xPoint_sub_center (v : UnitSphere X) :
    ‖(xPoint f y t ht v : X) - t • (y : X)‖ = pRadius f y t ht v := by
  rw [xPoint_eq, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (pRadius_pos f y t ht v).le, v.property, mul_one]

theorem norm_zPoint_sub_center (v : UnitSphere X) :
    ‖(zPoint f y t ht v : X) - t • (y : X)‖ = rRadius f y t ht v := rfl

omit [NormedSpace ℝ Y] in
/-- Radial uniqueness recovers any given unit endpoint from its direction. -/
theorem pRadius_normalize_sub (x : UnitSphere X) :
    pRadius f y t ht (normalize ((x : X) - t • (y : X))
      (unit_sub_center_ne_zero x y t ht)) = ‖(x : X) - t • (y : X)‖ := by
  symm
  apply radialRadius_unique (t • (y : X)) (returnCenter_lt_one y t ht) _ (norm_nonneg _)
  rw [norm_smul_normalize]
  have he : t • (y : X) + ((x : X) - t • (y : X)) = (x : X) := by abel
  rw [he]
  exact x.property

omit [NormedSpace ℝ Y] in
theorem xPoint_normalize_sub (x : UnitSphere X) :
    xPoint f y t ht (normalize ((x : X) - t • (y : X))
      (unit_sub_center_ne_zero x y t ht)) = x := by
  apply Subtype.ext
  rw [xPoint_eq, pRadius_normalize_sub, norm_smul_normalize]
  abel

omit [NormedSpace ℝ Y] in
theorem xPoint_surjective : Function.Surjective (xPoint f y t ht) := by
  intro x
  exact ⟨normalize ((x : X) - t • (y : X)) (unit_sub_center_ne_zero x y t ht),
    xPoint_normalize_sub f y t ht x⟩

/-- Normalizing a continuous everywhere-nonzero map preserves continuity. -/
theorem continuous_normalize_map {A : Type*} [TopologicalSpace A]
    (g : A → X) (hg : Continuous g) (hzero : ∀ a, g a ≠ 0) :
    Continuous (fun a => normalize (g a) (hzero a)) := by
  exact ((hg.norm.inv₀ (fun a => norm_ne_zero_iff.mpr (hzero a))).smul hg).subtype_mk _

omit [NormedSpace ℝ Y] in
theorem continuous_pRadius : Continuous (pRadius f y t ht) :=
  continuous_radialRadius (t • (y : X)) (returnCenter_lt_one y t ht)

omit [NormedSpace ℝ Y] in
theorem continuous_xPoint : Continuous (xPoint f y t ht) :=
  continuous_radialContact (t • (y : X)) (returnCenter_lt_one y t ht)

theorem continuous_sRadius : Continuous (sRadius f y t ht) :=
  ((continuous_subtype_val.comp (f.continuous.comp (continuous_xPoint f y t ht))).sub
    continuous_const).norm

theorem continuous_wDirection : Continuous (wDirection f y t ht) :=
  continuous_normalize_map _
    ((continuous_subtype_val.comp (f.continuous.comp (continuous_xPoint f y t ht))).sub
      continuous_const)
    (fun v => unit_sub_center_ne_zero (f (xPoint f y t ht v)) (f y) t ht)

theorem continuous_zPoint : Continuous (zPoint f y t ht) :=
  f.symm.continuous.comp
    ((continuous_radialContact (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)).comp
      (continuous_sphereNeg.comp (continuous_wDirection f y t ht)))

theorem continuous_returnSphere : Continuous (returnSphere f y t ht) :=
  continuous_normalize_map _
    (continuous_const.sub (continuous_subtype_val.comp (continuous_zPoint f y t ht)))
    (fun v => center_sub_unit_ne_zero (zPoint f y t ht v) y t ht)

/-- Total ambient functions, used only on the sphere by the convex-set argument. -/
def pAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then pRadius f y t ht ⟨v, hv⟩ else 0

def sAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then sRadius f y t ht ⟨v, hv⟩ else 0

def uAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then uRadius f y t ht ⟨v, hv⟩ else 0

def rAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then rRadius f y t ht ⟨v, hv⟩ else 0

def returnAmbient (v : X) : X :=
  if hv : ‖v‖ = 1 then (returnSphere f y t ht ⟨v, hv⟩ : X) else 0

omit [NormedSpace ℝ Y] in
@[simp] theorem pAmbient_coe (v : UnitSphere X) :
    pAmbient f y t ht (v : X) = pRadius f y t ht v := by
  simp only [pAmbient, v.property, dite_eq_left]

@[simp] theorem sAmbient_coe (v : UnitSphere X) :
    sAmbient f y t ht (v : X) = sRadius f y t ht v := by
  simp only [sAmbient, v.property, dite_eq_left]

@[simp] theorem uAmbient_coe (v : UnitSphere X) :
    uAmbient f y t ht (v : X) = uRadius f y t ht v := by
  simp only [uAmbient, v.property, dite_eq_left]

@[simp] theorem rAmbient_coe (v : UnitSphere X) :
    rAmbient f y t ht (v : X) = rRadius f y t ht v := by
  simp only [rAmbient, v.property, dite_eq_left]

@[simp] theorem returnAmbient_coe (v : UnitSphere X) :
    returnAmbient f y t ht (v : X) = (returnSphere f y t ht v : X) := by
  simp only [returnAmbient, v.property, dite_eq_left]

theorem continuousOn_returnAmbient :
    ContinuousOn (returnAmbient f y t ht) {v : X | ‖v‖ = 1} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : ({v : X | ‖v‖ = 1}).domRestrict (returnAmbient f y t ht) =
      fun v : UnitSphere X => (returnSphere f y t ht v : X) := by
    funext v
    exact returnAmbient_coe f y t ht v
  rw [he]
  exact continuous_subtype_val.comp (continuous_returnSphere f y t ht)

end Tingley

end

end OAI


