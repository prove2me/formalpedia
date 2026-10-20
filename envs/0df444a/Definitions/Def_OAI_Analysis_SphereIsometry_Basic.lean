-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_Basic
-- name    : OAI_Analysis_SphereIsometry_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T20:57:24.336451+00:00
-- url     : https://prove2.me/theorems/e198ce95-4277-41e2-a646-444ad74e0bee
-- title:
--   Signed cross-radius defects of a sphere isometry
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $f:S_X\to S_Y$ be a bijective isometry of unit spheres, with the ambient distances.
--
--   1. **Signed defect.** For $q\in\mathbb R$ and $x,y\in S_X$,
--   $$
--   \delta_q(x,y)=\|f(x)-q\,f(y)\|-\|x-q\,y\| .
--   $$
--   It vanishes at $q=0$ and $q=1$, it is $2$-Lipschitz in $q$, and $|\delta_q|\le\min(2q,1)$ on $[0,1]$. Moreover $\delta^{f^{-1}}_q(fx,fy)=-\delta^f_q(x,y)$.
--   2. **Defect bound.** $f$ has defect bound $M$ if $|\delta_q(x,y)|\le M$ for all $q\in[0,1]$ and all $x,y$.
--   3. **Maximal defect.** The supremum $M_f$ of all $|\delta_q(x,y)|$. It lies in $[0,1]$, is the same for $f^{-1}$, and is itself a defect bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/Basic.lean by skeleton subtraction
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

namespace OAI

/-!
# Sphere maps and the maximal cross-radius defect

The sphere carries the ambient distance. All defects below use the actual sphere
isometry and ordinary real scalar multiplication; no extension law is assumed.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
@[simp] theorem UnitSphere.norm_coe (x : UnitSphere X) : ‖(x : X)‖ = 1 := x.property

@[simp] theorem normalize_coe (x : X) (hx : x ≠ 0) :
    (normalize x hx : X) = ‖x‖⁻¹ • x := rfl

theorem norm_smul_normalize (x : X) (hx : x ≠ 0) :
    ‖x‖ • (normalize x hx : X) = x := by
  rw [normalize_coe, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

instance UnitSphere.instNonempty [Nontrivial X] : Nonempty (UnitSphere X) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  exact ⟨normalize x hx⟩

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem sphere_norm_sub (f : UnitSphere X ≃ᵢ UnitSphere Y) (x y : UnitSphere X) :
    ‖(f x : Y) - (f y : Y)‖ = ‖(x : X) - (y : X)‖ := by
  simpa only [Subtype.dist_eq, dist_eq_norm] using f.dist_eq x y

def signedDefect (f : UnitSphere X ≃ᵢ UnitSphere Y) (q : ℝ)
    (x y : UnitSphere X) : ℝ :=
  ‖(f x : Y) - q • (f y : Y)‖ - ‖(x : X) - q • (y : X)‖

def HasDefectBound (f : UnitSphere X ≃ᵢ UnitSphere Y) (M : ℝ) : Prop :=
  ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ x y : UnitSphere X, |signedDefect f q x y| ≤ M

def absoluteDefects (f : UnitSphere X ≃ᵢ UnitSphere Y) : Set ℝ :=
  {d | ∃ q ∈ Set.Icc (0 : ℝ) 1, ∃ x y : UnitSphere X, d = |signedDefect f q x y|}

def maxDefect (f : UnitSphere X ≃ᵢ UnitSphere Y) : ℝ := sSup (absoluteDefects f)

@[simp] theorem signedDefect_zero (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (x y : UnitSphere X) : signedDefect f 0 x y = 0 := by
  simp [signedDefect]

@[simp] theorem signedDefect_one (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (x y : UnitSphere X) : signedDefect f 1 x y = 0 := by
  simp [signedDefect, sphere_norm_sub]

theorem signedDefect_symm (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (q : ℝ) (x y : UnitSphere X) :
    signedDefect f.symm q (f x) (f y) = -signedDefect f q x y := by
  simp only [signedDefect, IsometryEquiv.symm_apply_apply]
  ring

theorem HasDefectBound.symm {f : UnitSphere X ≃ᵢ UnitSphere Y} {M : ℝ}
    (h : HasDefectBound f M) : HasDefectBound f.symm M := by
  intro q hq x y
  obtain ⟨a, rfl⟩ := f.surjective x
  obtain ⟨b, rfl⟩ := f.surjective y
  simpa only [signedDefect_symm, abs_neg] using h q hq a b

theorem norm_sub_smul_lipschitz (x : X) (y : UnitSphere X) (q r : ℝ) :
    |‖x - q • (y : X)‖ - ‖x - r • (y : X)‖| ≤ |q - r| := by
  calc
    |‖x - q • (y : X)‖ - ‖x - r • (y : X)‖| ≤
        ‖(x - q • (y : X)) - (x - r • (y : X))‖ := abs_norm_sub_norm_le _ _
    _ = ‖(r - q) • (y : X)‖ := by
      congr 1
      rw [sub_smul]
      abel
    _ = |q - r| := by simp [norm_smul, Real.norm_eq_abs, abs_sub_comm]

theorem signedDefect_lipschitz (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (q r : ℝ) (x y : UnitSphere X) :
    |signedDefect f q x y - signedDefect f r x y| ≤ 2 * |q - r| := by
  have hx := norm_sub_smul_lipschitz (x : X) y q r
  have hy := norm_sub_smul_lipschitz (f x : Y) (f y) q r
  have ht := abs_sub
    (‖(f x : Y) - q • (f y : Y)‖ - ‖(f x : Y) - r • (f y : Y)‖)
    (‖(x : X) - q • (y : X)‖ - ‖(x : X) - r • (y : X)‖)
  have he : signedDefect f q x y - signedDefect f r x y =
      (‖(f x : Y) - q • (f y : Y)‖ - ‖(f x : Y) - r • (f y : Y)‖) -
      (‖(x : X) - q • (y : X)‖ - ‖(x : X) - r • (y : X)‖) := by
    unfold signedDefect
    ring
  rw [he]
  linarith

theorem signedDefect_le_endpoints (f : UnitSphere X ≃ᵢ UnitSphere Y)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (x y : UnitSphere X) :
    |signedDefect f q x y| ≤ 2 * q ∧
      |signedDefect f q x y| ≤ 2 * (1 - q) := by
  constructor
  · simpa [abs_of_nonneg hq.1] using signedDefect_lipschitz f q 0 x y
  · simpa [abs_of_nonpos (sub_nonpos.mpr hq.2)] using
      signedDefect_lipschitz f q 1 x y

theorem signedDefect_abs_le_one (f : UnitSphere X ≃ᵢ UnitSphere Y)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (x y : UnitSphere X) :
    |signedDefect f q x y| ≤ 1 := by
  obtain ⟨h0, h1⟩ := signedDefect_le_endpoints f hq x y
  linarith

theorem absoluteDefects_bddAbove (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    BddAbove (absoluteDefects f) := by
  refine ⟨1, ?_⟩
  rintro d ⟨q, hq, x, y, rfl⟩
  exact signedDefect_abs_le_one f hq x y

theorem zero_mem_absoluteDefects [Nonempty (UnitSphere X)]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : 0 ∈ absoluteDefects f := by
  let x : UnitSphere X := Classical.choice inferInstance
  exact ⟨0, ⟨le_rfl, zero_le_one⟩, x, x, by simp⟩

theorem hasDefectBound_maxDefect (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    HasDefectBound f (maxDefect f) := by
  intro q hq x y
  exact le_csSup (absoluteDefects_bddAbove f) ⟨q, hq, x, y, rfl⟩

theorem maxDefect_nonneg [Nonempty (UnitSphere X)]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : 0 ≤ maxDefect f :=
  le_csSup (absoluteDefects_bddAbove f) (zero_mem_absoluteDefects f)

theorem absoluteDefects_symm (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    absoluteDefects f.symm = absoluteDefects f := by
  ext d
  constructor
  · rintro ⟨q, hq, x, y, hd⟩
    obtain ⟨a, rfl⟩ := f.surjective x
    obtain ⟨b, rfl⟩ := f.surjective y
    exact ⟨q, hq, a, b, by simpa only [signedDefect_symm, abs_neg] using hd⟩
  · rintro ⟨q, hq, x, y, hd⟩
    exact ⟨q, hq, f x, f y, by simpa only [signedDefect_symm, abs_neg] using hd⟩

@[simp] theorem maxDefect_symm (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    maxDefect f.symm = maxDefect f := by
  unfold maxDefect
  rw [absoluteDefects_symm]

theorem signedDefect_eq_zero_of_bound_zero {f : UnitSphere X ≃ᵢ UnitSphere Y}
    (h : HasDefectBound f 0) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (x y : UnitSphere X) : signedDefect f q x y = 0 := by
  exact abs_nonpos_iff.mp (h q hq x y)

end Tingley

end

end OAI


