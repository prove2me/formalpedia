-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_Supports
-- name    : OAI_Analysis_SphereIsometry_Supports
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:06:51.254158+00:00
-- url     : https://prove2.me/theorems/6ab5fcd9-136c-459c-93e1-9ea3ebe89e8f
-- title:
--   Supporting functionals
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords.
--
--   1. **Support at a vector.** A continuous linear functional $\varphi$ with
--   $$
--   \|\varphi\|\le1,\qquad\varphi(a)=\|a\| .
--   $$
--   Supports exist at every vector by Hahn–Banach. They are invariant under positive scaling of $a$, and $-\varphi$ supports $-a$.
--   2. **Extension and restriction.** Functionals on a subspace extend without increasing the norm, and supports restrict to subspaces. So statements about all supports at given vectors can be checked on their finite span.
--   3. **Triangle equality.** $\|x+y\|=\|x\|+\|y\|$ iff $x$ and $y$ have a common support. In particular, unit vectors with a positively weighted triangle equality have a functional of norm at most $1$ equal to $1$ at both.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/Supports.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/Supports.lean by skeleton subtraction
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

namespace OAI

/-!
# Supporting functionals

Supports are continuous real linear functionals of norm at most one which attain
the norm at the specified vector. Hahn–Banach supplies supports and extends them
from any subspace. Restriction and extension relate assertions about every ambient
support to assertions about every support on a finite span.

The results here hold in arbitrary real normed spaces, including the zero space.
-/

namespace Tingley

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A norm-bounded real functional attaining the norm at a vector. -/
def SupportAt (φ : X →L[ℝ] ℝ) (a : X) : Prop :=
  ‖φ‖ ≤ 1 ∧ φ a = ‖a‖

/-- The norm-at-most-one formulation also supplies a support at zero. -/
theorem exists_support (a : X) : ∃ φ : X →L[ℝ] ℝ, SupportAt φ a :=
  exists_dual_vector'' ℝ a

theorem abs_apply_le_norm {φ : X →L[ℝ] ℝ} (hφ : ‖φ‖ ≤ 1) (x : X) :
    |φ x| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs, one_mul] using φ.le_of_opNorm_le hφ x

theorem apply_le_norm {φ : X →L[ℝ] ℝ} (hφ : ‖φ‖ ≤ 1) (x : X) :
    φ x ≤ ‖x‖ :=
  (le_abs_self (φ x)).trans (abs_apply_le_norm hφ x)

@[simp] theorem supportAt_zero_iff (φ : X →L[ℝ] ℝ) :
    SupportAt φ (0 : X) ↔ ‖φ‖ ≤ 1 := by
  simp [SupportAt]

theorem SupportAt.smul_nonneg {φ : X →L[ℝ] ℝ} {a : X}
    (h : SupportAt φ a) {c : ℝ} (hc : 0 ≤ c) : SupportAt φ (c • a) := by
  refine ⟨h.1, ?_⟩
  simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, h.2]

theorem supportAt_pos_smul_iff (φ : X →L[ℝ] ℝ) (a : X)
    {c : ℝ} (hc : 0 < c) : SupportAt φ (c • a) ↔ SupportAt φ a := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have heq := h.2
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at heq
    exact mul_left_cancel₀ (ne_of_gt hc) heq
  · intro h
    exact h.smul_nonneg hc.le

@[simp] theorem supportAt_neg_iff (φ : X →L[ℝ] ℝ) (a : X) :
    SupportAt (-φ) (-a) ↔ SupportAt φ a := by
  simp [SupportAt]

theorem SupportAt.neg {φ : X →L[ℝ] ℝ} {a : X} (h : SupportAt φ a) :
    SupportAt (-φ) (-a) :=
  (supportAt_neg_iff φ a).2 h

theorem SupportAt.subgradient {φ : X →L[ℝ] ℝ} {a : X}
    (h : SupportAt φ a) (z : X) : φ (z - a) ≤ ‖z‖ - ‖a‖ := by
  rw [map_sub, h.2]
  exact sub_le_sub_right (apply_le_norm h.1 z) ‖a‖

/-- Hahn–Banach extends from any real subspace without changing the norm. -/
theorem extension_norm_eq (U : Submodule ℝ X) (φ : U →L[ℝ] ℝ) :
    ∃ Φ : X →L[ℝ] ℝ, (∀ u : U, Φ (u : X) = φ u) ∧ ‖Φ‖ = ‖φ‖ :=
  _root_.exists_extension_norm_eq U φ

theorem supportAt_extension (U : Submodule ℝ X) (a : U)
    (φ : U →L[ℝ] ℝ) (h : SupportAt φ a) :
    ∃ Φ : X →L[ℝ] ℝ,
      (∀ u : U, Φ (u : X) = φ u) ∧ SupportAt Φ (a : X) := by
  obtain ⟨Φ, hΦ, hnorm⟩ := extension_norm_eq U φ
  exact ⟨Φ, hΦ, ⟨hnorm.trans_le h.1, (hΦ a).trans h.2⟩⟩

theorem norm_restrict_le (U : Submodule ℝ X) (φ : X →L[ℝ] ℝ) :
    ‖φ.comp U.subtypeL‖ ≤ ‖φ‖ :=
  (φ.comp U.subtypeL).opNorm_le_bound (norm_nonneg φ) fun u => φ.le_opNorm (u : X)

theorem SupportAt.restrict (U : Submodule ℝ X)
    {φ : X →L[ℝ] ℝ} (a : U) (h : SupportAt φ (a : X)) :
    SupportAt (φ.comp U.subtypeL) a :=
  ⟨(norm_restrict_le U φ).trans h.1, h.2⟩

/-- Universal assertions about support evaluations can be made on any subspace
containing the two vectors. This permits using the dual of their finite span. -/
theorem forall_supportAt_apply_iff_submodule (U : Submodule ℝ X)
    (a b : U) (P : ℝ → Prop) :
    (∀ φ : X →L[ℝ] ℝ, SupportAt φ (a : X) → P (φ (b : X))) ↔
    (∀ ψ : U →L[ℝ] ℝ, SupportAt ψ a → P (ψ b)) := by
  constructor
  · intro h ψ hψ
    obtain ⟨Φ, hΦ, hsupport⟩ := supportAt_extension U a ψ hψ
    simpa only [hΦ b] using h Φ hsupport
  · intro h Φ hΦ
    exact h (Φ.comp U.subtypeL) (SupportAt.restrict U a hΦ)

/-- Triangle equality is equivalent to the existence of a common support. -/
theorem norm_add_eq_iff_exists_common_supportAt (x y : X) :
    ‖x + y‖ = ‖x‖ + ‖y‖ ↔
      ∃ φ : X →L[ℝ] ℝ, SupportAt φ x ∧ SupportAt φ y := by
  constructor
  · intro heq
    obtain ⟨φ, hφ⟩ := exists_support (x + y)
    have hx := apply_le_norm hφ.1 x
    have hy := apply_le_norm hφ.1 y
    have hsum : φ x + φ y = ‖x‖ + ‖y‖ := by
      calc
        φ x + φ y = φ (x + y) := (map_add φ x y).symm
        _ = ‖x + y‖ := hφ.2
        _ = ‖x‖ + ‖y‖ := heq
    refine ⟨φ, ⟨hφ.1, ?_⟩, ⟨hφ.1, ?_⟩⟩
    · linarith
    · linarith
  · rintro ⟨φ, hx, hy⟩
    apply le_antisymm (norm_add_le x y)
    have h := apply_le_norm hx.1 (x + y)
    rwa [map_add, hx.2, hy.2] at h

/-- Positive weighted triangle equality for unit vectors gives one functional
taking value one at both vectors. No strict convexity is required. -/
theorem common_support_of_norm_add_eq {v w : X}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (heq : ‖α • v + β • w‖ = α + β) :
    ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ φ v = 1 ∧ φ w = 1 := by
  have hsum : ‖α • v + β • w‖ = ‖α • v‖ + ‖β • w‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hα, abs_of_pos hβ,
      hv, hw, mul_one] using heq
  obtain ⟨φ, hvφ, hwφ⟩ :=
    (norm_add_eq_iff_exists_common_supportAt (α • v) (β • w)).mp hsum
  have hv' := (supportAt_pos_smul_iff φ v hα).mp hvφ
  have hw' := (supportAt_pos_smul_iff φ w hβ).mp hwφ
  exact ⟨φ, hv'.1, hv'.2.trans hv, hw'.2.trans hw⟩

end Tingley

end OAI


