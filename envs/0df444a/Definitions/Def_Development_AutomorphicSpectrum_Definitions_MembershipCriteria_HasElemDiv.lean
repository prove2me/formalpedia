-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_HasElemDiv
-- name    : Development_AutomorphicSpectrum_Definitions_MembershipCriteria_HasElemDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:47.373106+00:00
-- url     : https://prove2.me/theorems/3c5cb4df-1ab5-45df-b94d-2e0740d7e686
-- title:
--   Has Elem Div
-- statement:
--   Definitions and structural lemmas for Has Elem Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/HasElemDiv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SplitRow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
def om (κ₁ κ₂ : kˣ →* Circle) (g : GL r k) (h : GL n k) (Φ : Matrix r n k → ℂ) : Matrix r n k → ℂ := fun x =>
  (κ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((κ₂ (Matrix.GeneralLinearGroup.det h))⁻¹ : Circle) *
    ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ) / 2) : ℝ) : ℂ) *
    ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det h) ^ ((Fintype.card r : ℝ) / 2) : ℝ) : ℂ) *
    Φ ((g⁻¹ : GL r k).val * x * h.val)
def rho (ψ : AddChar k Circle) (w : Matrix r n k × Matrix n r k) (Φ : Matrix r n k → ℂ) : Matrix r n k → ℂ := fun x =>
  (ψ ((x * w.2).trace + (w.1 * w.2).trace / 2) : ℂ) * Φ (x + w.1)
def sympl (w w' : Matrix r n k × Matrix n r k) : k := (w.1 * w'.2).trace - (w'.1 * w.2).trace
def act (g : GL r k) (h : GL n k) (w : Matrix r n k × Matrix n r k) : Matrix r n k × Matrix n r k :=
  (g.val * w.1 * (h⁻¹ : GL n k).val, h.val * w.2 * (g⁻¹ : GL r k).val)
def intM (k : Type) [Field k] [ValuativeRel k] (a b : Type) : AddSubgroup (Matrix a b k) where
  carrier := {x | ∀ i j, x i j ∈ 𝒪[k]}
  zero_mem' := fun _ _ => zero_mem _
  add_mem' := fun hx hy i j => add_mem (hx i j) (hy i j)
  neg_mem' := fun hx i j => neg_mem (hx i j)
def lat0 (k : Type) [Field k] [ValuativeRel k] (r n : Type) : AddSubgroup (Matrix r n k × Matrix n r k) :=
  (intM k r n).prod (intM k n r)
def latOf (g : GL r k) (h : GL n k) : AddSubgroup (Matrix r n k × Matrix n r k) where
  carrier := {w | act g⁻¹ h⁻¹ w ∈ lat0 k r n}
  zero_mem' := by
    have : act g⁻¹ h⁻¹ (0 : Matrix r n k × Matrix n r k) = 0 := by simp [act]
    show act g⁻¹ h⁻¹ (0 : Matrix r n k × Matrix n r k) ∈ lat0 k r n
    rw [this]; exact zero_mem _
  add_mem' := by
    intro a b ha hb
    have : act g⁻¹ h⁻¹ (a + b) = act g⁻¹ h⁻¹ a + act g⁻¹ h⁻¹ b := by
      simp [act, Matrix.mul_add, Matrix.add_mul]
    show act g⁻¹ h⁻¹ (a + b) ∈ lat0 k r n
    rw [this]; exact add_mem ha hb
  neg_mem' := by
    intro a ha
    have : act g⁻¹ h⁻¹ (-a) = -act g⁻¹ h⁻¹ a := by simp [act]
    show act g⁻¹ h⁻¹ (-a) ∈ lat0 k r n
    rw [this]; exact neg_mem ha
def vac (k : Type) [Field k] [ValuativeRel k] (r n : Type) : Matrix r n k → ℂ :=
  Set.indicator (intM k r n : Set (Matrix r n k)) fun _ => 1
def al (ψ : AddChar k Circle) (w : Matrix r n k × Matrix n r k) : ℂ := (ψ (-((w.1 * w.2).trace / 2)) : ℂ)
def HasElemDiv (ϖ : kˣ) (h : GL n k) (a : n → ℤ) : Prop :=
  ∃ k₁ ∈ GlobalTheory.SplitWeil.KO k n, ∃ k₂ ∈ GlobalTheory.SplitWeil.KO k n,
    h.val = k₁.val * Matrix.diagonal (fun i => ((ϖ ^ a i : kˣ) : k)) * k₂.val
end GlobalTheory.CompanionTheory.SplitRow


