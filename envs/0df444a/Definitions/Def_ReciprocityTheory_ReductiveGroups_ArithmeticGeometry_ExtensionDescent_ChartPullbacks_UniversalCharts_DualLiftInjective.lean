-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:05.315907+00:00
-- url     : https://prove2.me/theorems/dfa79a33-9a0b-4d4f-9349-798857ee5c6e
-- title:
--   Dual Lift Injective
-- statement:
--   Definitions and structural lemmas for Dual Lift Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/DualLiftInjective.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_IsUnivChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
abbrev fstD (R : Type) [CommRing R] : DualNumber R →ₐ[R] R := TrivSqZeroExt.fstHom R R R
theorem kerD_sq : (RingHom.ker (fstD R)) ^ (1 + 1) = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  have ha0 : a.fst = 0 := ha
  have hb0 : b.fst = 0 := hb
  rw [Ideal.mem_bot, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha0 rfl,
    show b = TrivSqZeroExt.inr b.snd from TrivSqZeroExt.ext hb0 rfl, TrivSqZeroExt.inr_mul_inr]
theorem inr_mem_kerD (t : R) : (TrivSqZeroExt.inr t : DualNumber R) ∈ RingHom.ker (fstD R) :=
  TrivSqZeroExt.fst_inr R t
def dualLift {n : ℕ} (c : Fin n → R) : JetR R (Fin n) 1 →ₐ[R] DualNumber R :=
  jetLift R (RingHom.ker (fstD R)) kerD_sq (fun j => TrivSqZeroExt.inr (c j)) (fun j => inr_mem_kerD _)
theorem dualLift_zR {n : ℕ} (c : Fin n → R) (j : Fin n) : dualLift c (zR 1 j) = TrivSqZeroExt.inr (c j) :=
  jetLift_zR _ _ _ _ j
theorem fstD_comp_dualLift {n : ℕ} (c : Fin n → R) : (fstD R).comp (dualLift c) = jetAug R (Fin n) 1 :=
  jet_ext fun j => by rw [AlgHom.comp_apply, dualLift_zR, jetAug_zR]; exact inr_mem_kerD (c j)
theorem eq_dualLift {n : ℕ} (ψ : JetR R (Fin n) 1 →ₐ[R] DualNumber R) (h : (fstD R).comp ψ = jetAug R (Fin n) 1) :
    ψ = dualLift (fun j => (ψ (zR 1 j)).snd) :=
  jet_ext fun j => by
    rw [dualLift_zR]
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_inr]
      have := AlgHom.congr_fun h (zR 1 j)
      rw [AlgHom.comp_apply, jetAug_zR] at this
      exact this
    · rfl
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
def IsTan (w : sp (R₀ := R) (DualNumber R) ⟶ G) : Prop := spMap (fstD R) ≫ w = 1
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
include hx in
theorem exists_coord (w : sp (R₀ := R) (DualNumber R) ⟶ G) (hw : IsTan w) :
    ∃! c : Fin n → R, w = spMap (dualLift c) ≫ x 1 := by
  obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := hx.2.2 (DualNumber R) (fstD R) 1 kerD_sq w hw
  refine ⟨fun j => (ψ (zR 1 j)).snd, ?_, ?_⟩
  · show w = spMap (dualLift (fun j => (ψ (zR 1 j)).snd)) ≫ x 1
    rw [← eq_dualLift ψ h1]
    exact h2
  · intro c hc
    have := hu (dualLift c) ⟨fstD_comp_dualLift c, hc⟩
    rw [← this]
    funext j
    rw [dualLift_zR, TrivSqZeroExt.snd_inr]
def tcoord (w : sp (R₀ := R) (DualNumber R) ⟶ G) (hw : IsTan w) : Fin n → R :=
  (exists_coord hx w hw).exists.choose
end ReciprocityTheory.ChartRestriction.G.Chart


