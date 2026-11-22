-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:32.880974+00:00
-- url     : https://prove2.me/theorems/e028718c-4a4b-45b0-a6ef-32907cd86b56
-- title:
--   Restrict Diag Comp Incl Fst
-- statement:
--   Definitions and structural lemmas for Restrict Diag Comp Incl Fst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/RestrictDiagCompInclFst.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp

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
def qD (i : Fin 2) : DualNumber R →ₐ[R] JetR R (Fin 2) 1 :=
  TrivSqZeroExt.lift (Algebra.ofId R _) (LinearMap.toSpanSingleton R _ (zR 1 i))
    (fun a b => by
      simp only [LinearMap.toSpanSingleton_apply]
      rw [smul_mul_smul_comm]
      have : zR (R := R) 1 i * zR 1 i = 0 := by
        show Ideal.Quotient.mk _ (MvPolynomial.X i * MvPolynomial.X i) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, pow_two]
        exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (Ideal.subset_span ⟨i, rfl⟩)
      rw [this, smul_zero])
    (fun r a => by
      simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, map_mul, Algebra.ofId_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      ring)
    (fun r a => by
      simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, map_mul, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply]
      ring)
theorem delta_sq : (RingHom.ker (TrivSqZeroExt.fstHom R R (R × R))) ^ (1 + 1) = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  have ha0 : a.fst = 0 := ha
  have hb0 : b.fst = 0 := hb
  rw [Ideal.mem_bot, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha0 rfl,
    show b = TrivSqZeroExt.inr b.snd from TrivSqZeroExt.ext hb0 rfl, TrivSqZeroExt.inr_mul_inr]
def deltaJ : JetR R (Fin 2) 1 →ₐ[R] TrivSqZeroExt R (R × R) :=
  jetLift R (RingHom.ker (TrivSqZeroExt.fstHom R R (R × R))) delta_sq
    (fun i => TrivSqZeroExt.inr (if i = 0 then ((1 : R), (0 : R)) else (0, 1)))
    (fun i => (RingHom.mem_ker).mpr rfl)
def rD (l : R × R →ₗ[R] R) : JetR R (Fin 2) 1 →ₐ[R] DualNumber R :=
  (TrivSqZeroExt.map l).comp deltaJ
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
theorem isTan_mul {w₁ w₂ : sp (R₀ := R) (DualNumber R) ⟶ G} (h₁ : IsTan w₁) (h₂ : IsTan w₂) : IsTan (w₁ * w₂) := by
  rw [IsTan, MonObj.comp_mul, h₁, h₂, _root_.mul_one]
theorem isTan_one : IsTan (1 : sp (R₀ := R) (DualNumber R) ⟶ G) := comp_one' _
abbrev scaleD (c : R) : DualNumber R →ₐ[R] DualNumber R := TrivSqZeroExt.map (c • LinearMap.id)
theorem isTan_scale (c : R) {w : sp (R₀ := R) (DualNumber R) ⟶ G} (h : IsTan w) : IsTan (spMap (scaleD c) ≫ w) := by
  have : (fstD R).comp (scaleD c) = fstD R := by
    ext
    exact TrivSqZeroExt.fst_map _ _
  rw [IsTan, ← Category.assoc, spMap_comp, this]
  exact h
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
end ReciprocityTheory.ChartRestriction.G.Chart


