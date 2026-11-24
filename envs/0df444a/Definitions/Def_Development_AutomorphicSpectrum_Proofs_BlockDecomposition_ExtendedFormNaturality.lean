-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtendedFormNaturality
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtendedFormNaturality
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:01.465167+00:00
-- url     : https://prove2.me/theorems/5c1b046b-0d8b-4121-a33a-b3a8c7097779
-- title:
--   Extended Form Naturality
-- statement:
--   Definitions and structural lemmas for Extended Form Naturality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExtendedFormNaturality.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.OneFormCoh
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
def extForm (hp : Par F) (l : Glob1 F →ₗ[R] R) (T : C) : Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T :=
  (hp T).lift ((Algebra.linearMap R (F.obj T)) ∘ₗ l)
theorem extForm_ev (hp : Par F) (l : Glob1 F →ₗ[R] R) (T : C) (v : Glob1 F) :
    extForm F hp l T (v.1 T) = algebraMap R (F.obj T) (l v) :=
  (hp T).lift_eq _ v
theorem extended_form_naturality (hp : Par F) (l : Glob1 F →ₗ[R] R) {T T' : C} (φ : T ⟶ T') (α : Ω[F.obj T⁄R]) :
    extForm F hp l T' (p1 F φ α) = mp F φ (extForm F hp l T α) := by
  refine (hp T).inductionOn α (fun α => GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T' (GlobalTheory.CechDR.p1 F φ α) =
    GlobalTheory.CatCoh.mp F φ (GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T α)) ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro v
    change GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T' (GlobalTheory.CechDR.p1 F φ (v.1 T)) =
      GlobalTheory.CatCoh.mp F φ (GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T (v.1 T))
    have hv : GlobalTheory.CechDR.p1 F φ (v.1 T) = v.1 T' := by
      first
        | exact v.2 φ
        | exact v.2 T T' φ
        | exact (v.2 φ).symm
        | exact (v.2 T T' φ).symm
    rw [hv, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, AlgHom.commutes]
  · intro s n hn
    rw [GlobalTheory.CechDR.oneFormsMapOfFunctorMorphism_smul, map_smul, map_smul, hn, smul_eq_mul, smul_eq_mul, map_mul]
  · intro n₁ n₂ h₁ h₂
    rw [map_add, map_add, h₁, h₂, map_add, map_add]
def muMap : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F :=
  TensorProduct.lift (LinearMap.mk₂ R (fun (f : Z1 F) (v : Glob1 F) T T' φ ↦ f.1 T T' φ • v.1 T')
    (fun f f' v ↦ by funext T T' φ; simp [add_smul])
    (fun r f v ↦ by funext T T' φ; simp)
    (fun f v v' ↦ by funext T T' φ; simp)
    (fun r f v ↦ by funext T T' φ; simp [smul_comm r]))
def contr (l : Glob1 F →ₗ[R] R) : Z1 F ⊗[R] Glob1 F →ₗ[R] Z1 F :=
  (TensorProduct.rid R (Z1 F)).toLinearMap ∘ₗ LinearMap.lTensor (Z1 F) l
def pushZ (hp : Par F) (l : Glob1 F →ₗ[R] R) (a : A1 F)
    (ha : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) : Z1 F :=
  ⟨fun T T' φ ↦ extForm F hp l T' (a T T' φ), fun T T' T'' φ ψ ↦ by
    change extForm F hp l T'' (a T T'' (φ ≫ ψ)) =
      mp F ψ (extForm F hp l T' (a T T' φ)) + extForm F hp l T'' (a T' T'' ψ)
    rw [ha, map_add, extended_form_naturality]⟩
end GlobalTheory.CompanionTheory.OneFormCoh


