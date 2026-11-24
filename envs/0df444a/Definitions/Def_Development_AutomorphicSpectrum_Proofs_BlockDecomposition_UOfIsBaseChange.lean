-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:13:14.14686+00:00
-- url     : https://prove2.me/theorems/719c19fc-ef9e-4c5c-bb88-d707b697b1df
-- title:
--   UOf Is Base Change
-- statement:
--   Definitions and structural lemmas for UOf Is Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
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
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
abbrev Spo {T : Type} [CommRing T] (f : R →+* T) : Over (Sp R) := Over.mk (spMap f)
def spo {T T' : Type} [CommRing T] [CommRing T'] {f : R →+* T} {f' : R →+* T'} (a : T →+* T')
    (h : a.comp f = f') : Spo f' ⟶ Spo f :=
  Over.homMk (spMap a) (by subst h; exact (spMap_comp f a).symm)
theorem spo_comp {T T' T'' : Type} [CommRing T] [CommRing T'] [CommRing T''] {f : R →+* T}
    {f' : R →+* T'} {f'' : R →+* T''} (a : T →+* T') (b : T' →+* T'') (h : a.comp f = f')
    (h' : b.comp f' = f'') (h'' : (b.comp a).comp f = f'') :
    spo b h' ≫ spo a h = spo (b.comp a) h'' :=
  Over.OverMorphism.ext (spMap_comp a b).symm
theorem spo_id {T : Type} [CommRing T] {f : R →+* T} (h : (RingHom.id T).comp f = f) :
    spo (RingHom.id T) h = 𝟙 _ :=
  Over.OverMorphism.ext (spMap_id T)
section Pts
variable (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M]
abbrev sz : R →+* TrivSqZeroExt B M := (TrivSqZeroExt.inlHom B M).comp (algebraMap R B)
abbrev fs : TrivSqZeroExt B M →+* B := (TrivSqZeroExt.fstHom B B M).toRingHom
theorem fs_sz : (fs B M).comp (sz (R := R) B M) = algebraMap R B := RingHom.ext fun _ ↦ rfl
theorem fs_inl : (fs B M).comp (TrivSqZeroExt.inlHom B M) = RingHom.id B := RingHom.ext fun _ ↦ rfl
end Pts
theorem one_left (A P : Over (Sp R)) [GrpObj A] : (1 : P ⟶ A).left = P.hom ≫ η[A].left := by
  rw [Hom.one_def]
  simp
section Tm
variable {B B' M M' : Type} [CommRing B] [CommRing B'] [AddCommGroup M] [AddCommGroup M'] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M']
def tmap (α : B →+* B') (f : M →+ M') (hf : ∀ b m, f (b • m) = α b • f m) :
    TrivSqZeroExt B M →+* TrivSqZeroExt B' M' where
  toFun c := TrivSqZeroExt.inl (α c.fst) + TrivSqZeroExt.inr (f c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [hf]
variable (α : B →+* B') (f : M →+ M') (hf : ∀ b m, f (b • m) = α b • f m)
@[simp] theorem fst_tmap (c : TrivSqZeroExt B M) : (tmap α f hf c).fst = α c.fst := by simp [tmap]
@[simp] theorem snd_tmap (c : TrivSqZeroExt B M) : (tmap α f hf c).snd = f c.snd := by simp [tmap]
end Tm
section Group
variable {A : Over (Sp R)} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
def xo (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B)) : Spo (algebraMap R B) ⟶ A :=
  Over.homMk x hx
variable {M : Type} [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))
def Zp (σ : B →+* TrivSqZeroExt B M) (hσ : σ.comp (algebraMap R B) = sz B M) : Spo (sz (R := R) B M) ⟶ A :=
  spo σ hσ ≫ xo x hx * (spo (TrivSqZeroExt.inlHom B M) rfl ≫ xo x hx)⁻¹
theorem spo_xo (τ : B →+* B) (hτ : τ = RingHom.id B) (h : τ.comp (algebraMap R B) = algebraMap R B) :
    spo τ h ≫ xo x hx = xo x hx := by
  subst hτ
  rw [spo_id, Category.id_comp]
theorem Zp_fst (σ : B →+* TrivSqZeroExt B M) (hσ : σ.comp (algebraMap R B) = sz B M)
    (h1 : (fs B M).comp σ = RingHom.id B) : spo (fs B M) (fs_sz B M) ≫ Zp x hx σ hσ = 1 := by
  rw [Zp, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spo_comp _ _ _ _ (by rw [RingHom.comp_assoc, hσ, fs_sz]),
    spo_comp _ _ _ _ (by rw [RingHom.comp_assoc]; exact fs_sz B M), spo_xo x hx _ h1, spo_xo x hx _ (fs_inl B M), mul_inv_cancel]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M']
end Group
section Cot
variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
  [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ A.left} (hy : IsCot A.hom η[A].left W y₀)
def yo : Spo (TrivSqZeroExt.inlHom R W) ⟶ A := Over.homMk y₀ hy.1
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
theorem tsz_comp (u : W →ₗ[R] M) : (tsz (B := B) u).comp (TrivSqZeroExt.inlHom R W) = sz B M :=
  RingHom.ext fun r ↦ by ext <;> simp [tsz]
def tzo (u : W →ₗ[R] M) : Spo (sz (R := R) B M) ⟶ A := spo (tsz u) (tsz_comp u) ≫ yo hy
theorem cot_unique (Zt : Spo (sz (R := R) B M) ⟶ A) (hZ : spo (fs B M) (fs_sz B M) ≫ Zt = 1) :
    ∃! u : W →ₗ[R] M, Zt = tzo hy u := by
  have h2 : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ Zt.left =
      spMap (algebraMap R B) ≫ η[A].left :=
    (congrArg (fun t ↦ t.left) hZ).trans (one_left _ _)
  obtain ⟨u, hu, hu'⟩ := hy.2.2 B M Zt.left (Over.w Zt) h2
  exact ⟨u, Over.OverMorphism.ext hu, fun v hv ↦ hu' v (congrArg (fun t ↦ t.left) hv)⟩
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M']
theorem diag_w : (diagSec R B : B →+* TrivSqZeroExt B Ω[B⁄R]).comp (algebraMap R B) = sz B Ω[B⁄R] :=
  RingHom.ext fun r ↦ by
    ext
    · exact fst_derSec _ _
    · exact (snd_derSec _ _).trans (by simp)
theorem diag_fst : (fs B Ω[B⁄R]).comp (diagSec R B : B →+* TrivSqZeroExt B Ω[B⁄R]) = RingHom.id B :=
  RingHom.ext fun b ↦ fst_derSec _ b
variable (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))
theorem Zp_diag_fst : spo (fs B Ω[B⁄R]) (fs_sz B Ω[B⁄R]) ≫
    Zp x hx (M := Ω[B⁄R]) (diagSec R B : B →+* _) diag_w = 1 := by
  have h := Zp_fst (R := R) (A := A) (B := B) (M := Ω[B⁄R]) x hx (diagSec R B : B →+* _) diag_w diag_fst
  exact h
theorem exists_uOf : ∃ u : W →ₗ[R] Ω[B⁄R],
    Zp x hx (diagSec R B : B →+* _) diag_w = tzo (B := B) (M := Ω[B⁄R]) hy u := by
  have h := cot_unique (B := B) (M := Ω[B⁄R]) hy _ (Zp_diag_fst x hx)
  exact h.exists
def uOf : W →ₗ[R] Ω[B⁄R] :=
  (exists_uOf hy x hx).choose
abbrev tm (f : Ω[B⁄R] →ₗ[B] M) : TrivSqZeroExt B Ω[B⁄R] →+* TrivSqZeroExt B M :=
  tmap (RingHom.id B) (f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) fun b m ↦ f.map_smul b m
abbrev sg (f : Ω[B⁄R] →ₗ[B] M) : B →+* TrivSqZeroExt B M := (tm f).comp (diagSec R B : B →+* _)
theorem tm_w (f : Ω[B⁄R] →ₗ[B] M) : (tm f).comp (sz (R := R) B Ω[B⁄R]) = sz B M :=
  RingHom.ext fun r ↦ by
    ext
    · exact fst_tmap (RingHom.id B) ((f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) : Ω[B⁄R] →+ M)
        (fun b m ↦ f.map_smul b m) _
    · exact (snd_tmap (RingHom.id B) ((f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) : Ω[B⁄R] →+ M)
        (fun b m ↦ f.map_smul b m) _).trans (map_zero _)
theorem sg_w (f : Ω[B⁄R] →ₗ[B] M) : (sg f).comp (algebraMap R B) = sz B M := by
  rw [RingHom.comp_assoc, diag_w, tm_w]
def derOf (σ : B →+* TrivSqZeroExt B M) (h1 : ∀ b, (σ b).fst = b)
    (h2 : ∀ r, σ (algebraMap R B r) = TrivSqZeroExt.inl (algebraMap R B r)) : Derivation R B M :=
  Derivation.mk'
    { toFun b := (σ b).snd
      map_add' a b := by simp
      map_smul' r b := by
        rw [Algebra.smul_def, map_mul, h2]
        simp [h1] }
    fun a b ↦ by
      simp [h1, add_comm]
variable [IsOpenImmersion x]
end Cot
section Family
variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
end Family
end GlobalTheory.CompanionTheory.AbForms


