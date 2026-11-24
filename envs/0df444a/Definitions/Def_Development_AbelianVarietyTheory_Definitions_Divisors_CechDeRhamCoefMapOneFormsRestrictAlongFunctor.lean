-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:16:51.472177+00:00
-- url     : https://prove2.me/theorems/35bb4eeb-601c-4569-88e6-5249b4a844c7
-- title:
--   Cech De Rham Coef Map One Forms Restrict Along Functor
-- statement:
--   Definitions and structural lemmas for Cech De Rham Coef Map One Forms Restrict Along Functor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamCoefMapOneFormsRestrictAlongFunctor.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_dOne
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_dTwo
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_of_algHom
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_comp_oneFormMap
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_two
import Theorems.Thm_GlobalTheory_CechDR_ofForm_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
namespace GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
section Pull
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')
theorem semiHom_coef (T : C') : SemiHom σ (m.α T) := m.smul T
def q1 (T : C') : Ω[F.obj (m.G.obj T)⁄R] →ₛₗ[σ] Ω[F'.obj T⁄R'] := (semiHom_coef m T).m1
def qOm (j : ℕ) (T : C') : Om R (F.obj (m.G.obj T)) j →ₛₗ[σ] Om R' (F'.obj T) j :=
  (semiHom_coef m T).mOm j
section
variable {T T' : C'}
theorem cechDeRhamCoefMapOneForms_D (b : F.obj (m.G.obj T)) : q1 m T (D R _ b) = D R' _ (m.α T b) := (semiHom_coef m T).m1_D b
theorem cechDeRhamCoefMapOneForms_naturality (φ : T ⟶ T') (ω : Ω[F.obj (m.G.obj T)⁄R]) :
    q1 m T' (p1 F (m.G.map φ) ω) = p1 F' φ (q1 m T ω) :=
  (SemiHom.oneFormMap_comp_oneFormMap _ _ ((semiHom_coef m T).comp (semiHom_mp F' φ)) (m.naturality φ) ω).trans
    (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) ω).symm
theorem qOm_pOm {j : ℕ} (φ : T ⟶ T') (x : Om R (F.obj (m.G.obj T)) j) :
    qOm m j T' (pOm F j (m.G.map φ) x) = pOm F' j φ (qOm m j T x) :=
  (SemiHom.mOm_mOm _ _ ((semiHom_coef m T).comp (semiHom_mp F' φ)) (m.naturality φ) x).trans
    (SemiHom.mOm_mOm _ _ _ (fun _ ↦ rfl) x).symm
theorem qOm_dOne (ω : Ω[F.obj (m.G.obj T)⁄R]) : qOm m 2 T (dOne R _ ω) = dOne R' _ (q1 m T ω) :=
  (semiHom_coef m T).mOm_dOne ω
theorem qOm_dTwo (x : Om R (F.obj (m.G.obj T)) 2) : qOm m 3 T (dTwo R _ x) = dTwo R' _ (qOm m 2 T x) :=
  (semiHom_coef m T).mOm_dTwo x
end
def pullTot1 : Tot1 F →ₛₗ[σ] Tot1 F' where
  toFun c := (fun _ T' φ ↦ m.α T' (c.1 _ _ (m.G.map φ)), fun T ↦ q1 m T (c.2 _))
  map_add' a b := Tot1.ext (by intros; simp) (by intros; simp)
  map_smul' r a := Tot1.ext (by intros; simp [m.smul]) (by intros; simp)
def pullTot2 : Tot2 F →ₛₗ[σ] Tot2 F' where
  toFun c := (fun _ _ T'' φ ψ ↦ m.α T'' (c.1 _ _ _ (m.G.map φ) (m.G.map ψ)),
    fun _ T' φ ↦ q1 m T' (c.2.1 _ _ (m.G.map φ)), fun T ↦ qOm m 2 T (c.2.2 _))
  map_add' a b := Tot2.ext (by intros; simp) (by intros; simp) (by intros; simp)
  map_smul' r a := Tot2.ext (by intros; simp [m.smul]) (by intros; simp) (by intros; simp)
section
variable {T T' T'' : C'} (φ : T ⟶ T') (ψ : T' ⟶ T'')
theorem pullTot1_f (c : Tot1 F) : (pullTot1 m c).1 T T' φ = m.α T' (c.1 _ _ (m.G.map φ)) := rfl
theorem pullTot1_ω (c : Tot1 F) (T : C') : (pullTot1 m c).2 T = q1 m T (c.2 _) := rfl
theorem cechDeRhamPullbackTotalDegreeTwo_function_part (c : Tot2 F) :
    (pullTot2 m c).1 T T' T'' φ ψ = m.α T'' (c.1 _ _ _ (m.G.map φ) (m.G.map ψ)) := rfl
theorem pullTot2_a (c : Tot2 F) : (pullTot2 m c).2.1 T T' φ = q1 m T' (c.2.1 _ _ (m.G.map φ)) := rfl
theorem pullTot2_η (c : Tot2 F) (T : C') : (pullTot2 m c).2.2 T = qOm m 2 T (c.2.2 _) := rfl
end
theorem pullTot1_dTot0 (g : Tot0 F) : pullTot1 m (dTot0 F g) = dTot0 F' fun T ↦ m.α T (g _) :=
  Tot1.ext (fun T T' φ ↦ by simp only [pullTot1_f, dTot0_f, map_sub, m.naturality])
    fun T ↦ by simp only [pullTot1_ω, dTot0_ω, cechDeRhamCoefMapOneForms_D]
theorem pullTot2_dTot1 (c : Tot1 F) : pullTot2 m (dTot1 F c) = dTot1 F' (pullTot1 m c) :=
  Tot2.ext (fun T T' T'' φ ψ ↦ by
      simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, cechDeRhamTotalDifferentialOne_functionPart, pullTot1_f, map_sub, map_add, m.naturality, Functor.map_comp])
    (fun T T' φ ↦ by simp only [pullTot2_a, dTot1_a, pullTot1_f, pullTot1_ω, map_sub, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D])
    fun T ↦ by simp only [pullTot2_η, dTot1_η, pullTot1_ω, qOm_dOne]
def pullZZ1 : cechDeRhamTotalCocyclesOne F →ₛₗ[σ] cechDeRhamTotalCocyclesOne F' :=
  ((pullTot1 m).domRestrict (cechDeRhamTotalCocyclesOne F)).codRestrict (cechDeRhamTotalCocyclesOne F') fun c ↦ by
    change dTot1 F' (pullTot1 m c.1) = 0
    rw [← pullTot2_dTot1, show dTot1 F c.1 = 0 from c.2, map_zero]
def pullZZ2 : cechDeRhamTotalCocyclesTwo F →ₛₗ[σ] cechDeRhamTotalCocyclesTwo F' :=
  ((pullTot2 m).domRestrict (cechDeRhamTotalCocyclesTwo F)).codRestrict (cechDeRhamTotalCocyclesTwo F') fun c ↦ by
    change pullTot2 m c.1 ∈ _
    refine mem_cechDeRhamTotalCocyclesTwo_iff.2 ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
    · simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, Functor.map_comp, ← map_add, ← m.naturality, cechDeRhamTotalCocyclesTwo.comp c]
    · simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, pullTot2_a, Functor.map_comp, cechDeRhamTotalCocyclesTwo.one c, map_add, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D]
    · simp only [pullTot2_η, pullTot2_a]
      rw [cechDeRhamTotalCocyclesTwo.two c (m.G.map φ), map_add, qOm_pOm, qOm_dOne]
    · rw [pullTot2_η, ← qOm_dTwo, cechDeRhamTotalCocyclesTwo.closed c, map_zero]
def pullHyp1 : Hyp1 F →ₛₗ[σ] Hyp1 F' :=
  Submodule.mapQ _ _ (pullZZ1 m) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, Subtype.ext (pullTot1_dTot0 m g).symm⟩)
def pullHyp2 : Hyp2 F →ₛₗ[σ] Hyp2 F' :=
  Submodule.mapQ _ _ (pullZZ2 m) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, Subtype.ext (pullTot2_dTot1 m g).symm⟩)
def pullGlob1 : Glob1 F →ₛₗ[σ] Glob1 F' where
  toFun ω := ⟨fun T ↦ q1 m T (ω.1 _), fun T T' φ ↦ by
    simp only; rw [ω.2 (m.G.map φ), cechDeRhamCoefMapOneForms_naturality]⟩
  map_add' a b := Subtype.ext (funext fun T ↦ by simp)
  map_smul' r a := Subtype.ext (funext fun T ↦ by simp)
def pullClosed1 : Closed1 F →ₛₗ[σ] Closed1 F' :=
  ((pullGlob1 m).domRestrict (Closed1 F)).codRestrict (Closed1 F') fun ω T ↦ by
    change dOne R' _ (q1 m T (ω.1.1 _)) = 0
    rw [← qOm_dOne, ω.2, map_zero]
section Nat
variable {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
  (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b)
include h
end Nat
end Pull
section Initial
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
def exact1 : Submodule R (LinearMap.ker (dOne R B)) :=
  (LinearMap.range (D R B).toLinearMap).comap (LinearMap.ker (dOne R B)).subtype
abbrev AlgebraFirstDeRham : Type := LinearMap.ker (dOne R B) ⧸ exact1 R B
variable {R B} {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)
def coneForm : LinearMap.ker (dOne R B) →ₗ[R] Closed1 F where
  toFun ω := ⟨⟨fun T ↦ (SemiHom.of_algHom (e T)).m1 ω.1, fun T T' φ ↦
    (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (he φ) _).symm⟩, fun T ↦ by
      change dOne R _ ((SemiHom.of_algHom (e T)).m1 ω.1) = 0
      rw [← SemiHom.mOm_dOne, show dOne R B ω.1 = 0 from ω.2, map_zero]⟩
  map_add' a b := Subtype.ext (Subtype.ext (funext fun T ↦ map_add _ _ _))
  map_smul' r a := Subtype.ext (Subtype.ext (funext fun T ↦ (SemiHom.of_algHom (e T)).m1.map_smulₛₗ r a.1))
theorem coneForm_apply (ω : LinearMap.ker (dOne R B)) (T : C) :
    (coneForm e he ω).1.1 T = (SemiHom.of_algHom (e T)).m1 ω.1 := rfl
def coneMap : AlgebraFirstDeRham R B →ₗ[R] Hyp1 F :=
  Submodule.liftQ _ (ofForm F ∘ₗ coneForm e he) (by
    rintro ω ⟨b, hb⟩
    refine ofForm_eq_zero.2 ⟨fun T ↦ e T b, fun T T' φ ↦ (he φ b).symm, fun T ↦ ?_⟩
    rw [coneForm_apply, show ω.1 = D R B b from hb.symm, SemiHom.m1_D]; rfl)
end Initial
end GlobalTheory.CechDR


