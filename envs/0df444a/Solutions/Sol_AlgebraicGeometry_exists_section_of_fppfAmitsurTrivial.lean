-- Prove2me | solution 1 for AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b571c299-0476-5002-aaf2-86dbc5245e62

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
import Definitions.Def_Algebra_DescentCofaces
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology
import Theorems.Thm_AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf
import Theorems.Thm_AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2
import Theorems.Thm_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_section_of_fppfAmitsurTrivial

set_option autoImplicit false

universe u

p2m_open "CategoryTheory Opposite AlgebraicGeometry Algebra.DescentCofaces CategoryTheory.Limits"

namespace FppfKummerSES
namespace RCovMain
p2m_open "FppfKummerSES"

variable {F E G : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1}}

private theorem _root_.FppfKummerSES.RCovMain.imageSieve_mem (g : E ⟶ G) [Epi g] (T : Scheme.{u}) (z : ToType (G.obj.obj (op T))) :
    Presheaf.imageSieve g.hom z ∈ Scheme.fppfTopology T := by
  haveI : Sheaf.IsLocallySurjective g := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u+1} g).mpr inferInstance
  exact Presheaf.imageSieve_mem _ g.hom z

p2m_export "FppfKummerSES.RCovMain" "imageSieve_mem"

theorem app_injective (f : F ⟶ E) [Mono f] (T : Scheme.{u}) : Function.Injective (f.hom.app (op T)) := by
  haveI : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  haveI : Mono (f.hom.app (op T)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

set_option maxHeartbeats 3200000 in
theorem exists_app_eq_of_app_eq_zero (f : F ⟶ E) (g : E ⟶ G) [Mono f] (w : f ≫ g = 0)
    (hfg : (ShortComplex.mk f g w).Exact) (T : Scheme.{u}) (x : ToType (E.obj.obj (op T)))
    (hx : g.hom.app (op T) x = 0) : ∃ c, f.hom.app (op T) c = x := by
  let Φ : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op T)
  have hk : IsLimit ((KernelFork.ofι f w).map Φ) := KernelFork.mapIsLimit _ hfg.fIsKernel Φ
  let k : AddCommGrpCat.of (g.hom.app (op T)).hom.ker ⟶ Φ.obj E := AddCommGrpCat.ofHom (AddSubgroup.subtype _)
  have hk0 : k ≫ Φ.map g = 0 := by
    ext ⟨y, hy⟩
    exact hy
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hk k hk0
  refine ⟨l ⟨x, hx⟩, ?_⟩
  have := ConcreteCategory.congr_hom hl ⟨x, hx⟩
  simp at this
  exact this

theorem map_map_Spec (X : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1}) {P Q S : CommRingCat.{u}}
    (a : P ⟶ Q) (b : Q ⟶ S) (x : ToType (X.obj.obj (op (Spec P)))) :
    X.obj.map (Spec.map b).op (X.obj.map (Spec.map a).op x) = X.obj.map (Spec.map (a ≫ b)).op x := by
  rw [Spec.map_comp, op_comp, Functor.map_comp]; rfl

theorem app_map (f : F ⟶ E) {P Q : CommRingCat.{u}} (a : P ⟶ Q) (x : ToType (F.obj.obj (op (Spec P)))) :
    f.hom.app _ (F.obj.map (Spec.map a).op x) = E.obj.map (Spec.map a).op (f.hom.app _ x) :=
  ConcreteCategory.congr_hom (f.hom.naturality (Spec.map a).op) x

set_option maxHeartbeats 3200000 in
theorem cech_identity (f : F ⟶ E) [Mono f] (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (e : ToType (E.obj.obj (op (Spec (.of A))))) (c : ToType (F.obj.obj (op (Spec (R₂ R A)))))
    (hc : f.hom.app _ c = E.obj.map (Spec.map (i₁ R A)).op e - E.obj.map (Spec.map (i₂ R A)).op e) :
    F.obj.map (Spec.map (c₁₂ R A)).op c + F.obj.map (Spec.map (c₂₃ R A)).op c =
      F.obj.map (Spec.map (c₁₃ R A)).op c := by
  apply app_injective f (Spec (R₃ R A))
  rw [map_add, app_map, app_map, app_map, hc, map_sub, map_sub, map_sub]
  simp only [map_map_Spec, i₁_c₁₂, i₂_c₁₂, i₂_c₁₃]
  abel

set_option maxHeartbeats 6400000 in
theorem main (f : F ⟶ E) (g : E ⟶ G) [Mono f] [Epi g] (w : f ≫ g = 0) (hfg : (ShortComplex.mk f g w).Exact)
    (R : Type u) [CommRing R] (z : ToType (G.obj.obj (op (Spec (.of R))))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Module.FaithfullyFlat R A) (_ : Algebra.FinitePresentation R A)
      (e : ToType (E.obj.obj (op (Spec (.of A)))))
      (c : ToType (F.obj.obj (op (Spec (R₂ R A))))),
      g.hom.app (op (Spec (.of A))) e = G.obj.map (Spec.map (CommRingCat.ofHom (algebraMap R A))).op z ∧
      f.hom.app (op (Spec (R₂ R A))) c = E.obj.map (Spec.map (i₁ R A)).op e - E.obj.map (Spec.map (i₂ R A)).op e ∧
      F.obj.map (Spec.map (c₁₂ R A)).op c + F.obj.map (Spec.map (c₂₃ R A)).op c = F.obj.map (Spec.map (c₁₃ R A)).op c := by
  classical

  obtain ⟨ι, _, Ac, φ, hcov, hmem⟩ := Scheme.exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology
    (Presheaf.imageSieve g.hom z) (imageSieve_mem g _ z)
  choose t ht using hmem

  let A : Type u := ∀ i, Ac i
  letI : Algebra R A := (RingHom.pi fun i => (φ i).hom).toAlgebra
  have hsingle : Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap R A))) ∈ Scheme.fppfPrecoverage (Spec (.of R)) :=
    Scheme.singleton_sigma_mem_fppfPrecoverage Ac φ hcov
  rw [Scheme.fppfPrecoverage, Scheme.singleton_mem_precoverage_iff] at hsingle
  obtain ⟨hsurj, hflat, hlfp⟩ := hsingle
  haveI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp
    ((HasRingHomProperty.Spec_iff (P := @Flat) (φ := CommRingCat.ofHom (algebraMap R A))).mp hflat)
  haveI : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_comap_surjective hsurj
  haveI : Algebra.FinitePresentation R A := RingHom.finitePresentation_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := CommRingCat.ofHom (algebraMap R A))).mp hlfp)

  obtain ⟨e, he⟩ := (Scheme.bijective_pi_map_of_fppf_sheaf E Ac).2 t
  have hev : ∀ i, CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom (Pi.evalRingHom (fun i => (Ac i : Type u)) i) = φ i :=
    fun i => by ext r; rfl
  have hge : g.hom.app (op (Spec (.of A))) e = G.obj.map (Spec.map (CommRingCat.ofHom (algebraMap R A))).op z := by
    apply (Scheme.bijective_pi_map_of_fppf_sheaf G Ac).1
    funext i
    have h1 : E.obj.map (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => (Ac i : Type u)) i))).op e = t i :=
      congrFun he i
    calc G.obj.map _ (g.hom.app _ e) = g.hom.app _ (E.obj.map _ e) := (app_map g _ e).symm
      _ = g.hom.app (op (Spec (Ac i))) (t i) := by rw [h1]
      _ = G.obj.map (Spec.map (φ i)).op z := ht i
      _ = _ := by
        change _ = G.obj.map _ (G.obj.map _ z)
        rw [map_map_Spec, hev]

  have hx : g.hom.app _ (E.obj.map (Spec.map (i₁ R A)).op e - E.obj.map (Spec.map (i₂ R A)).op e) = 0 := by
    rw [map_sub, app_map g, app_map g, hge, map_map_Spec, map_map_Spec, algebraMap_i₁_eq_i₂, sub_self]
  obtain ⟨c, hc⟩ := exists_app_eq_of_app_eq_zero f g w hfg _ _ hx
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, e, c, hge, hc, cech_identity f R A e c hc⟩

end FppfKummerSES.RCovMain

set_option maxHeartbeats 6400000 in
open FppfKummerSES.RCovMain in
theorem solution
    (F E : Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}) (f : F ⟶ E)
    (g : E ⟶ (constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)))
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (H : ∀ (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A] [Algebra.FinitePresentation ℤ A],
      Scheme.FppfAmitsurTrivial F A) :
    ∃ s : (constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)) ⟶ E,
      s ≫ g = 𝟙 _ := by

  let Zc : Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1} :=
    (constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ))
  let one : ToType (Zc.obj.obj (op (Spec (.of ℤ)))) :=
    (constantSheafAdj Scheme.fppfTopology.{0} AddCommGrpCat.{1} AlgebraicGeometry.specZIsTerminal).unit.app
      (.of (ULift.{1} ℤ)) (ULift.up 1)
  haveI := hS.mono_f
  haveI := hS.epi_g

  obtain ⟨A, _, instAlg, _, _, eA, c, hge, hc, hcocy⟩ := main f g w hS.exact ℤ one

  have hinst : instAlg = Ring.toIntAlgebra A := Subsingleton.elim _ _
  subst hinst

  obtain ⟨b, hb⟩ := H A c hcocy

  let e' : ToType (E.obj.obj (op (Spec (.of A)))) := eA - f.hom.app _ b
  have he' : E.obj.map (Spec.map (i₁ ℤ A)).op e' = E.obj.map (Spec.map (i₂ ℤ A)).op e' := by
    rw [← sub_eq_zero]
    change E.obj.map _ (eA - f.hom.app _ b) - E.obj.map _ (eA - f.hom.app _ b) = 0
    rw [map_sub, map_sub, ← app_map f, ← app_map f, sub_sub_sub_comm, ← hc, ← map_sub, ← hb, sub_self]

  obtain ⟨e₀, he₀, -⟩ := Scheme.existsUnique_section_of_map_i1_eq_map_i2 E ℤ A e' he'

  have hgfb : g.hom.app (op (Spec (.of A))) (f.hom.app _ b) = 0 := by
    have := congrArg (fun h => h.hom.app (op (Spec (.of A))) b) w
    simpa using this
  have hone : Zc.obj.map (Spec.map (i₁ ℤ A)).op (Zc.obj.map (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))).op one) =
      Zc.obj.map (Spec.map (i₂ ℤ A)).op (Zc.obj.map (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))).op one) := by
    rw [map_map_Spec, map_map_Spec, algebraMap_i₁_eq_i₂]
  have hge₀ : g.hom.app (op (Spec (.of ℤ))) e₀ = one := by
    refine (Scheme.existsUnique_section_of_map_i1_eq_map_i2 Zc ℤ A _ hone).unique ?_ rfl
    rw [← app_map g, he₀]
    change g.hom.app _ (eA - f.hom.app _ b) = _
    rw [map_sub, hgfb, sub_zero, hge]

  exact AlgebraicGeometry.fppf_exists_section_of_map_eq_unit g e₀ hge₀

end S_AlgebraicGeometry_exists_section_of_fppfAmitsurTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_exists_section_of_fppfAmitsurTrivial (solution)
