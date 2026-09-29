-- Prove2me | solution 1 for AlgebraicGeometry.exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/69d44568-c502-5664-a511-dc7b6b3cd4b9

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Theorems.Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_apply_eq_of_bialgEquiv_monoidAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MuPunctHom

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite WithConv

variable (q : ℕ) [NeZero q]

abbrev K₀ : Type := MonoidAlgebra ℤ (Multiplicative (ZMod q))

abbrev xGen : K₀ q := MonoidAlgebra.single (Multiplicative.ofAdd 1) 1

section Precomp

variable {q}
variable {K : Type} [CommRing K] [HopfAlgebra ℤ K] (ι : K₀ q →ₐc[ℤ] K)
variable (R : Type) [CommRing R]

attribute [local instance 10000] Algebra.toModule

def precomp : Additive (WithConv (K →ₐ[ℤ] R)) →+ Additive (WithConv (K₀ q →ₐ[ℤ] R)) where
  toFun φ := Additive.ofMul (toConv ((Additive.toMul φ).ofConv.comp (ι : K₀ q →ₐ[ℤ] K)))
  map_zero' := by
    change Additive.ofMul (toConv ((1 : WithConv (K →ₐ[ℤ] R)).ofConv.comp (ι : K₀ q →ₐ[ℤ] K))) =
      Additive.ofMul (1 : WithConv (K₀ q →ₐ[ℤ] R))
    congr 1
    apply WithConv.ext
    refine AlgHom.ext fun c => ?_
    change (1 : WithConv (K →ₐ[ℤ] R)) (ι c) = (1 : WithConv (K₀ q →ₐ[ℤ] R)) c
    rw [AlgHom.convOne_apply, AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]
  map_add' φ ψ := by
    change Additive.ofMul (toConv ((Additive.toMul φ * Additive.toMul ψ).ofConv.comp (ι : K₀ q →ₐ[ℤ] K))) =
      Additive.ofMul (toConv ((Additive.toMul φ).ofConv.comp (ι : K₀ q →ₐ[ℤ] K)) *
        toConv ((Additive.toMul ψ).ofConv.comp (ι : K₀ q →ₐ[ℤ] K)))
    rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv]

theorem precomp_apply (φ : Additive (WithConv (K →ₐ[ℤ] R))) :
    (Additive.toMul (precomp ι R φ)).ofConv = (Additive.toMul φ).ofConv.comp (ι : K₀ q →ₐ[ℤ] K) :=
  rfl

theorem precomp_injective
    (hinj : ∀ f g : K →ₐ[ℤ] R, f.comp (ι : K₀ q →ₐ[ℤ] K) = g.comp (ι : K₀ q →ₐ[ℤ] K) → f = g) :
    Function.Injective (precomp ι R) := by
  intro φ ψ h
  have h' := congrArg (fun w => (Additive.toMul w).ofConv) h
  simp only [precomp_apply] at h'
  have := hinj _ _ h'
  exact congrArg Additive.ofMul (WithConv.ext this)

theorem mem_range_precomp_iff (g : Additive (WithConv (K₀ q →ₐ[ℤ] R))) :
    g ∈ Set.range (precomp ι R) ↔
      ∃ f : K →ₐ[ℤ] R, f.comp (ι : K₀ q →ₐ[ℤ] K) = (Additive.toMul g).ofConv := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨(Additive.toMul φ).ofConv, rfl⟩
  · rintro ⟨f, hf⟩
    refine ⟨Additive.ofMul (toConv f), ?_⟩
    exact congrArg Additive.ofMul (WithConv.ext hf)

end Precomp

section NearCondition

variable {q}
variable (p : ℕ) {R : Type} [CommRing R]

theorem algebraMap_counit_single (m : Multiplicative (ZMod q)) :
    algebraMap ℤ R (Bialgebra.counitAlgHom ℤ (K₀ q) (MonoidAlgebra.single m 1)) = 1 := by
  rw [Bialgebra.counitAlgHom_apply, MonoidAlgebra.counit_single]
  exact map_one (algebraMap ℤ R)

theorem single_eq_xGen_pow [NeZero q] (m : Multiplicative (ZMod q)) :
    (MonoidAlgebra.single m 1 : K₀ q) = xGen q ^ (Multiplicative.toAdd m).val := by
  rw [xGen, MonoidAlgebra.single_pow, one_pow]
  congr 1
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rfl

theorem forall_mul_sub_counit_eq_zero_iff [NeZero q] (a : R) (g : K₀ q →ₐ[ℤ] R) :
    (∀ h : K₀ q, a * (g h - algebraMap ℤ R (Bialgebra.counitAlgHom ℤ (K₀ q) h)) = 0) ↔
      a * (g (xGen q) - 1) = 0 := by
  constructor
  · intro H
    have := H (xGen q)
    rwa [algebraMap_counit_single] at this
  · intro H h
    induction h using MonoidAlgebra.induction_on with
    | of m =>
      rw [MonoidAlgebra.of_apply, algebraMap_counit_single, single_eq_xGen_pow, map_pow]
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (g (xGen q)) 1 (Multiplicative.toAdd m).val
      rw [one_pow] at hc
      rw [hc, ← mul_assoc, H, zero_mul]
    | add f₁ f₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, add_sub_add_comm, mul_add, h₁, h₂, add_zero]
    | smul r f hf =>
      rw [map_smul, map_smul, smul_eq_mul, map_mul, Algebra.smul_def, ← mul_sub, mul_left_comm, hf,
        mul_zero]

end NearCondition

section SheafSide

p2m_open "CategoryTheory.Limits FppfKummerSES"

variable {q}
variable (p : ℕ)
variable {K : Type} [CommRing K] [HopfAlgebra ℤ K] (ι : K₀ q →ₐc[ℤ] K)
variable (L : Sheaf (smallFppfTopology specInt) Ab.{1})
  (e : ∀ U : specInt.Fppf,
    L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
  (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
    (Additive.toMul (e U (L.1.map f.op s))) k
      = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
  (C : Sheaf (smallFppfTopology specInt) Ab.{1})
  (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
    (muPAbelianSheafLifted.{0} q).obj)
  (e₀ : ∀ T : Scheme.{0},
    ((muPAbelianSheafLifted.{0} q).obj.obj (Opposite.op T)) ≃+
      Additive (WithConv (K₀ q →ₐ[ℤ] Γ(T, ⊤))))
  (he₀ : ∀ {T T' : Scheme.{0}} (g : T ⟶ T')
    (s : (muPAbelianSheafLifted.{0} q).obj.obj (Opposite.op T')) (k : K₀ q),
    (Additive.toMul (e₀ T ((muPAbelianSheafLifted.{0} q).obj.map g.op s))) k
      = (Scheme.Γ.map g.op) ((Additive.toMul (e₀ T' s)) k))

private def _root_.MuPunctHom.comp (U : specInt.Fppf) : (L.obj.obj (op U) : Type 1) →+ (C.obj.obj (op U) : Type 1) :=
  (iC.inv.app (op U)).hom.comp <|
    (e₀ U.left).symm.toAddMonoidHom.comp <| (precomp ι Γ(U.left, ⊤)).comp (e U).toAddMonoidHom

p2m_export "MuPunctHom" "comp"
theorem comp_apply (U : specInt.Fppf) (l : L.obj.obj (op U)) :
    comp ι L e C iC e₀ U l = iC.inv.app (op U) ((e₀ U.left).symm (precomp ι Γ(U.left, ⊤) (e U l))) :=
  rfl

theorem iC_hom_comp_apply (U : specInt.Fppf) (l : L.obj.obj (op U)) :
    iC.hom.app (op U) (comp ι L e C iC e₀ U l) = (e₀ U.left).symm (precomp ι Γ(U.left, ⊤) (e U l)) := by
  rw [comp_apply]
  exact ConcreteCategory.congr_hom (iC.inv_hom_id_app (op U)) _

theorem e₀_iC_hom_comp_apply (U : specInt.Fppf) (l : L.obj.obj (op U)) :
    e₀ U.left (iC.hom.app (op U) (comp ι L e C iC e₀ U l)) = precomp ι Γ(U.left, ⊤) (e U l) := by
  rw [iC_hom_comp_apply, AddEquiv.apply_symm_apply]

include hnat in

theorem e_map (U V : specInt.Fppf) (g : V ⟶ U) (s : L.obj.obj (op U)) :
    e V (L.obj.map g.op s) =
      Additive.ofMul (toConv (((Scheme.Γ.map g.left.op).hom.toIntAlgHom).comp
        (Additive.toMul (e U s)).ofConv)) := by
  apply (Additive.toMul).injective
  apply WithConv.ext
  refine AlgHom.ext fun k => ?_
  exact hnat g s k

include he₀ in

theorem e₀_symm_map {T T' : Scheme.{0}} (g : T ⟶ T') (φ : Additive (WithConv (K₀ q →ₐ[ℤ] Γ(T', ⊤)))) :
    (e₀ T).symm (Additive.ofMul (toConv (((Scheme.Γ.map g.op).hom.toIntAlgHom).comp
        (Additive.toMul φ).ofConv))) =
      (muPAbelianSheafLifted.{0} q).obj.map g.op ((e₀ T').symm φ) := by
  apply (e₀ T).injective
  rw [AddEquiv.apply_symm_apply]
  apply (Additive.toMul).injective
  apply WithConv.ext
  refine AlgHom.ext fun k => ?_
  rw [he₀ g ((e₀ T').symm φ) k, AddEquiv.apply_symm_apply]
  rfl

theorem precomp_ofMul_comp {R S : Type} [CommRing R] [CommRing S] (h : R →ₐ[ℤ] S)
    (φ : Additive (WithConv (K →ₐ[ℤ] R))) :
    precomp ι S (Additive.ofMul (toConv (h.comp (Additive.toMul φ).ofConv))) =
      Additive.ofMul (toConv (h.comp (Additive.toMul (precomp ι R φ)).ofConv)) :=
  rfl

include hnat he₀ in
theorem comp_naturality (U V : specInt.Fppf) (g : V ⟶ U) (s : L.obj.obj (op U)) :
    comp ι L e C iC e₀ V (L.obj.map g.op s) = C.obj.map g.op (comp ι L e C iC e₀ U s) := by
  rw [comp_apply, comp_apply, e_map L e hnat U V g s]
  change iC.inv.app (op V) ((e₀ V.left).symm (Additive.ofMul (toConv
      (((Scheme.Γ.map g.left.op).hom.toIntAlgHom).comp
        (Additive.toMul (precomp ι Γ(U.left, ⊤) (e U s))).ofConv)))) = _
  rw [e₀_symm_map e₀ he₀ g.left]
  exact ConcreteCategory.congr_hom (iC.inv.naturality g.op) _

def homLC (hn : ∀ (U V : specInt.Fppf) (g : V ⟶ U) (s : L.obj.obj (op U)),
    comp ι L e C iC e₀ V (L.obj.map g.op s) = C.obj.map g.op (comp ι L e C iC e₀ U s)) : L ⟶ C :=
  ObjectProperty.homMk
    { app := fun U => AddCommGrpCat.ofHom (comp ι L e C iC e₀ U.unop)
      naturality := by
        intro U V g
        ext s
        exact hn U.unop V.unop g.unop s }

theorem homLC_app (hn) (U : specInt.Fppf) (l : L.obj.obj (op U)) :
    (homLC ι L e C iC e₀ hn).hom.app (op U) l = comp ι L e C iC e₀ U l :=
  rfl

theorem comp_injective (U : specInt.Fppf)
    (hinj : ∀ f g : K →ₐ[ℤ] Γ(U.left, ⊤),
      f.comp (ι : K₀ q →ₐ[ℤ] K) = g.comp (ι : K₀ q →ₐ[ℤ] K) → f = g) :
    Function.Injective (comp ι L e C iC e₀ U) := by
  intro l l' h
  have h1 := congrArg (fun x => e₀ U.left (iC.hom.app (op U) x)) h
  simp only [e₀_iC_hom_comp_apply] at h1
  exact (e U).injective (precomp_injective ι _ hinj h1)

theorem mem_range_comp_iff (U : specInt.Fppf) (s : C.obj.obj (op U)) :
    s ∈ Set.range (comp ι L e C iC e₀ U) ↔
      e₀ U.left (iC.hom.app (op U) s) ∈ Set.range (precomp ι Γ(U.left, ⊤)) := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨e U l, (e₀_iC_hom_comp_apply ι L e C iC e₀ U l).symm⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨(e U).symm φ, ?_⟩
    have h1 : iC.hom.app (op U) (comp ι L e C iC e₀ U ((e U).symm φ)) = iC.hom.app (op U) s := by
      rw [iC_hom_comp_apply, AddEquiv.apply_symm_apply, hφ, AddEquiv.symm_apply_apply]
    have h2 := congrArg (iC.inv.app (op U)) h1
    have h3 := ConcreteCategory.congr_hom (iC.hom_inv_id_app (op U))
    exact (h3 _).symm.trans (h2.trans (h3 _))

end SheafSide

end MuPunctHom

end

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory in
theorem solution
    (p q : ℕ) [NeZero q]
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K)
    (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐc[ℤ] K)
    (hι : ∀ (R : Type) [CommRing R],
        (∀ f g : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) =
            g.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) → f = g) ∧
        ∀ g : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] R,
          (∃ f : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) = g) ↔
            ∃ a : R, a - 1 ∈ Ideal.span {(p : R)} ∧
              ∀ h : MonoidAlgebra ℤ (Multiplicative (ZMod q)),
                a * (g h - algebraMap ℤ R
                  (Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q))) h)) = 0)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj) :
    ∃ f : L ⟶ C,
      (∀ U : specInt.Fppf, Function.Injective (f.hom.app (Opposite.op U))) ∧
      ∀ (U : specInt.Fppf) (s : C.obj.obj (Opposite.op U)),
        s ∈ Set.range (f.hom.app (Opposite.op U)) ↔
          ∃ a : Γ(U.left, ⊤), a - 1 ∈ Ideal.span {(p : Γ(U.left, ⊤))} ∧
            a * ((FppfKummerSES.gmLiftedSectionUnit
                    ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (Opposite.op U.left)
                      (iC.hom.app (Opposite.op U) s)) : Γ(U.left, ⊤)) - 1) = 0 := by
  classical
  obtain ⟨e₀, he₀, hpin⟩ :=
    AlgebraicGeometry.exists_sectionsEquiv_algHom_muP_apply_eq_of_bialgEquiv_monoidAlgebra q
      (MonoidAlgebra ℤ (Multiplicative (ZMod q))) (BialgEquiv.refl ℤ _)
  have hn := MuPunctHom.comp_naturality ι L e hnat C iC e₀ he₀
  refine ⟨MuPunctHom.homLC ι L e C iC e₀ hn, ?_, ?_⟩
  · intro U
    exact MuPunctHom.comp_injective ι L e C iC e₀ U (hι Γ(U.left, ⊤)).1
  · intro U s
    change s ∈ Set.range (MuPunctHom.comp ι L e C iC e₀ U) ↔ _
    rw [MuPunctHom.mem_range_comp_iff, MuPunctHom.mem_range_precomp_iff, (hι Γ(U.left, ⊤)).2]
    refine exists_congr fun a => and_congr_right fun _ => ?_
    rw [MuPunctHom.forall_mul_sub_counit_eq_zero_iff]
    have hp := hpin U.left (iC.hom.app (Opposite.op U) s)
    rw [show (BialgEquiv.refl ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q)))).symm
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) = MuPunctHom.xGen q from rfl] at hp
    rw [show ((Additive.toMul (e₀ U.left (iC.hom.app (Opposite.op U) s))).ofConv) (MuPunctHom.xGen q)
        = (Additive.toMul (e₀ U.left (iC.hom.app (Opposite.op U) s))) (MuPunctHom.xGen q) from rfl, hp]

end S_AlgebraicGeometry_exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra
end P2MW
export P2MW.S_AlgebraicGeometry_exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra (solution)
