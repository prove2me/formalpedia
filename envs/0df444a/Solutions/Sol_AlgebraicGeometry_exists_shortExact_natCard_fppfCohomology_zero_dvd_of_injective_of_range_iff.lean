-- Prove2me | solution 1 for AlgebraicGeometry.exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a7372633-3311-5011-b880-de05a2625093

import Theorems.Thm_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_specInt_pullback_forget_comp
import Theorems.Thm_exists_sub_one_mem_span_and_mul_sub_one_eq_zero_of_pow_eq_one_of_sub_one_mem_span_pow
import Theorems.Thm_ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfH0Identification
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff

set_option autoImplicit false

p2m_open "CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme"

noncomputable section

namespace MuPunctureCokernel

theorem mono_of_injective {L C : Sheaf (smallFppfTopology specInt) Ab.{1}} (f : L ⟶ C)
    (hinj : ∀ U : specInt.Fppf, Function.Injective (f.hom.app (op U))) : Mono f := by
  haveI : ∀ X : (specInt.Fppf)ᵒᵖ, Mono (f.hom.app X) := fun X =>
    (AddCommGrpCat.mono_iff_injective _).mpr (hinj X.unop)
  haveI : Mono f.hom := NatTrans.mono_of_mono_app f.hom
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ f

theorem app_injective_of_mono {F G : Sheaf (smallFppfTopology specInt) Ab.{1}} (m : F ⟶ G) [Mono m]
    (U : (specInt.Fppf)ᵒᵖ) : Function.Injective (m.hom.app U) := by
  have hm : Mono ((sheafToPresheaf _ _).map m) := inferInstance
  have hm' : Mono (m.hom.app U) := (NatTrans.mono_iff_mono_app _).mp hm U
  exact (AddCommGrpCat.mono_iff_injective _).mp hm'

theorem shortExact_cokernel {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {L C : 𝒜} (f : L ⟶ C) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
  mono_f := ‹Mono f›
  epi_g := (inferInstance : Epi (cokernel.π f))

section Thickening

variable (p : ℕ) [Fact p.Prime] (q : ℕ)

abbrev lvl : ℕ := padicValNat p q + 1

abbrev thick : Scheme.{0} := Spec (CommRingCat.of (ZMod (p ^ lvl p q)))

abbrev ιT : thick p q ⟶ specInt := Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod (p ^ lvl p q))))

abbrev bc : specInt.Fppf ⥤ Scheme.{0} :=
  Scheme.Fppf.forget specInt ⋙ Over.pullback (ιT p q) ⋙ Over.forget (thick p q)

@[reassoc]
theorem bc_map_fst {V U : specInt.Fppf} (k : V ⟶ U) :
    (bc p q).map k ≫ pullback.fst U.hom (ιT p q) = pullback.fst V.hom (ιT p q) ≫ k.left := by
  dsimp [Over.pullback, Scheme.Fppf.forget]
  erw [pullback.lift_fst]
  try rfl

def πfst : bc p q ⟶ Scheme.Fppf.forget specInt ⋙ Over.forget specInt where
  app U := pullback.fst U.hom (ιT p q)
  naturality _ _ k := bc_map_fst p q k

def D : Sheaf (smallFppfTopology specInt) Ab.{1} :=
  ⟨(bc p q).op ⋙ (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj,
    AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_specInt_pullback_forget_comp (ιT p q)
      (FppfKummerSES.muPAbelianSheafLifted.{0} q)⟩

variable (C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)

def φ : C ⟶ D p q :=
  ObjectProperty.homMk
    (iC.hom ≫ Functor.whiskerRight (NatTrans.op (πfst p q)) (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)

theorem φ_app_apply (U : specInt.Fppf) (c : C.obj.obj (op U)) :
    (φ p q C iC).hom.app (op U) c =
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.map (pullback.fst U.hom (ιT p q)).op
        (iC.hom.app (op U) c) := rfl

end Thickening

section Units

variable (q : ℕ)

abbrev unitOf {X : Scheme.{0}}
    (y : ToType ((FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.obj (op X))) : (Γ(X, ⊤) : Type 0)ˣ :=
  FppfKummerSES.gmLiftedSectionUnit
    ((kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X) y)

theorem kernelι_app_injective (X : Scheme.{0}) :
    Function.Injective ((kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X)) := by
  have hm : Mono ((sheafToPresheaf _ _).map (kernel.ι (FppfKummerSES.gmPowSelf.{0} q))) :=
    inferInstance
  have hm' : Mono ((kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X)) := by
    have := (NatTrans.mono_iff_mono_app _).mp hm (op X)
    exact this
  exact (AddCommGrpCat.mono_iff_injective _).mp hm'

theorem eq_of_unitOf_eq {X : Scheme.{0}}
    (y y' : ToType ((FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.obj (op X)))
    (h : unitOf q y = unitOf q y') : y = y' := by
  apply kernelι_app_injective q X

  apply ULift.ext
  exact congrArg Additive.ofMul h

theorem unitOf_zero {X : Scheme.{0}} :
    unitOf q (0 : ToType ((FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.obj (op X))) = 1 := by
  have h0 : (kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X) 0 = 0 := map_zero _
  change FppfKummerSES.gmLiftedSectionUnit ((kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X) 0) = 1
  rw [h0]
  rfl

theorem eq_zero_of_unitOf_eq_one {X : Scheme.{0}}
    (y : ToType ((FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.obj (op X)))
    (h : unitOf q y = 1) : y = 0 := by
  apply eq_of_unitOf_eq q
  rw [h, unitOf_zero]

theorem unitOf_map {X Y : Scheme.{0}} (g : Y ⟶ X)
    (y : ToType ((FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.obj (op X))) :
    unitOf q ((FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.map g.op y) =
      Units.map g.appTop.hom.toMonoidHom (unitOf q y) := by
  simp only [unitOf]
  have hn := (kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.naturality g.op
  have hn' := ConcreteCategory.congr_hom hn y
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at hn'
  erw [hn']
  rfl

theorem unitOf_pow {X : Scheme.{0}}
    (y : ToType ((FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.obj (op X))) :
    (unitOf q y) ^ q = 1 := by
  have hc := kernel.condition (FppfKummerSES.gmPowSelf.{0} q)
  have hc' : ((kernel.ι (FppfKummerSES.gmPowSelf.{0} q)) ≫ FppfKummerSES.gmPowSelf.{0} q).hom.app (op X) y
      = 0 := by rw [hc]; rfl

  have h2 : (FppfKummerSES.gmPowSelf.{0} q).hom.app (op X)
      ((kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X) y) = 0 := hc'
  rw [FppfKummerSES.gmPowSelf_app_apply] at h2
  have h3 := congrArg (fun z : ULift.{1} (Additive ((Γ(X, ⊤) : Type 0)ˣ)) => z.down.toMul) h2
  convert h3 using 1 <;> rfl

end Units

theorem map_eq_zero_of_mul_eq_zero {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (p : ℕ) (N : ℕ) (hS : (p : S) ^ N = 0) (a t x : R) (hat : a - 1 = t * p) (hax : a * x = 0) :
    g x = 0 := by
  have hx : ∀ n : ℕ, x = (-(t * p)) ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : x = -(t * p) * x := by
        have : a = 1 + t * p := by linear_combination hat
        rw [this] at hax
        linear_combination hax
      calc x = (-(t * p)) ^ n * x := ih
        _ = (-(t * p)) ^ n * (-(t * p) * x) := by rw [← h1]
        _ = (-(t * p)) ^ (n + 1) * x := by ring
  rw [hx N, map_mul, map_pow, map_neg, map_mul, map_natCast, neg_pow, mul_pow]
  rw [hS]; ring

theorem map_eq_one_of_mul_sub_one_eq_zero {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (p : ℕ) (N : ℕ) (hS : (p : S) ^ N = 0) (a t y : R) (hat : a - 1 = t * p) (hay : a * (y - 1) = 0) :
    g y = 1 := by
  have h := map_eq_zero_of_mul_eq_zero g p N hS a t (y - 1) hat hay
  rwa [map_sub, map_one, sub_eq_zero] at h

variable (p : ℕ) [Fact p.Prime] (q : ℕ)

theorem natCast_pow_lvl_eq_zero (U : specInt.Fppf) :
    ((p : ℕ) : (Γ((bc p q).obj U, ⊤) : Type 0)) ^ lvl p q = 0 := by

  let r : ZMod (p ^ lvl p q) →+* (Γ((bc p q).obj U, ⊤) : Type 0) :=
    ((pullback.snd U.hom (ιT p q)).appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ZMod (p ^ lvl p q)))).inv.hom
  have h := congrArg r (ZMod.natCast_self (p ^ lvl p q))
  rw [map_natCast, map_zero, Nat.cast_pow] at h
  exact h

variable {p q}
variable (L C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)
    (f : L ⟶ C)
    (hrange :
      ∀ (U : specInt.Fppf) (s : C.obj.obj (Opposite.op U)),
        s ∈ Set.range (f.hom.app (Opposite.op U)) ↔
          ∃ a : Γ(U.left, ⊤), a - 1 ∈ Ideal.span {(p : Γ(U.left, ⊤))} ∧
            a * ((FppfKummerSES.gmLiftedSectionUnit
                    ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (Opposite.op U.left)
                      (iC.hom.app (Opposite.op U) s)) : Γ(U.left, ⊤)) - 1) = 0)

include hrange in

theorem φ_app_eq_zero_of_mem_range (U : specInt.Fppf) (c : C.obj.obj (op U))
    (hc : c ∈ Set.range (f.hom.app (op U))) : (φ p q C iC).hom.app (op U) c = 0 := by
  obtain ⟨a, ha1, ha⟩ := (hrange U c).mp hc
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp ha1
  rw [φ_app_apply]
  apply eq_zero_of_unitOf_eq_one
  rw [unitOf_map]
  apply Units.ext
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]

  exact map_eq_one_of_mul_sub_one_eq_zero (pullback.fst U.hom (ιT p q)).appTop.hom p (lvl p q)
    (natCast_pow_lvl_eq_zero p q U) a t _ ht.symm ha

include hrange in
theorem comp_φ_eq_zero : f ≫ φ p q C iC = 0 := by
  ext U : 3
  apply AddCommGrpCat.ext
  intro s
  change (φ p q C iC).hom.app U (f.hom.app U s) = 0
  exact φ_app_eq_zero_of_mem_range L C iC f hrange U.unop _ ⟨s, rfl⟩

end MuPunctureCokernel

namespace MuPunctureCokernel

section Probe

variable (p : ℕ) [Fact p.Prime] (q : ℕ)

theorem isoSpec_inv_appTop (X : Scheme.{0}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have h : (Scheme.ΓSpecIso Γ(X, ⊤)).hom ≫ X.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_toSpecΓ]
    simp
  exact ((Iso.eq_inv_comp _).mpr h).trans (Category.comp_id _)

def zmodHomOfEqZero (R : Type*) [CommRing R] (n : ℕ) (h : (n : R) = 0) : ZMod n →+* R :=
  (Ideal.Quotient.lift (Ideal.span {(n : ℤ)}) (Int.castRingHom R) (by
      intro z hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, h, mul_zero])).comp
    (Int.quotientSpanNatEquivZMod n).symm.toRingHom

set_option maxHeartbeats 3200000 in

theorem mem_span_pow_of_appTop_fst_eq_zero (V : specInt.Fppf) [hV : IsAffine V.left]
    (x : (Γ(V.left, ⊤) : Type 0)) (hx : (pullback.fst V.hom (ιT p q)).appTop x = 0) :
    x ∈ Ideal.span {((p : ℕ) : (Γ(V.left, ⊤) : Type 0)) ^ lvl p q} := by
  let I : Ideal (Γ(V.left, ⊤) : Type 0) := Ideal.span {((p : ℕ) : (Γ(V.left, ⊤) : Type 0)) ^ lvl p q}
  have hpI : ((p ^ lvl p q : ℕ) : (Γ(V.left, ⊤) : Type 0) ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.subset_span (Set.mem_singleton _)

  let F : Γ(V.left, ⊤) ⟶ CommRingCat.of ((Γ(V.left, ⊤) : Type 0) ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let toV : Spec (CommRingCat.of ((Γ(V.left, ⊤) : Type 0) ⧸ I)) ⟶ V.left :=
    Spec.map F ≫ V.left.isoSpec.inv
  let toT : Spec (CommRingCat.of ((Γ(V.left, ⊤) : Type 0) ⧸ I)) ⟶ thick p q :=
    Spec.map (CommRingCat.ofHom (zmodHomOfEqZero _ _ hpI))
  have hcomm : toV ≫ V.hom = toT ≫ ιT p q := specZIsTerminal.hom_ext _ _

  have h1 : toV.appTop x = 0 := by
    have e : toV = pullback.lift toV toT hcomm ≫ pullback.fst V.hom (ιT p q) :=
      (pullback.lift_fst _ _ _).symm
    rw [e]
    change (pullback.lift toV toT hcomm).appTop ((pullback.fst V.hom (ιT p q)).appTop x) = 0
    rw [hx]
    exact map_zero _

  have h2 : toV.appTop = V.left.isoSpec.inv.appTop ≫ (Spec.map F).appTop :=
    Scheme.Hom.comp_appTop _ _
  rw [h2, isoSpec_inv_appTop, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply] at h1
  have h5 : F x = 0 :=
    (Scheme.ΓSpecIso (CommRingCat.of ((Γ(V.left, ⊤) : Type 0) ⧸ I))).commRingCatIsoToRingEquiv.symm.injective
      (h1.trans (map_zero _).symm)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h5

set_option maxHeartbeats 1600000 in

theorem eq_zero_of_natCast_mul_eq_zero (V : specInt.Fppf) [hV : IsAffine V.left]
    (x : (Γ(V.left, ⊤) : Type 0)) (hx : ((p : ℕ) : (Γ(V.left, ⊤) : Type 0)) * x = 0) : x = 0 := by
  haveI : IsAffine ((𝟭 Scheme).obj V.left) := hV
  haveI : IsAffine ((Functor.fromPUnit.{0} specInt).obj V.right) := inferInstanceAs (IsAffine specInt)
  let g : (Γ(specInt, ⊤) : Type 0) →+* (Γ(V.left, ⊤) : Type 0) := (V.hom.appTop).hom
  have hflat : g.Flat := HasRingHomProperty.appTop (P := @Flat) _ V.prop.1
  letI := g.toAlgebra
  haveI : Module.Flat (Γ(specInt, ⊤) : Type 0) (Γ(V.left, ⊤) : Type 0) := hflat

  let e : (Γ(specInt, ⊤) : Type 0) ≃+* ℤ := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv
  haveI : NoZeroDivisors (Γ(specInt, ⊤) : Type 0) :=
    e.injective.noZeroDivisors e.toRingHom (map_zero _) (map_mul _)
  have hp0 : ((p : ℕ) : (Γ(specInt, ⊤) : Type 0)) ≠ 0 := by
    intro h
    have := congrArg e h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  have hreg : IsRegular ((p : ℕ) : (Γ(specInt, ⊤) : Type 0)) := IsRegular.of_ne_zero hp0
  have hsm : IsSMulRegular (Γ(V.left, ⊤) : Type 0) ((p : ℕ) : (Γ(specInt, ⊤) : Type 0)) :=
    Module.Flat.isSMulRegular_of_isRegular hreg
  apply hsm
  change ((p : ℕ) : (Γ(specInt, ⊤) : Type 0)) • x = ((p : ℕ) : (Γ(specInt, ⊤) : Type 0)) • (0 : (Γ(V.left, ⊤) : Type 0))
  rw [smul_zero, Algebra.smul_def, map_natCast]
  exact hx

end Probe

section Affine

variable (p : ℕ) [Fact p.Prime] (q : ℕ)
variable (L C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)
    (f : L ⟶ C)
    (hrange :
      ∀ (U : specInt.Fppf) (s : C.obj.obj (Opposite.op U)),
        s ∈ Set.range (f.hom.app (Opposite.op U)) ↔
          ∃ a : Γ(U.left, ⊤), a - 1 ∈ Ideal.span {(p : Γ(U.left, ⊤))} ∧
            a * ((FppfKummerSES.gmLiftedSectionUnit
                    ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (Opposite.op U.left)
                      (iC.hom.app (Opposite.op U) s)) : Γ(U.left, ⊤)) - 1) = 0)

set_option maxHeartbeats 1600000 in
include hrange in

theorem mem_range_of_φ_eq_zero_affine (hq : q ≠ 0) (V : specInt.Fppf) [IsAffine V.left]
    (c : C.obj.obj (op V)) (hc : (φ p q C iC).hom.app (op V) c = 0) :
    c ∈ Set.range (f.hom.app (op V)) := by
  let u : (Γ(V.left, ⊤) : Type 0)ˣ := unitOf q (iC.hom.app (op V) c)

  have hc' : (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.map (pullback.fst V.hom (ιT p q)).op
      (iC.hom.app (op V) c) = 0 := hc
  have h0 : unitOf q ((FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.map
      (pullback.fst V.hom (ιT p q)).op (iC.hom.app (op V) c)) = 1 := by
    rw [hc', unitOf_zero]
  have hu1 : Units.map (pullback.fst V.hom (ιT p q)).appTop.hom.toMonoidHom u = 1 :=
    (unitOf_map q (pullback.fst V.hom (ιT p q)) (iC.hom.app (op V) c)).symm.trans h0
  let g : (Γ(V.left, ⊤) : Type 0) →+* (Γ(pullback V.hom (ιT p q), ⊤) : Type 0) :=
    (pullback.fst V.hom (ιT p q)).appTop.hom
  have hu1' : g (u : Γ(V.left, ⊤)) = 1 := by
    have := congrArg Units.val hu1
    simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one] using this
  have hx : g ((u : Γ(V.left, ⊤)) - 1) = 0 := by
    rw [map_sub, map_one, hu1', sub_self]
  have hN := mem_span_pow_of_appTop_fst_eq_zero p q V _ hx
  have hupow : (u : Γ(V.left, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, unitOf_pow, Units.val_one]
  obtain ⟨a, ha1, ha⟩ :=
    exists_sub_one_mem_span_and_mul_sub_one_eq_zero_of_pow_eq_one_of_sub_one_mem_span_pow
      p Fact.out q hq _ (eq_zero_of_natCast_mul_eq_zero p V) (u : Γ(V.left, ⊤)) hupow hN
  exact (hrange V c).mpr ⟨a, ha1, ha⟩

end Affine

section Glue

def openObj (U : specInt.Fppf) (W : U.left.Opens) : specInt.Fppf :=
  MorphismProperty.Over.mk ⊤ (W.ι ≫ U.hom)
    (fppfProperty.comp_mem _ _ ⟨inferInstance, inferInstance⟩ U.prop)

def openHom (U : specInt.Fppf) (W : U.left.Opens) : openObj U W ⟶ U :=
  MorphismProperty.Over.homMk W.ι rfl trivial

theorem openHom_left (U : specInt.Fppf) (W : U.left.Opens) : (openHom U W).left = W.ι := rfl

scoped instance (U : specInt.Fppf) (W : U.left.affineOpens) : IsAffine (openObj U W.1).left := W.2

theorem generate_openHom_mem (U : specInt.Fppf) {K : Type} (W : K → U.left.Opens)
    (hW : ∀ x : U.left, ∃ k, x ∈ W k) :
    Sieve.generate (Presieve.ofArrows (fun k => openObj U (W k)) (fun k => openHom U (W k))) ∈
      smallFppfTopology specInt U := by
  rw [smallFppfTopology_eq_restrictedTopology, Functor.mem_restrictedTopology_iff,
      GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv ((Scheme.Fppf.forget specInt).obj U)
      (Sieve.functorPushforward (Scheme.Fppf.forget specInt)
        (Sieve.generate (Presieve.ofArrows (fun k => openObj U (W k)) (fun k => openHom U (W k))))) ∈
    Scheme.grothendieckTopology fppfProperty U.left
  refine (Scheme.mem_grothendieckTopology_iff (X := U.left)).mpr
    ⟨Cover.mkOfCovers K (fun k => ↑(W k)) (fun k => (W k).ι)
      (fun x => by obtain ⟨k, hk⟩ := hW x; exact ⟨k, ⟨x, hk⟩, rfl⟩)
      (fun k => ⟨inferInstance, inferInstance⟩), ?_⟩
  rintro Y g ⟨k⟩
  rw [Sieve.overEquiv_iff]
  have hgen : (Sieve.generate (Presieve.ofArrows (fun k => openObj U (W k)) (fun k => openHom U (W k)))).arrows
      (openHom U (W k)) := ⟨_, 𝟙 _, _, Presieve.ofArrows.mk k, Category.id_comp _⟩
  exact Sieve.image_mem_functorPushforward (Scheme.Fppf.forget specInt) _ hgen

variable {L C : Sheaf (smallFppfTopology specInt) Ab.{1}} (f : L ⟶ C)

theorem naturality_apply {F G : (specInt.Fppf)ᵒᵖ ⥤ Ab.{1}} (α : F ⟶ G) {U V : (specInt.Fppf)ᵒᵖ}
    (k : U ⟶ V) (x : F.obj U) : α.app V (F.map k x) = G.map k (α.app U x) := by
  change (F.map k ≫ α.app V) x = (α.app U ≫ G.map k) x
  rw [α.naturality]

set_option maxHeartbeats 1600000 in

theorem mem_range_of_forall_openHom
    (hinj : ∀ U : specInt.Fppf, Function.Injective (f.hom.app (op U)))
    (U : specInt.Fppf) {K : Type} (W : K → U.left.Opens) (hW : ∀ x : U.left, ∃ k, x ∈ W k)
    (s : C.obj.obj (op U))
    (h : ∀ k, C.obj.map (openHom U (W k)).op s ∈ Set.range (f.hom.app (op (openObj U (W k))))) :
    s ∈ Set.range (f.hom.app (op U)) := by
  choose t ht using h
  have hmem := generate_openHom_mem U W hW

  have hL : Presieve.IsSheafFor (L.obj ⋙ forget Ab)
      (Presieve.ofArrows (fun k => openObj U (W k)) (fun k => openHom U (W k))) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact ((isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget (smallFppfTopology specInt) L.obj (forget Ab)).mp
        L.property)) _ hmem
  have hC : Presieve.IsSeparatedFor (C.obj ⋙ forget Ab)
      (Presieve.ofArrows (fun k => openObj U (W k)) (fun k => openHom U (W k))) := by
    refine Presieve.IsSheafFor.isSeparatedFor ?_
    rw [Presieve.isSheafFor_iff_generate]
    exact ((isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget (smallFppfTopology specInt) C.obj (forget Ab)).mp
        C.property)) _ hmem

  have hcompat : Presieve.Arrows.Compatible (L.obj ⋙ forget Ab) (fun k => openHom U (W k)) t := by
    intro i j Z gi gj hg
    apply hinj Z
    change f.hom.app (op Z) (L.obj.map gi.op (t i)) = f.hom.app (op Z) (L.obj.map gj.op (t j))
    rw [naturality_apply, naturality_apply, ht, ht]
    change (C.obj.map (openHom U (W i)).op ≫ C.obj.map gi.op) s =
      (C.obj.map (openHom U (W j)).op ≫ C.obj.map gj.op) s
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hg]
  obtain ⟨tU, htU, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hL t hcompat
  refine ⟨tU, hC.ext ?_⟩
  rintro _ _ ⟨k⟩
  change C.obj.map (openHom U (W k)).op (f.hom.app (op U) tU) = C.obj.map (openHom U (W k)).op s
  rw [← naturality_apply, ← ht k]
  exact congrArg (f.hom.app _) (htU k)

end Glue

section Exactness

variable (p : ℕ) [Fact p.Prime] (q : ℕ)
variable (L C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)
    (f : L ⟶ C) (hinj : ∀ U : specInt.Fppf, Function.Injective (f.hom.app (Opposite.op U)))
    (hrange :
      ∀ (U : specInt.Fppf) (s : C.obj.obj (Opposite.op U)),
        s ∈ Set.range (f.hom.app (Opposite.op U)) ↔
          ∃ a : Γ(U.left, ⊤), a - 1 ∈ Ideal.span {(p : Γ(U.left, ⊤))} ∧
            a * ((FppfKummerSES.gmLiftedSectionUnit
                    ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (Opposite.op U.left)
                      (iC.hom.app (Opposite.op U) s)) : Γ(U.left, ⊤)) - 1) = 0)

include hinj hrange in

theorem mem_range_of_φ_eq_zero (hq : q ≠ 0) (U : specInt.Fppf)
    (c : C.obj.obj (op U)) (hc : (φ p q C iC).hom.app (op U) c = 0) :
    c ∈ Set.range (f.hom.app (op U)) := by
  refine mem_range_of_forall_openHom f hinj U (fun W : U.left.affineOpens => W.1)
    (fun x => ?_) c (fun W => ?_)
  · obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) (by simp)
    exact ⟨⟨W, hW⟩, hxW⟩
  · apply mem_range_of_φ_eq_zero_affine p q L C iC f hrange hq
    change (φ p q C iC).hom.app _ (C.obj.map (openHom U W.1).op c) = 0
    rw [naturality_apply, hc, map_zero]

set_option maxHeartbeats 1600000 in
include hinj hrange in
theorem exact_f_φ (hq : q ≠ 0) (w : f ≫ φ p q C iC = 0) :
    (ShortComplex.mk f (φ p q C iC) w).Exact := by
  haveI : Mono f := mono_of_injective f hinj
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  dsimp only
  set k := kernel.lift (φ p q C iC) f w with hk
  have hkι : k ≫ kernel.ι (φ p q C iC) = f := kernel.lift_ι _ _ _
  have hkι' : ∀ (X : (specInt.Fppf)ᵒᵖ) (x : L.obj.obj X),
      (kernel.ι (φ p q C iC)).hom.app X (k.hom.app X x) = f.hom.app X x := by
    intro X x
    change ((k ≫ kernel.ι (φ p q C iC)).hom.app X) x = _
    rw [hkι]

  suffices hiso : IsIso k by infer_instance
  have happ : ∀ X : (specInt.Fppf)ᵒᵖ, IsIso (k.hom.app X) := by
    intro X
    have hbij : Function.Bijective (k.hom.app X) := by
      constructor
      · intro x y hxy
        apply hinj X.unop
        rw [← hkι' X x, ← hkι' X y]
        exact congrArg _ hxy
      · intro y
        have hc : (φ p q C iC).hom.app X ((kernel.ι (φ p q C iC)).hom.app X y) = 0 := by
          change ((kernel.ι (φ p q C iC) ≫ φ p q C iC).hom.app X) y = 0
          rw [kernel.condition]
          rfl
        obtain ⟨x, hx⟩ := mem_range_of_φ_eq_zero p q L C iC f hinj hrange hq X.unop _ hc
        refine ⟨x, ?_⟩
        apply app_injective_of_mono (kernel.ι (φ p q C iC)) X
        rw [hkι' X x, hx]
    have : IsIso ((forget Ab).map (k.hom.app X)) := (isIso_iff_bijective _).mpr hbij
    exact isIso_of_reflects_iso (k.hom.app X) (forget Ab)
  haveI : IsIso k.hom := NatIso.isIso_of_isIso_app k.hom
  haveI : IsIso ((sheafToPresheaf _ _).map k) := by
    change IsIso k.hom; infer_instance
  exact isIso_of_fully_faithful (sheafToPresheaf _ _) k

end Exactness

section H0

variable (p : ℕ) [Fact p.Prime] (q : ℕ)

def unitHom (X : Scheme.{0}) :
    ToType ((FppfKummerSES.muPAbelianSheafLifted.{0} q).obj.obj (op X)) →+ Additive ((Γ(X, ⊤) : Type 0)ˣ) where
  toFun y := Additive.ofMul (unitOf q y)
  map_zero' := by rw [unitOf_zero]; rfl
  map_add' y y' := by
    have h : (kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X) (y + y') =
        (kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X) y +
          (kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X) y' := map_add _ _ _
    change Additive.ofMul (FppfKummerSES.gmLiftedSectionUnit
      ((kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (op X) (y + y'))) = _
    rw [h]
    rfl

theorem unitHom_injective (X : Scheme.{0}) : Function.Injective (unitHom q X) := by
  intro y y' h
  exact eq_of_unitOf_eq q y y' (Additive.ofMul.injective h)

scoped instance : IsIso (pullback.snd (fppfTerminal specInt).hom (ιT p q)) := by
  change IsIso (pullback.snd (𝟙 specInt) (ιT p q))
  infer_instance

def ΓbcTerminalEquiv :
    (Γ((bc p q).obj (fppfTerminal specInt), ⊤) : Type 0) ≃+* ZMod (p ^ lvl p q) :=
  ((Scheme.Γ.mapIso (asIso (pullback.snd (fppfTerminal specInt).hom (ιT p q))).op).symm ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (ZMod (p ^ lvl p q)))).commRingCatIsoToRingEquiv

set_option maxHeartbeats 1600000 in
theorem exists_embedding :
    ∃ emb : fppfCohomology specInt (D p q) 0 →+ Additive (ZMod (p ^ lvl p q))ˣ,
      Function.Injective emb ∧ ∀ x, (Additive.toMul (emb x)) ^ q = 1 := by
  let e0 := fppfCohomologySpecIntZeroAddEquiv (D p q)
  let r := ΓbcTerminalEquiv p q
  let e2 : Additive ((Γ((bc p q).obj (fppfTerminal specInt), ⊤) : Type 0)ˣ) ≃+
      Additive (ZMod (p ^ lvl p q))ˣ :=
    MulEquiv.toAdditive (Units.mapEquiv r.toMulEquiv)
  refine ⟨e2.toAddMonoidHom.comp ((unitHom q _).comp e0.toAddMonoidHom), ?_, ?_⟩
  · exact e2.injective.comp ((unitHom_injective q _).comp e0.injective)
  · intro x
    change (Units.mapEquiv r.toMulEquiv (unitOf q (e0 x))) ^ q = 1
    rw [← map_pow, unitOf_pow, map_one]

end H0

end MuPunctureCokernel
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff.MuPunctureCokernel"

open MuPunctureCokernel

set_option maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)
    (f : L ⟶ C) (hinj : ∀ U : specInt.Fppf, Function.Injective (f.hom.app (Opposite.op U)))
    (hrange :
      ∀ (U : specInt.Fppf) (s : C.obj.obj (Opposite.op U)),
        s ∈ Set.range (f.hom.app (Opposite.op U)) ↔
          ∃ a : Γ(U.left, ⊤), a - 1 ∈ Ideal.span {(p : Γ(U.left, ⊤))} ∧
            a * ((FppfKummerSES.gmLiftedSectionUnit
                    ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (Opposite.op U.left)
                      (iC.hom.app (Opposite.op U) s)) : Γ(U.left, ⊤)) - 1) = 0) :
    ∃ (Q : Sheaf (smallFppfTopology specInt) Ab.{1}) (g : C ⟶ Q) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧ Nat.card (fppfCohomology specInt Q 0) ∣ q := by
  haveI : Mono f := mono_of_injective f hinj
  refine ⟨cokernel f, cokernel.π f, cokernel.condition f, shortExact_cokernel f, ?_⟩
  rcases Nat.eq_zero_or_pos q with hq | hq
  · rw [hq]; exact dvd_zero _

  have w : f ≫ φ p q C iC = 0 := comp_φ_eq_zero L C iC f hrange
  have hExact : (ShortComplex.mk f (φ p q C iC) w).Exact := exact_f_φ p q L C iC f hinj hrange hq.ne' w
  haveI : Mono (cokernel.desc f (φ p q C iC) w) := hExact.mono_cokernelDesc

  have hinjH0 : Function.Injective (fppfCohomologyMap specInt (cokernel.desc f (φ p q C iC) w) 0) :=
    FppfCohomologyLES.cohomologyMap_zero_injective_of_mono (cokernel.desc f (φ p q C iC) w)

  have hemb : ∃ emb : fppfCohomology specInt (D p q) 0 →+ Additive (ZMod (p ^ lvl p q))ˣ,
      Function.Injective emb ∧ ∀ x, (Additive.toMul (emb x)) ^ q = 1 := exists_embedding p q
  obtain ⟨emb, hembi, hembq⟩ := hemb
  let θ : fppfCohomology specInt (cokernel f) 0 →+ Additive (ZMod (p ^ lvl p q))ˣ :=
    emb.comp (fppfCohomologyMap specInt (cokernel.desc f (φ p q C iC) w) 0)
  have hθ : Function.Injective θ := hembi.comp hinjH0
  let H : Subgroup (ZMod (p ^ (padicValNat p q + 1)))ˣ := θ.range.toSubgroup
  have hH : ∀ x ∈ H, x ^ q = 1 := by
    rintro x ⟨y, rfl⟩
    exact hembq _
  have hcard : Nat.card (fppfCohomology specInt (cokernel f) 0) = Nat.card H := by
    rw [Nat.card_congr (Equiv.ofInjective θ hθ)]
    rfl
  rw [hcard]
  exact ZMod.natCard_dvd_of_forall_pow_eq_one_units_prime_pow p Fact.out q hq.ne' H hH

end
end S_AlgebraicGeometry_exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff
end P2MW
export P2MW.S_AlgebraicGeometry_exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff (solution)
