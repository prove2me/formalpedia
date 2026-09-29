-- Prove2me | solution 1 for AlgebraicGeometry.exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4fb701c5-a7ef-599b-8056-e05c2b27bad3

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two

set_option autoImplicit false

noncomputable section

namespace MuTwoGroupAlgebraRepr

namespace KernelSections

p2m_open "CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite"
open FppfKummerSES

universe u

section PreservationChain

def sheafKernelPresheafIso (p : ℕ) :
    (muPAbelianSheafLifted.{u} p).obj ≅ kernel ((gmPowSelf.{u} p).hom) :=
  PreservesKernel.iso (sheafToPresheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (gmPowSelf.{u} p)

def evalKernelIso (p : ℕ) (T : Scheme.{u}) :
    (kernel ((gmPowSelf.{u} p).hom)).obj (op T) ≅ kernel ((gmPowSelf.{u} p).hom.app (op T)) :=
  PreservesKernel.iso ((evaluation Scheme.{u}ᵒᵖ Ab.{u + 1}).obj (op T)) ((gmPowSelf.{u} p).hom)

def muPSectionsCatKernelIso (p : ℕ) (T : Scheme.{u}) :
    (muPAbelianSheafLifted.{u} p).obj.obj (op T) ≅
      kernel ((gmPowSelf.{u} p).hom.app (op T)) :=
  (sheafKernelPresheafIso.{u} p).app (op T) ≪≫ evalKernelIso.{u} p T

def muPSectionsKernelIso (p : ℕ) (T : Scheme.{u}) :
    (muPAbelianSheafLifted.{u} p).obj.obj (op T) ≅
      AddCommGrpCat.of (((gmPowSelf.{u} p).hom.app (op T)).hom.ker) :=
  muPSectionsCatKernelIso.{u} p T ≪≫
    AddCommGrpCat.kernelIsoKer ((gmPowSelf.{u} p).hom.app (op T))

theorem sheafKernelPresheafIso_inv_ι (p : ℕ) :
    (sheafKernelPresheafIso.{u} p).inv ≫ (kernel.ι (gmPowSelf.{u} p)).hom =
      kernel.ι ((gmPowSelf.{u} p).hom) :=
  PreservesKernel.iso_inv_ι (sheafToPresheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    (gmPowSelf.{u} p)

theorem evalKernelIso_inv_ι (p : ℕ) (T : Scheme.{u}) :
    (evalKernelIso.{u} p T).inv ≫ (kernel.ι ((gmPowSelf.{u} p).hom)).app (op T) =
      kernel.ι ((gmPowSelf.{u} p).hom.app (op T)) :=
  PreservesKernel.iso_inv_ι ((evaluation Scheme.{u}ᵒᵖ Ab.{u + 1}).obj (op T))
    ((gmPowSelf.{u} p).hom)

theorem muPSectionsKernelIso_inv_comp_ι (p : ℕ) (T : Scheme.{u}) :
    (muPSectionsKernelIso.{u} p T).inv ≫ (kernel.ι (gmPowSelf.{u} p)).hom.app (op T) =
      AddCommGrpCat.ofHom
        (AddSubgroup.subtype (((gmPowSelf.{u} p).hom.app (op T)).hom.ker)) := by
  simp only [muPSectionsKernelIso, muPSectionsCatKernelIso, Iso.trans_inv, Iso.app_inv,
    Category.assoc]
  rw [← NatTrans.comp_app, sheafKernelPresheafIso_inv_ι, evalKernelIso_inv_ι,
    AddCommGrpCat.kernelIsoKer_inv_comp_ι]

theorem muPSectionsKernelIso_hom_comp_subtype (p : ℕ) (T : Scheme.{u}) :
    (muPSectionsKernelIso.{u} p T).hom ≫
      AddCommGrpCat.ofHom
        (AddSubgroup.subtype (((gmPowSelf.{u} p).hom.app (op T)).hom.ker)) =
      (kernel.ι (gmPowSelf.{u} p)).hom.app (op T) := by
  rw [← muPSectionsKernelIso_inv_comp_ι p T, Iso.hom_inv_id_assoc]

theorem muPSectionsKernelIso_hom_apply_val (p : ℕ) (T : Scheme.{u})
    (x : ToType ((muPAbelianSheafLifted.{u} p).obj.obj (op T))) :
    ((muPSectionsKernelIso.{u} p T).hom x).1 =
      (kernel.ι (gmPowSelf.{u} p)).hom.app (op T) x :=
  ConcreteCategory.congr_hom (muPSectionsKernelIso_hom_comp_subtype p T) x

end PreservationChain

section TorsionIdentification

theorem mem_gmPowSelfApp_ker_iff (p : ℕ) (T : Scheme.{u})
    (t : ToType (GmAbelianSheafLifted.{u}.obj.obj (op T))) :
    t ∈ (((gmPowSelf.{u} p).hom.app (op T)).hom).ker ↔
      (gmLiftedSectionUnit t) ^ p = 1 := by
  constructor
  · intro h
    have e1 : ULift.up.{u + 1} (Additive.ofMul ((gmLiftedSectionUnit t) ^ p)) =
        (0 : ULift.{u + 1} (Additive ((Γ(T, ⊤) : Type u)ˣ))) :=
      (gmPowSelf_app_apply.{u} p T t).symm.trans (AddMonoidHom.mem_ker.mp h)
    exact congrArg (fun s => Additive.toMul s.down) e1
  · intro h
    refine AddMonoidHom.mem_ker.mpr ?_
    refine (gmPowSelf_app_apply.{u} p T t).trans ?_
    exact congrArg (fun w => ULift.up.{u + 1} (Additive.ofMul w)) h

end TorsionIdentification

section Sections

variable (p : ℕ)

def secUnit (T : Scheme.{u}) (x : ToType ((muPAbelianSheafLifted.{u} p).obj.obj (op T))) :
    ((Γ(T, ⊤) : Type u))ˣ :=
  gmLiftedSectionUnit ((kernel.ι (gmPowSelf.{u} p)).hom.app (op T) x)

theorem secUnit_eq (T : Scheme.{u}) (x : ToType ((muPAbelianSheafLifted.{u} p).obj.obj (op T))) :
    secUnit p T x = gmLiftedSectionUnit ((muPSectionsKernelIso.{u} p T).hom x).1 := by
  rw [muPSectionsKernelIso_hom_apply_val]
  rfl

theorem secUnit_pow (T : Scheme.{u}) (x : ToType ((muPAbelianSheafLifted.{u} p).obj.obj (op T))) :
    secUnit p T x ^ p = 1 := by
  rw [secUnit_eq]
  exact (mem_gmPowSelfApp_ker_iff p T _).mp ((muPSectionsKernelIso.{u} p T).hom x).2

theorem secUnit_add (T : Scheme.{u})
    (x y : ToType ((muPAbelianSheafLifted.{u} p).obj.obj (op T))) :
    secUnit p T (x + y) = secUnit p T x * secUnit p T y := by
  simp only [secUnit]
  have hadd : (ConcreteCategory.hom ((kernel.ι (gmPowSelf.{u} p)).hom.app (op T))) (x + y) =
      (ConcreteCategory.hom ((kernel.ι (gmPowSelf.{u} p)).hom.app (op T))) x +
        (ConcreteCategory.hom ((kernel.ι (gmPowSelf.{u} p)).hom.app (op T))) y :=
    map_add _ x y
  rw [hadd]
  rfl

theorem secUnit_map {T V : Scheme.{u}} (h : V ⟶ T)
    (x : ToType ((muPAbelianSheafLifted.{u} p).obj.obj (op T))) :
    secUnit p V ((muPAbelianSheafLifted.{u} p).obj.map h.op x) =
      Units.map (h.appTop).hom.toMonoidHom (secUnit p T x) := by
  have hnat : (kernel.ι (gmPowSelf.{u} p)).hom.app (op V)
        ((muPAbelianSheafLifted.{u} p).obj.map h.op x) =
      GmAbelianSheafLifted.{u}.obj.map h.op
        ((kernel.ι (gmPowSelf.{u} p)).hom.app (op T) x) :=
    ConcreteCategory.congr_hom ((kernel.ι (gmPowSelf.{u} p)).hom.naturality h.op) x
  simp only [secUnit]
  rw [hnat]
  rfl

def secKerEquiv (T : Scheme.{u}) :
    ToType ((muPAbelianSheafLifted.{u} p).obj.obj (op T)) ≃+
      (((gmPowSelf.{u} p).hom.app (op T)).hom).ker :=
  (muPSectionsKernelIso.{u} p T).addCommGroupIsoToAddEquiv

theorem secKerEquiv_apply_unit (T : Scheme.{u})
    (x : ToType ((muPAbelianSheafLifted.{u} p).obj.obj (op T))) :
    gmLiftedSectionUnit (secKerEquiv p T x).1 = secUnit p T x :=
  (secUnit_eq p T x).symm

end Sections

end KernelSections

namespace GroupAlgebraPoints

p2m_open "Algebra Coalgebra Bialgebra TensorProduct Algebra.TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"

abbrev C2 : Type := Multiplicative (ZMod 2)

def gen : C2 := Multiplicative.ofAdd 1

theorem gen_mul_gen : gen * gen = 1 := by
  rw [gen, ← ofAdd_add]
  rfl

theorem C2_cases (m : C2) : m = 1 ∨ m = gen := by
  have h : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  rcases h (Multiplicative.toAdd m) with h0 | h1
  · exact Or.inl (congrArg Multiplicative.ofAdd h0)
  · exact Or.inr (congrArg Multiplicative.ofAdd h1)

theorem toAdd_gen_val : (Multiplicative.toAdd gen).val = 1 := rfl

def chi {R : Type} [CommRing R] (x : R) (hx : x * x = 1) : C2 →* R where
  toFun m := x ^ (Multiplicative.toAdd m).val
  map_one' := by
    show x ^ (0 : ZMod 2).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' a b := by
    show x ^ ((Multiplicative.toAdd a + Multiplicative.toAdd b).val) =
      x ^ (Multiplicative.toAdd a).val * x ^ (Multiplicative.toAdd b).val
    have hx2 : x ^ 2 = 1 := by rw [pow_two, hx]
    rw [ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd a).val +
      (Multiplicative.toAdd b).val) 2, pow_add, pow_mul, hx2, one_pow, mul_one]

theorem chi_gen {R : Type} [CommRing R] (x : R) (hx : x * x = 1) : chi x hx gen = x := by
  show x ^ (Multiplicative.toAdd gen).val = x
  rw [toAdd_gen_val, pow_one]

section Transport

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K]

attribute [local instance 10000] Algebra.toModule

def uGen (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) : K :=
  f.symm (MonoidAlgebra.of ℤ C2 gen)

theorem f_uGen (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) :
    f (uGen f) = MonoidAlgebra.of ℤ C2 gen :=
  f.apply_symm_apply _

theorem uGen_mul_uGen (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) : uGen f * uGen f = 1 := by
  rw [uGen, ← map_mul, ← map_mul, gen_mul_gen, map_one, map_one]

theorem counit_uGen (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) :
    Coalgebra.counit (R := ℤ) (uGen f) = 1 := by
  rw [uGen, CoalgHomClass.counit_comp_apply, MonoidAlgebra.of_apply, MonoidAlgebra.counit_single]
  rfl

theorem comul_of_gen :
    Coalgebra.comul (R := ℤ) (MonoidAlgebra.of ℤ C2 gen) =
      MonoidAlgebra.of ℤ C2 gen ⊗ₜ[ℤ] MonoidAlgebra.of ℤ C2 gen := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.comul_single]
  simp

theorem comul_uGen (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) :
    Coalgebra.comul (R := ℤ) (uGen f) = uGen f ⊗ₜ[ℤ] uGen f := by
  rw [uGen, ← CoalgHomClass.map_comp_comul_apply, comul_of_gen, TensorProduct.map_tmul]
  rfl

theorem convMul_apply_uGen (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) {R : Type} [CommRing R]
    (φ ψ : WithConv (K →ₐ[ℤ] R)) :
    (φ * ψ) (uGen f) = φ.ofConv (uGen f) * ψ.ofConv (uGen f) := by
  rw [AlgHom.convMul_apply, comul_uGen]
  simp only [Algebra.TensorProduct.lift_tmul]

theorem convOne_apply_uGen (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) {R : Type} [CommRing R] :
    (1 : WithConv (K →ₐ[ℤ] R)) (uGen f) = 1 := by
  rw [AlgHom.convOne_apply, counit_uGen, map_one]

theorem apply_uGen_mul_self (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) {R : Type} [CommRing R]
    (φ : K →ₐ[ℤ] R) : φ (uGen f) * φ (uGen f) = 1 := by
  rw [← map_mul, uGen_mul_uGen, map_one]

theorem algHom_ext_uGen (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) {R : Type} [CommRing R]
    (φ ψ : K →ₐ[ℤ] R) (h : φ (uGen f) = ψ (uGen f)) : φ = ψ := by
  have key :
      φ.comp ((f.symm : MonoidAlgebra ℤ C2 →ₐc[ℤ] K) : MonoidAlgebra ℤ C2 →ₐ[ℤ] K) =
      ψ.comp ((f.symm : MonoidAlgebra ℤ C2 →ₐc[ℤ] K) : MonoidAlgebra ℤ C2 →ₐ[ℤ] K) := by
    refine MonoidAlgebra.algHom_ext (fun m => ?_) (Algebra.ext_id _ _ _)
    rcases C2_cases m with rfl | rfl
    · rw [← MonoidAlgebra.one_def, map_one, map_one]
    · simp only [AlgHom.comp_apply]
      exact h
  ext k
  have hk := DFunLike.congr_fun key (f k)
  simp only [AlgHom.comp_apply] at hk
  have hs : ((f.symm : MonoidAlgebra ℤ C2 →ₐc[ℤ] K) : MonoidAlgebra ℤ C2 →ₐ[ℤ] K) (f k) = k :=
    f.symm_apply_apply k
  rw [hs] at hk
  exact hk

theorem exists_algHom_apply_uGen (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) {R : Type} [CommRing R]
    (x : R) (hx : x * x = 1) : ∃ φ : K →ₐ[ℤ] R, φ (uGen f) = x := by
  refine ⟨(MonoidAlgebra.lift ℤ R C2 (chi x hx)).comp
    ((f : K →ₐc[ℤ] MonoidAlgebra ℤ C2) : K →ₐ[ℤ] MonoidAlgebra ℤ C2), ?_⟩
  rw [AlgHom.comp_apply]
  have h1 : ((f : K →ₐc[ℤ] MonoidAlgebra ℤ C2) : K →ₐ[ℤ] MonoidAlgebra ℤ C2) (uGen f) =
      MonoidAlgebra.of ℤ C2 gen := f_uGen f
  rw [h1, MonoidAlgebra.lift_of, chi_gen]

theorem exists_pointData (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ C2) :
    ∃ u : K, ∀ (R : Type) [CommRing R],
      (∀ φ ψ : WithConv (K →ₐ[ℤ] R), (φ * ψ) u = φ.ofConv u * ψ.ofConv u) ∧
      (∀ φ : K →ₐ[ℤ] R, φ u * φ u = 1) ∧
      (∀ φ ψ : K →ₐ[ℤ] R, φ u = ψ u → φ = ψ) ∧
      (∀ x : R, x * x = 1 → ∃ φ : K →ₐ[ℤ] R, φ u = x) :=
  ⟨uGen f, fun _ _ => ⟨convMul_apply_uGen f, apply_uGen_mul_self f, algHom_ext_uGen f,
    exists_algHom_apply_uGen f⟩⟩

end Transport

end GroupAlgebraPoints

namespace Assembly

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite CategoryTheory.Limits"
open FppfKummerSES MuTwoGroupAlgebraRepr.KernelSections

def selfInvUnit {M : Type*} [Monoid M] (x : M) (hx : x * x = 1) : Mˣ := ⟨x, x, hx, hx⟩

theorem val_mul_val_of_sq {M : Type*} [Monoid M] (v : Mˣ) (h : v ^ 2 = 1) :
    (v : M) * v = 1 := by
  rw [← Units.val_mul, ← pow_two, h, Units.val_one]

theorem selfInvUnit_sq {M : Type*} [Monoid M] (x : M) (hx : x * x = 1) :
    selfInvUnit x hx ^ 2 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, pow_two]; exact hx)

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K] (u : K)

section Points

variable {R : Type} [CommRing R]
  (hsurj : ∀ x : R, x * x = 1 → ∃ φ : K →ₐ[ℤ] R, φ u = x)

def pt (x : R) (hx : x * x = 1) : K →ₐ[ℤ] R :=
  Classical.choose (hsurj x hx)

theorem pt_apply_u (x : R) (hx : x * x = 1) : pt u hsurj x hx u = x :=
  Classical.choose_spec (hsurj x hx)

end Points

variable (T : Scheme.{0})

section KerPoints

variable (hsq : ∀ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u * φ u = 1)
  (hsurj : ∀ x : Γ(T, ⊤), x * x = 1 → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x)

theorem ker_val_mul_val (t : (((gmPowSelf.{0} 2).hom.app (op T)).hom).ker) :
    ((gmLiftedSectionUnit t.1 : (Γ(T, ⊤))ˣ) : Γ(T, ⊤)) * (gmLiftedSectionUnit t.1 : (Γ(T, ⊤))ˣ)
      = 1 :=
  val_mul_val_of_sq _ ((mem_gmPowSelfApp_ker_iff 2 T t.1).mp t.2)

def kerToPoint (t : (((gmPowSelf.{0} 2).hom.app (op T)).hom).ker) : K →ₐ[ℤ] Γ(T, ⊤) :=
  pt u hsurj _ (ker_val_mul_val T t)

theorem kerToPoint_apply_u (t : (((gmPowSelf.{0} 2).hom.app (op T)).hom).ker) :
    kerToPoint u T hsurj t u = ((gmLiftedSectionUnit t.1 : (Γ(T, ⊤))ˣ) : Γ(T, ⊤)) :=
  pt_apply_u u hsurj _ _

def pointToKer (φ : K →ₐ[ℤ] Γ(T, ⊤)) : (((gmPowSelf.{0} 2).hom.app (op T)).hom).ker :=
  ⟨ULift.up (Additive.ofMul (selfInvUnit (φ u) (hsq φ))),
    (mem_gmPowSelfApp_ker_iff 2 T _).mpr (selfInvUnit_sq _ _)⟩

theorem unit_pointToKer (φ : K →ₐ[ℤ] Γ(T, ⊤)) :
    gmLiftedSectionUnit (pointToKer u T hsq φ).1 = selfInvUnit (φ u) (hsq φ) :=
  rfl

theorem kerToPoint_pointToKer (hinj : ∀ φ ψ : K →ₐ[ℤ] Γ(T, ⊤), φ u = ψ u → φ = ψ)
    (φ : K →ₐ[ℤ] Γ(T, ⊤)) :
    kerToPoint u T hsurj (pointToKer u T hsq φ) = φ :=
  hinj _ _ (by rw [kerToPoint_apply_u, unit_pointToKer]; rfl)

theorem pointToKer_kerToPoint (t : (((gmPowSelf.{0} 2).hom.app (op T)).hom).ker) :
    pointToKer u T hsq (kerToPoint u T hsurj t) = t := by
  apply Subtype.ext
  have h1 : selfInvUnit (kerToPoint u T hsurj t u) (hsq _) = gmLiftedSectionUnit t.1 :=
    Units.ext (kerToPoint_apply_u u T hsurj t)
  exact congrArg (fun v => (ULift.up (Additive.ofMul v) :
    ToType (GmAbelianSheafLifted.{0}.obj.obj (op T)))) h1

end KerPoints

def kerPointsEquiv
    (hmul : ∀ φ ψ : WithConv (K →ₐ[ℤ] Γ(T, ⊤)), (φ * ψ) u = φ.ofConv u * ψ.ofConv u)
    (hsq : ∀ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u * φ u = 1)
    (hinj : ∀ φ ψ : K →ₐ[ℤ] Γ(T, ⊤), φ u = ψ u → φ = ψ)
    (hsurj : ∀ x : Γ(T, ⊤), x * x = 1 → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x) :
    (((gmPowSelf.{0} 2).hom.app (op T)).hom).ker ≃+
      Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))) where
  toFun t := Additive.ofMul (WithConv.toConv (kerToPoint u T hsurj t))
  invFun φ := pointToKer u T hsq (Additive.toMul φ).ofConv
  left_inv t := pointToKer_kerToPoint u T hsq hsurj t
  right_inv φ := by
    change Additive.ofMul (WithConv.toConv
      (kerToPoint u T hsurj (pointToKer u T hsq (Additive.toMul φ).ofConv))) = φ
    rw [kerToPoint_pointToKer u T hsq hsurj hinj]
    rfl
  map_add' t t' := by
    rw [← ofMul_mul]
    apply congrArg Additive.ofMul
    apply WithConv.ext
    change kerToPoint u T hsurj (t + t') =
      (WithConv.toConv (kerToPoint u T hsurj t) * WithConv.toConv (kerToPoint u T hsurj t')).ofConv
    apply hinj
    rw [kerToPoint_apply_u]
    change _ = (WithConv.toConv (kerToPoint u T hsurj t) *
      WithConv.toConv (kerToPoint u T hsurj t')) u
    rw [hmul, WithConv.ofConv_toConv, WithConv.ofConv_toConv, kerToPoint_apply_u,
      kerToPoint_apply_u]
    rfl

def secEquiv
    (hmul : ∀ φ ψ : WithConv (K →ₐ[ℤ] Γ(T, ⊤)), (φ * ψ) u = φ.ofConv u * ψ.ofConv u)
    (hsq : ∀ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u * φ u = 1)
    (hinj : ∀ φ ψ : K →ₐ[ℤ] Γ(T, ⊤), φ u = ψ u → φ = ψ)
    (hsurj : ∀ x : Γ(T, ⊤), x * x = 1 → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x) :
    ToType ((muPAbelianSheafLifted.{0} 2).obj.obj (op T)) ≃+
      Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))) :=
  (secKerEquiv 2 T).trans (kerPointsEquiv u T hmul hsq hinj hsurj)

theorem secEquiv_apply_u
    (hmul : ∀ φ ψ : WithConv (K →ₐ[ℤ] Γ(T, ⊤)), (φ * ψ) u = φ.ofConv u * ψ.ofConv u)
    (hsq : ∀ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u * φ u = 1)
    (hinj : ∀ φ ψ : K →ₐ[ℤ] Γ(T, ⊤), φ u = ψ u → φ = ψ)
    (hsurj : ∀ x : Γ(T, ⊤), x * x = 1 → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x)
    (s : ToType ((muPAbelianSheafLifted.{0} 2).obj.obj (op T))) :
    (Additive.toMul (secEquiv u T hmul hsq hinj hsurj s)).ofConv u =
      ((secUnit 2 T s : (Γ(T, ⊤))ˣ) : Γ(T, ⊤)) := by
  change kerToPoint u T hsurj (secKerEquiv 2 T s) u = _
  rw [kerToPoint_apply_u, secKerEquiv_apply_unit]

variable {T}

theorem secEquiv_naturality {T T' : Scheme.{0}} (g : T ⟶ T')
    (hmul : ∀ φ ψ : WithConv (K →ₐ[ℤ] Γ(T, ⊤)), (φ * ψ) u = φ.ofConv u * ψ.ofConv u)
    (hsq : ∀ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u * φ u = 1)
    (hinj : ∀ φ ψ : K →ₐ[ℤ] Γ(T, ⊤), φ u = ψ u → φ = ψ)
    (hsurj : ∀ x : Γ(T, ⊤), x * x = 1 → ∃ φ : K →ₐ[ℤ] Γ(T, ⊤), φ u = x)
    (hmul' : ∀ φ ψ : WithConv (K →ₐ[ℤ] Γ(T', ⊤)), (φ * ψ) u = φ.ofConv u * ψ.ofConv u)
    (hsq' : ∀ φ : K →ₐ[ℤ] Γ(T', ⊤), φ u * φ u = 1)
    (hinj' : ∀ φ ψ : K →ₐ[ℤ] Γ(T', ⊤), φ u = ψ u → φ = ψ)
    (hsurj' : ∀ x : Γ(T', ⊤), x * x = 1 → ∃ φ : K →ₐ[ℤ] Γ(T', ⊤), φ u = x)
    (s : ToType ((muPAbelianSheafLifted.{0} 2).obj.obj (op T'))) (k : K) :
    (Additive.toMul (secEquiv u T hmul hsq hinj hsurj
        ((muPAbelianSheafLifted.{0} 2).obj.map g.op s))) k =
      (Scheme.Γ.map g.op) ((Additive.toMul (secEquiv u T' hmul' hsq' hinj' hsurj' s)) k) := by
  have key : (Additive.toMul (secEquiv u T hmul hsq hinj hsurj
        ((muPAbelianSheafLifted.{0} 2).obj.map g.op s))).ofConv =
      ((Scheme.Γ.map g.op).hom.toIntAlgHom).comp
        (Additive.toMul (secEquiv u T' hmul' hsq' hinj' hsurj' s)).ofConv := by
    apply hinj
    rw [secEquiv_apply_u u T hmul hsq hinj hsurj, secUnit_map, Units.coe_map]
    change (g.appTop).hom (secUnit 2 T' s : Γ(T', ⊤)) =
      (Scheme.Γ.map g.op).hom ((Additive.toMul (secEquiv u T' hmul' hsq' hinj' hsurj' s)).ofConv u)
    rw [secEquiv_apply_u u T' hmul' hsq' hinj' hsurj']
    rfl
  change (Additive.toMul (secEquiv u T hmul hsq hinj hsurj
      ((muPAbelianSheafLifted.{0} 2).obj.map g.op s))).ofConv k = _
  rw [key]
  rfl

variable (K)

theorem exists_sectionsEquiv_of_pointData
    (H : ∀ (R : Type) [CommRing R],
      (∀ φ ψ : WithConv (K →ₐ[ℤ] R), (φ * ψ) u = φ.ofConv u * ψ.ofConv u) ∧
      (∀ φ : K →ₐ[ℤ] R, φ u * φ u = 1) ∧
      (∀ φ ψ : K →ₐ[ℤ] R, φ u = ψ u → φ = ψ) ∧
      (∀ x : R, x * x = 1 → ∃ φ : K →ₐ[ℤ] R, φ u = x)) :
    ∃ e : ∀ T : Scheme.{0},
      ((FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj.obj (Opposite.op T)) ≃+
        Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))),
      ∀ {T T' : Scheme.{0}} (g : T ⟶ T')
        (s : (FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj.obj (Opposite.op T')) (k : K),
        (Additive.toMul (e T ((FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj.map g.op s))) k
          = (Scheme.Γ.map g.op) ((Additive.toMul (e T' s)) k) := by
  refine ⟨fun T => secEquiv u T (H _).1 (H _).2.1 (H _).2.2.1 (H _).2.2.2, ?_⟩
  intro T T' g s k
  exact secEquiv_naturality u g (H _).1 (H _).2.1 (H _).2.2.1 (H _).2.2.2
    (H _).1 (H _).2.1 (H _).2.2.1 (H _).2.2.2 s k

end Assembly

end MuTwoGroupAlgebraRepr

end

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory in
theorem solution
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod 2))) :
    ∃ e : ∀ T : Scheme.{0},
      ((FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj.obj (Opposite.op T)) ≃+
        Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))),
      ∀ {T T' : Scheme.{0}} (g : T ⟶ T')
        (s : (FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj.obj (Opposite.op T')) (k : K),
        (Additive.toMul (e T ((FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj.map g.op s))) k
          = (Scheme.Γ.map g.op) ((Additive.toMul (e T' s)) k) := by
  obtain ⟨u, H⟩ := MuTwoGroupAlgebraRepr.GroupAlgebraPoints.exists_pointData f
  exact MuTwoGroupAlgebraRepr.Assembly.exists_sectionsEquiv_of_pointData K u H

end S_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two
end P2MW
export P2MW.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two (solution)
