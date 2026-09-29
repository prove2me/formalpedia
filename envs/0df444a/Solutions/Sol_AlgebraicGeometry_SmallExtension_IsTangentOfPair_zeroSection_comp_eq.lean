-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.IsTangentOfPair.zeroSection_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/79414a97-78ac-5e34-8f3e-40c2c72ac57a

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_IsTangentOfPair_zeroSection_comp_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

namespace ZeroSectionAux

open AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

noncomputable def aug : thickening T' V C →ₐ[ResidueField T'] ResidueField T' ⊗[T'] C :=
  Algebra.TensorProduct.lift (R := ResidueField T') (S := ResidueField T')
    (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
    ((Algebra.ofId (ResidueField T') (ResidueField T' ⊗[T'] C)).comp (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V))
    (fun _ _ => Commute.all _ _)

theorem aug_tmul (a : ResidueField T' ⊗[T'] C) (t : TrivSqZeroExt (ResidueField T') V) :
    aug T' V C (a ⊗ₜ t) = a * algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) t.fst := by
  simp [aug, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

theorem zeroSection_eq_specMap_aug :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) =
      Spec.map (CommRingCat.ofHom (aug T' V C).toRingHom) := by
  apply (thickening_isPullback V C).hom_ext
  · rw [SquareZero.zeroSection_fst, thickeningFst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id,
      ← CommRingCat.ofHom_id]
    congr 2
    refine RingHom.ext fun a => ?_
    change a = aug T' V C (a ⊗ₜ 1)
    rw [aug_tmul, TrivSqZeroExt.fst_one, map_one, mul_one]
  · rw [SquareZero.zeroSection_snd, thickeningSnd, reductionBase, SquareZero.basePoint, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun t => ?_
    change algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) t.fst = aug T' V C (1 ⊗ₜ t)
    rw [aug_tmul, one_mul]

variable (I : Ideal T') (ι : V →ₗ[T'] T')

theorem aug_comp_schlessinger (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (ϑ : pairRing I C →+* thickening T' V C) (hϑ : IsSchlessingerMap I V ι C ϑ) :
    (aug T' V C).toRingHom.comp ϑ = (toReduction T' C).comp (pairFst I C) := by

  have hzero : ∀ d ∈ I.map (algebraMap T' C), ∀ hd : ((0 : C), d) ∈ pairRing I C, aug T' V C (ϑ ⟨((0 : C), d), hd⟩) = 0 := by
    intro d hd
    refine Submodule.span_induction (p := fun d _ => ∀ hd : ((0 : C), d) ∈ pairRing I C, aug T' V C (ϑ ⟨((0 : C), d), hd⟩) = 0)
      ?_ ?_ ?_ ?_ hd
    · rintro d ⟨t, ht, rfl⟩ hd
      obtain ⟨v, rfl⟩ : t ∈ LinearMap.range ι := by rw [hιI]; exact ht
      have hd' : ((0 : C), algebraMap T' C (ι v) * 1) ∈ pairRing I C := by rwa [mul_one]
      have : (⟨((0 : C), algebraMap T' C (ι v)), hd⟩ : pairRing I C) = ⟨((0 : C), algebraMap T' C (ι v) * 1), hd'⟩ :=
        Subtype.ext (Prod.ext rfl (mul_one _).symm)
      rw [this, hϑ.2 v 1 hd', aug_tmul, TrivSqZeroExt.fst_inr, map_zero, mul_zero]
    · intro hd
      have : (⟨((0 : C), (0 : C)), hd⟩ : pairRing I C) = 0 := rfl
      rw [this, map_zero, map_zero]
    · intro d₁ d₂ _ _ h₁ h₂ hd
      have hd₁ : ((0 : C), d₁) ∈ pairRing I C := by
        rw [mem_pairRing, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; assumption
      have hd₂ : ((0 : C), d₂) ∈ pairRing I C := by
        rw [mem_pairRing, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; assumption
      have : (⟨((0 : C), d₁ + d₂), hd⟩ : pairRing I C) = ⟨((0 : C), d₁), hd₁⟩ + ⟨((0 : C), d₂), hd₂⟩ :=
        Subtype.ext (by ext <;> simp)
      rw [this, map_add, map_add, h₁ hd₁, h₂ hd₂, add_zero]
    · intro c d _ h hd
      have hdd : ((0 : C), d) ∈ pairRing I C := by
        rw [mem_pairRing, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; assumption
      have hcc : (c, c) ∈ pairRing I C := by rw [mem_pairRing]
      have : (⟨((0 : C), c • d), hd⟩ : pairRing I C) = ⟨(c, c), hcc⟩ * ⟨((0 : C), d), hdd⟩ :=
        Subtype.ext (by ext <;> simp [smul_eq_mul])
      rw [this, map_mul, map_mul, h hdd, mul_zero]
  refine RingHom.ext fun x => ?_
  obtain ⟨⟨a, b⟩, hab⟩ := x
  have hab' : b - a ∈ I.map (algebraMap T' C) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact ((mem_pairRing I C).mp hab).symm
  have haa : (a, a) ∈ pairRing I C := by rw [mem_pairRing]
  have h0 : ((0 : C), b - a) ∈ pairRing I C := by
    rw [mem_pairRing, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact hab'
  have hsplit : (⟨(a, b), hab⟩ : pairRing I C) = ⟨(a, a), haa⟩ + ⟨((0 : C), b - a), h0⟩ :=
    Subtype.ext (by ext <;> simp)
  change aug T' V C (ϑ ⟨(a, b), hab⟩) = toReduction T' C a
  rw [hsplit, map_add, map_add, hϑ.1 a haa, hzero _ hab' h0, add_zero, aug_tmul, TrivSqZeroExt.fst_one, map_one, mul_one]

end ZeroSectionAux

theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y) (w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y)
    (huvw : IsTangentOfPair I V ι C u v w) :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) ≫ w
      = Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u := by
  obtain ⟨ϑ, hϑ, φ, hu, -, rfl⟩ := huvw
  rw [← hu, ZeroSectionAux.zeroSection_eq_specMap_aug, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ZeroSectionAux.aug_comp_schlessinger V C I ι hιI ϑ hϑ]

end S_AlgebraicGeometry_SmallExtension_IsTangentOfPair_zeroSection_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_IsTangentOfPair_zeroSection_comp_eq (solution)
