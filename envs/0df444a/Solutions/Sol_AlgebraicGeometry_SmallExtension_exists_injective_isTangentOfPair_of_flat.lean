-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_injective_isTangentOfPair_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e2127112-4ce5-5b85-b951-15e11d6f0dda

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Theorems.Thm_AlgebraicGeometry_SmallExtension_existsUnique_isTangentOfPair_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentOfPair_comp_of_isTangentOfPair_of_flat
import Theorems.Thm_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension

universe u

namespace P2mWs2I1b

section Thickening

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T'))
  {Yk : Scheme.{u}} (ik : Yk ⟶ Y) (f₀ : Yk ⟶ Spec (CommRingCat.of (ResidueField T')))
  (hk : IsPullback ik f₀ q (Spec.map (CommRingCat.ofHom (residue T'))))
  {Z : Scheme.{u}} (q₁ : Z ⟶ Yk) (q₂ : Z ⟶ SquareZero.spec (ResidueField T') V)
  (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase (ResidueField T') V))
  (C : Type u) [CommRing C] [Algebra T' C]
  (c : Spec (CommRingCat.of C) ⟶ Y) (hc : c ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C)))

theorem isPullback_reduction :
    IsPullback (reductionBase T' C) (Spec.map (CommRingCat.ofHom (toReduction T' C)))
      (Spec.map (CommRingCat.ofHom (residue T'))) (Spec.map (CommRingCat.ofHom (algebraMap T' C))) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct T' (ResidueField T') C)
  have e1 : CommRingCat.ofHom (algebraMap T' (ResidueField T')) = CommRingCat.ofHom (residue T') := rfl
  have e2 : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := T') (A := ResidueField T') (B := C)) =
      CommRingCat.ofHom (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C)) := rfl
  rw [e1, e2] at h
  exact h

include hc in
theorem comm_reduction :
    (Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ c) ≫ q =
      reductionBase T' C ≫ Spec.map (CommRingCat.ofHom (residue T')) := by
  rw [Category.assoc, hc]; exact (isPullback_reduction C).w.symm

noncomputable def chartK : Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)) ⟶ Yk :=
  hk.lift (Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ c) (reductionBase T' C)
    (comm_reduction q C c hc)

@[reassoc (attr := simp)]
theorem chartK_ik : chartK q ik f₀ hk C c hc ≫ ik = Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ c :=
  hk.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem chartK_f₀ : chartK q ik f₀ hk C c hc ≫ f₀ = reductionBase T' C :=
  hk.lift_snd _ _ _

theorem isPullback_chartK :
    IsPullback (chartK q ik f₀ hk C c hc) (Spec.map (CommRingCat.ofHom (toReduction T' C))) ik c := by
  refine IsPullback.of_right ?_ (chartK_ik q ik f₀ hk C c hc) hk.flip
  have h := (isPullback_reduction (T' := T') C)
  rw [← hc, ← chartK_f₀ q ik f₀ hk C c hc] at h
  exact h

noncomputable def chartZ : Spec (CommRingCat.of (thickening T' V C)) ⟶ Z :=
  hZ.lift (thickeningFst T' V C ≫ chartK q ik f₀ hk C c hc) (thickeningSnd T' V C)
    (by rw [Category.assoc, chartK_f₀]; exact (thickening_isPullback V C).w)

@[reassoc (attr := simp)]
theorem chartZ_q₁ : chartZ V q ik f₀ hk q₁ q₂ hZ C c hc ≫ q₁ = thickeningFst T' V C ≫ chartK q ik f₀ hk C c hc :=
  hZ.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem chartZ_q₂ : chartZ V q ik f₀ hk q₁ q₂ hZ C c hc ≫ q₂ = thickeningSnd T' V C :=
  hZ.lift_snd _ _ _

@[reassoc]
theorem chartZ_q₁_ik : chartZ V q ik f₀ hk q₁ q₂ hZ C c hc ≫ q₁ ≫ ik =
    thickeningFst T' V C ≫ Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ c := by
  rw [chartZ_q₁_assoc, chartK_ik]

theorem isPullback_chartZ_q₁ :
    IsPullback (chartZ V q ik f₀ hk q₁ q₂ hZ C c hc) (thickeningFst T' V C) q₁ (chartK q ik f₀ hk C c hc) := by
  refine IsPullback.of_right ?_ (chartZ_q₁ V q ik f₀ hk q₁ q₂ hZ C c hc) hZ.flip
  have h := (thickening_isPullback (T' := T') V C).flip
  rw [← chartZ_q₂ V q ik f₀ hk q₁ q₂ hZ C c hc, ← chartK_f₀ q ik f₀ hk C c hc] at h
  exact h

theorem isPullback_chartZ :
    IsPullback (chartZ V q ik f₀ hk q₁ q₂ hZ C c hc)
      (thickeningFst T' V C ≫ Spec.map (CommRingCat.ofHom (toReduction T' C))) (q₁ ≫ ik) c :=
  (isPullback_chartZ_q₁ V q ik f₀ hk q₁ q₂ hZ C c hc).paste_vert (isPullback_chartK q ik f₀ hk C c hc)

theorem chartZ_unique (cZ : Spec (CommRingCat.of (thickening T' V C)) ⟶ Z)
    (h1 : cZ ≫ q₁ ≫ ik = thickeningFst T' V C ≫ Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ c)
    (h2 : cZ ≫ q₂ = thickeningSnd T' V C) :
    cZ = chartZ V q ik f₀ hk q₁ q₂ hZ C c hc := by
  have e1 : cZ ≫ q₁ ≫ f₀ = thickeningFst T' V C ≫ reductionBase T' C := by
    rw [hZ.w, ← Category.assoc, h2]; exact (thickening_isPullback V C).w.symm
  apply hZ.hom_ext
  · apply hk.hom_ext
    · rw [Category.assoc, h1, Category.assoc, chartZ_q₁_ik]
    · rw [Category.assoc, Category.assoc, e1, chartZ_q₁_assoc, chartK_f₀]
  · rw [h2, chartZ_q₂]

end Thickening

end P2mWs2I1b

namespace P2mWs2I1b

section Naturality

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  {C C' : Type u} [CommRing C] [Algebra T' C] [CommRing C'] [Algebra T' C'] (r : C →ₐ[T'] C')

noncomputable def redMap : ResidueField T' ⊗[T'] C →ₐ[ResidueField T'] ResidueField T' ⊗[T'] C' :=
  Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) r

noncomputable def thMap : thickening T' V C →ₐ[ResidueField T'] thickening T' V C' :=
  Algebra.TensorProduct.map (redMap r) (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V))

theorem redMap_comp_toReduction :
    (redMap r).toRingHom.comp (toReduction T' C) = (toReduction T' C').comp r.toRingHom := by
  refine RingHom.ext fun c => ?_
  simp [redMap, toReduction, Algebra.TensorProduct.includeRight_apply]

theorem thMap_comp_includeLeft :
    (thMap V r).toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom) =
      (Algebra.TensorProduct.includeLeftRingHom).comp (redMap r).toRingHom := by
  refine RingHom.ext fun x => ?_
  simp [thMap, Algebra.TensorProduct.includeLeftRingHom_apply]

omit [Module T' V] [IsScalarTower T' (ResidueField T') V] in
theorem thMap_comp_includeRight :
    (thMap V r).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C)
        (B := TrivSqZeroExt (ResidueField T') V)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C')
        (B := TrivSqZeroExt (ResidueField T') V)).toRingHom := by
  refine RingHom.ext fun t => ?_
  simp [thMap, Algebra.TensorProduct.includeRight_apply]

@[reassoc]
theorem specThMap_thickeningFst :
    Spec.map (CommRingCat.ofHom (thMap V r).toRingHom) ≫ thickeningFst T' V C =
      thickeningFst T' V C' ≫ Spec.map (CommRingCat.ofHom (redMap r).toRingHom) := by
  rw [thickeningFst, thickeningFst, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, thMap_comp_includeLeft]

@[reassoc]
theorem specRedMap_toReduction :
    Spec.map (CommRingCat.ofHom (redMap r).toRingHom) ≫ Spec.map (CommRingCat.ofHom (toReduction T' C)) =
      Spec.map (CommRingCat.ofHom (toReduction T' C')) ≫ Spec.map (CommRingCat.ofHom r.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    redMap_comp_toReduction]

@[reassoc]
theorem specThMap_thickeningSnd :
    Spec.map (CommRingCat.ofHom (thMap V r).toRingHom) ≫ thickeningSnd T' V C = thickeningSnd T' V C' := by
  rw [thickeningSnd, thickeningSnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, thMap_comp_includeRight]

variable {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T'))
  {Yk : Scheme.{u}} (ik : Yk ⟶ Y) (f₀ : Yk ⟶ Spec (CommRingCat.of (ResidueField T')))
  (hk : IsPullback ik f₀ q (Spec.map (CommRingCat.ofHom (residue T'))))
  {Z : Scheme.{u}} (q₁ : Z ⟶ Yk) (q₂ : Z ⟶ SquareZero.spec (ResidueField T') V)
  (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase (ResidueField T') V))
  (c : Spec (CommRingCat.of C) ⟶ Y) (hc : c ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
  (c' : Spec (CommRingCat.of C') ⟶ Y) (hc' : c' ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C')))
  (hcc' : Spec.map (CommRingCat.ofHom r.toRingHom) ≫ c = c')

include hcc' in

theorem chartZ_naturality :
    chartZ V q ik f₀ hk q₁ q₂ hZ C' c' hc' =
      Spec.map (CommRingCat.ofHom (thMap V r).toRingHom) ≫ chartZ V q ik f₀ hk q₁ q₂ hZ C c hc := by
  symm
  apply chartZ_unique
  · rw [Category.assoc, chartZ_q₁_ik, specThMap_thickeningFst_assoc, specRedMap_toReduction_assoc, hcc']
  · rw [Category.assoc, chartZ_q₂, specThMap_thickeningSnd]

end Naturality

end P2mWs2I1b

namespace P2mWs2I1b

section RingFacts

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T') (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

noncomputable def aug : thickening T' V C →ₐ[ResidueField T'] ResidueField T' ⊗[T'] C :=
  Algebra.TensorProduct.lift (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
    ((Algebra.ofId (ResidueField T') (ResidueField T' ⊗[T'] C)).comp
      (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V))
    (fun _ _ => Commute.all _ _)

@[scoped simp] theorem aug_tmul (x : ResidueField T' ⊗[T'] C) (t : TrivSqZeroExt (ResidueField T') V) :
    aug T' V C (x ⊗ₜ t) = t.fst • x := by
  simp [aug, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def, mul_comm]

theorem aug_comp_includeLeft :
    (aug T' V C).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  simp [Algebra.TensorProduct.includeLeftRingHom_apply]

theorem aug_comp_includeRight :
    (aug T' V C).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C)
        (B := TrivSqZeroExt (ResidueField T') V)).toRingHom =
      (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C)).comp
        (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V).toRingHom := by
  refine RingHom.ext fun t => ?_
  simp [Algebra.TensorProduct.includeRight_apply, Algebra.smul_def]

theorem zeroSection_thickening_eq :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
        (thickening_isPullback V C) =
      Spec.map (CommRingCat.ofHom (aug T' V C).toRingHom) := by
  apply (thickening_isPullback V C).hom_ext
  · rw [SquareZero.zeroSection_fst, thickeningFst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      aug_comp_includeLeft, CommRingCat.ofHom_id, Spec.map_id]
  · rw [SquareZero.zeroSection_snd, thickeningSnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      aug_comp_includeRight, reductionBase, SquareZero.basePoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

include hιI in

theorem aug_comp_schlessinger (ϑ : pairRing I C →+* thickening T' V C)
    (hϑ : IsSchlessingerMap I V ι C ϑ) :
    (aug T' V C).toRingHom.comp ϑ = (toReduction T' C).comp (pairFst I C) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨⟨a, b⟩, hab⟩ := x

  have hmem0 : ∀ d : C, d ∈ I.map (algebraMap T' C) → ((0 : C), d) ∈ pairRing I C := fun d hd =>
    (mem_pairRing I C).mpr (by
      show Ideal.Quotient.mk _ (0 : C) = Ideal.Quotient.mk _ d
      rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact hd)

  have haa : (a, a) ∈ pairRing I C := by simp [mem_pairRing]
  have hd : b - a ∈ I.map (algebraMap T' C) := Ideal.Quotient.eq.mp ((mem_pairRing I C).mp hab).symm
  have h0d : ((0 : C), b - a) ∈ pairRing I C := hmem0 _ hd
  have hsplit : (⟨(a, b), hab⟩ : pairRing I C) = ⟨(a, a), haa⟩ + ⟨((0 : C), b - a), h0d⟩ := by
    apply Subtype.ext; simp

  have hkill : ∀ d ∈ I.map (algebraMap T' C), ∀ (h : ((0 : C), d) ∈ pairRing I C),
      aug T' V C (ϑ ⟨((0 : C), d), h⟩) = 0 := by
    intro d hd'
    rw [Ideal.map] at hd'
    refine Submodule.span_induction (p := fun d _ => ∀ (h : ((0 : C), d) ∈ pairRing I C),
      aug T' V C (ϑ ⟨((0 : C), d), h⟩) = 0) ?_ ?_ ?_ ?_ hd'
    · rintro d ⟨t, ht, rfl⟩ h
      have ht' : t ∈ LinearMap.range ι := by rw [hιI]; exact ht
      obtain ⟨v, rfl⟩ := ht'
      have h1 : ((0 : C), algebraMap T' C (ι v) * 1) ∈ pairRing I C := by simpa using h
      have : (⟨((0 : C), algebraMap T' C (ι v)), h⟩ : pairRing I C) = ⟨((0 : C), algebraMap T' C (ι v) * 1), h1⟩ := by
        apply Subtype.ext; simp
      rw [this, hϑ.2 v 1 h1, aug_tmul, TrivSqZeroExt.fst_inr, zero_smul]
    · intro h
      have : (⟨((0 : C), (0 : C)), h⟩ : pairRing I C) = 0 := Subtype.ext rfl
      rw [this, RingHom.map_zero ϑ, map_zero]
    · intro d₁ d₂ hd₁ hd₂ ih₁ ih₂ h
      have h₁ : ((0 : C), d₁) ∈ pairRing I C := hmem0 _ hd₁
      have h₂ : ((0 : C), d₂) ∈ pairRing I C := hmem0 _ hd₂
      have : (⟨((0 : C), d₁ + d₂), h⟩ : pairRing I C) = ⟨((0 : C), d₁), h₁⟩ + ⟨((0 : C), d₂), h₂⟩ := by
        apply Subtype.ext; simp
      rw [this, RingHom.map_add ϑ, map_add, ih₁ h₁, ih₂ h₂, add_zero]
    · intro r d hd₀ ih h
      have h' : ((0 : C), d) ∈ pairRing I C := hmem0 _ hd₀
      have hrr : (r, r) ∈ pairRing I C := by simp [mem_pairRing]
      have : (⟨((0 : C), r • d), h⟩ : pairRing I C) = ⟨(r, r), hrr⟩ * ⟨((0 : C), d), h'⟩ := by
        apply Subtype.ext; simp [smul_eq_mul]
      rw [this, RingHom.map_mul ϑ, map_mul, ih h', mul_zero]
  rw [hsplit]
  change aug T' V C (ϑ (_ + _)) = toReduction T' C (pairFst I C (_ + _))
  rw [RingHom.map_add ϑ, map_add, hϑ.1 a haa, hkill _ hd h0d, add_zero, aug_tmul, TrivSqZeroExt.fst_one,
    one_smul, RingHom.map_add (pairFst I C), pairFst_apply, pairFst_apply]
  simp

noncomputable def diag : C →+* pairRing I C :=
  (RingHom.prod (RingHom.id C) (RingHom.id C)).codRestrict (pairRing I C)
    (fun a => by simp [mem_pairRing])

theorem pairFst_comp_diag : (pairFst I C).comp (diag I C) = RingHom.id C := RingHom.ext fun _ => rfl
theorem pairSnd_comp_diag : (pairSnd I C).comp (diag I C) = RingHom.id C := RingHom.ext fun _ => rfl

theorem schlessinger_comp_diag (ϑ : pairRing I C →+* thickening T' V C) (hϑ : IsSchlessingerMap I V ι C ϑ) :
    ϑ.comp (diag I C) = (Algebra.TensorProduct.includeLeftRingHom).comp (toReduction T' C) := by
  refine RingHom.ext fun a => ?_
  have haa : (a, a) ∈ pairRing I C := by simp [mem_pairRing]
  have : diag I C a = ⟨(a, a), haa⟩ := rfl
  rw [RingHom.comp_apply, this, hϑ.1 a haa]
  rfl

end RingFacts

section PairFacts

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T') (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
  (C : Type u) [CommRing C] [Algebra T' C] {A : Scheme.{u}}

include hιI in

theorem IsTangentOfPair.zeroSection_comp {u v : Spec (CommRingCat.of C) ⟶ A}
    {w : Spec (CommRingCat.of (thickening T' V C)) ⟶ A} (h : IsTangentOfPair I V ι C u v w) :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
        (thickening_isPullback V C) ≫ w =
      Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u := by
  obtain ⟨ϑ, hϑ, φ, hu, hv, rfl⟩ := h
  rw [zeroSection_thickening_eq, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    aug_comp_schlessinger I V ι hιI C ϑ hϑ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hu]

theorem IsTangentOfPair.const (ϑ : pairRing I C →+* thickening T' V C) (hϑ : IsSchlessingerMap I V ι C ϑ)
    (x : Spec (CommRingCat.of C) ⟶ A) :
    IsTangentOfPair I V ι C x x
      (thickeningFst T' V C ≫ Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ x) := by
  refine ⟨ϑ, hϑ, Spec.map (CommRingCat.ofHom (diag I C)) ≫ x, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pairFst_comp_diag,
      CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pairSnd_comp_diag,
      CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  · conv_rhs => rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      schlessinger_comp_diag I V ι C ϑ hϑ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

namespace IsTangentOfPair

private theorem _root_.P2mWs2I1b.IsTangentOfPair.comp {u v : Spec (CommRingCat.of C) ⟶ A}
    {w : Spec (CommRingCat.of (thickening T' V C)) ⟶ A} (h : IsTangentOfPair I V ι C u v w)
    {A' : Scheme.{u}} (g : A ⟶ A') : IsTangentOfPair I V ι C (u ≫ g) (v ≫ g) (w ≫ g) := by
  obtain ⟨ϑ, hϑ, φ, hu, hv, rfl⟩ := h
  exact ⟨ϑ, hϑ, φ ≫ g, by rw [← Category.assoc, hu], by rw [← Category.assoc, hv],
    by rw [Category.assoc]⟩

end IsTangentOfPair
p2m_export "P2mWs2I1b" "IsTangentOfPair.comp"
end PairFacts

end P2mWs2I1b
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.P2mWs2I1b"

namespace P2mWs2I1b

section Charts

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T'))

noncomputable def resHom (U : Y.Opens) : CommRingCat.of T' ⟶ Γ(Y, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ q.appTop ≫ Y.presheaf.map (homOfLE le_top).op

theorem resHom_res {U U' : Y.Opens} (h : U ≤ U') :
    resHom q U' ≫ Y.presheaf.map (homOfLE h).op = resHom q U := by
  simp only [resHom, Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem fromSpec_comp_eq {U : Y.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (resHom q U) := by
  calc hU.fromSpec ≫ q
      = hU.fromSpec ≫ q ≫ (Spec (CommRingCat.of T')).toSpecΓ ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of T')).inv := by
        rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = Spec.map (resHom q U) := by
        rw [Scheme.toSpecΓ_naturality_assoc, hU.fromSpec_toSpecΓ_assoc, resHom]
        simp only [Spec.map_comp, Category.assoc]

@[reducible] noncomputable def algOfOpen (U : Y.Opens) : Algebra T' Γ(Y, U) :=
  (resHom q U).hom.toAlgebra

theorem specOver {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := algOfOpen q U
    hU.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))) :=
  fromSpec_comp_eq q hU

theorem flat_algOfOpen [Flat q] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := algOfOpen q U
    Module.Flat T' Γ(Y, U) := by
  have : Flat (Spec.map (resHom q U)) := by rw [← fromSpec_comp_eq q hU]; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this

noncomputable def resAlg {U U' : Y.Opens} (h : U ≤ U') :
    letI := algOfOpen q U; letI := algOfOpen q U'
    Γ(Y, U') →ₐ[T'] Γ(Y, U) :=
  letI := algOfOpen q U; letI := algOfOpen q U'
  { (Y.presheaf.map (homOfLE h).op).hom with
    commutes' := fun r => by
      change (resHom q U' ≫ Y.presheaf.map (homOfLE h).op).hom r = (resHom q U).hom r
      rw [resHom_res] }

theorem spec_resAlg {U U' : Y.Opens} (h : U ≤ U') :
    letI := algOfOpen q U; letI := algOfOpen q U'
    Spec.map (CommRingCat.ofHom (resAlg q h).toRingHom) = Spec.map (Y.presheaf.map (homOfLE h).op) := rfl

theorem spec_resAlg_fromSpec {U U' : Y.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    letI := algOfOpen q U; letI := algOfOpen q U'
    Spec.map (CommRingCat.ofHom (resAlg q h).toRingHom) ≫ hU'.fromSpec = hU.fromSpec := by
  rw [spec_resAlg]; exact IsAffineOpen.map_fromSpec hU' hU (homOfLE h).op

end Charts
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.P2mWs2I1b"

section Local

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
  (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
  {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T'))
  {Y₀ : Scheme.{u}} (i₀ : Y₀ ⟶ Y) (q₀ : Y₀ ⟶ Spec (CommRingCat.of (T' ⧸ I)))
  (h₀ : IsPullback i₀ q₀ q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
  {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q)
  (v : Y ⟶ A) (hv : v ≫ pA = q) (huv : i₀ ≫ v = i₀ ≫ u)
  (C : Type u) [CommRing C] [Algebra T' C]
  (c : Spec (CommRingCat.of C) ⟶ Y) (hc : c ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C)))

include h₀ hc huv in

theorem agree_mod :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ c ≫ u =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ c ≫ v := by
  have hle : I ≤ (I.map (algebraMap T' C)).comap (algebraMap T' C) := Ideal.le_comap_map
  have hsq : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ c) ≫ q =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map (algebraMap T' C)) (algebraMap T' C) hle)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [Category.assoc, hc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
  have e := h₀.lift_fst _ _ hsq
  simp only [← Category.assoc]
  rw [← e]
  simp only [Category.assoc, huv]

variable [Module.Flat T' C]

include hI hsmall hι hιI h₀ hu hv huv hc

theorem existsUnique_locField : ∃! w : Spec (CommRingCat.of (thickening T' V C)) ⟶ A,
    IsTangentOfPair I V ι C (c ≫ u) (c ≫ v) w :=
  AlgebraicGeometry.SmallExtension.existsUnique_isTangentOfPair_of_flat I hI hsmall V ι hι hιI C pA
    (c ≫ u) (by rw [Category.assoc, hu, hc]) (c ≫ v) (by rw [Category.assoc, hv, hc])
    (agree_mod I q i₀ q₀ h₀ u v huv C c hc)

noncomputable def locField : Spec (CommRingCat.of (thickening T' V C)) ⟶ A :=
  (existsUnique_locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc).exists.choose

theorem locField_spec : IsTangentOfPair I V ι C (c ≫ u) (c ≫ v)
    (locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc) :=
  (existsUnique_locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc).exists.choose_spec

theorem locField_unique {w : Spec (CommRingCat.of (thickening T' V C)) ⟶ A}
    (hw : IsTangentOfPair I V ι C (c ≫ u) (c ≫ v) w) :
    w = locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc :=
  (existsUnique_locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc).unique hw
    (locField_spec I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc)

theorem locField_nat (C' : Type u) [CommRing C'] [Algebra T' C'] [Module.Flat T' C'] (r : C →ₐ[T'] C')
    (c' : Spec (CommRingCat.of C') ⟶ Y) (hc' : c' ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C')))
    (hcc' : Spec.map (CommRingCat.ofHom r.toRingHom) ≫ c = c') :
    locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C' c' hc' =
      Spec.map (CommRingCat.ofHom (thMap V r).toRingHom) ≫
        locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc := by
  symm
  apply locField_unique
  have h := AlgebraicGeometry.SmallExtension.isTangentOfPair_comp_of_isTangentOfPair_of_flat I hI hsmall V ι hι hιI
    C C' r (c ≫ u) (c ≫ v) _ (locField_spec I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc)
  rw [← Category.assoc, ← Category.assoc, hcc'] at h
  exact h

theorem zeroSection_locField :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
        (thickening_isPullback V C) ≫ locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc =
      Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ c ≫ u :=
  IsTangentOfPair.zeroSection_comp I V ι hιI C (locField_spec I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc)

end Local
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.P2mWs2I1b"

end P2mWs2I1b
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.P2mWs2I1b"

namespace P2mWs2I1b

section Glue

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
  (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
  {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [Flat q]
  {Y₀ : Scheme.{u}} (i₀ : Y₀ ⟶ Y) (q₀ : Y₀ ⟶ Spec (CommRingCat.of (T' ⧸ I)))
  (h₀ : IsPullback i₀ q₀ q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
  {Yk : Scheme.{u}} (ik : Yk ⟶ Y) (f₀ : Yk ⟶ Spec (CommRingCat.of (ResidueField T')))
  (hk : IsPullback ik f₀ q (Spec.map (CommRingCat.ofHom (residue T'))))
  {Z : Scheme.{u}} (q₁ : Z ⟶ Yk) (q₂ : Z ⟶ SquareZero.spec (ResidueField T') V)
  (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase (ResidueField T') V))
  {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q)
  (v : Y ⟶ A) (hv : v ≫ pA = q) (huv : i₀ ≫ v = i₀ ≫ u)

noncomputable def chZ (U : Y.affineOpens) :
    letI := algOfOpen q U.1
    Spec (CommRingCat.of (thickening T' V Γ(Y, U.1))) ⟶ Z :=
  letI := algOfOpen q U.1
  chartZ V q ik f₀ hk q₁ q₂ hZ Γ(Y, U.1) U.2.fromSpec (specOver q U.2)

noncomputable def chE (U : Y.affineOpens) :
    letI := algOfOpen q U.1
    Spec (CommRingCat.of (thickening T' V Γ(Y, U.1))) ⟶ (U.1 : Scheme.{u}) :=
  letI := algOfOpen q U.1
  (thickeningFst T' V Γ(Y, U.1) ≫ Spec.map (CommRingCat.ofHom (toReduction T' Γ(Y, U.1)))) ≫ U.2.isoSpec.inv

theorem isPullback_chZ (U : Y.affineOpens) :
    IsPullback (chZ V q ik f₀ hk q₁ q₂ hZ U) (chE V q U) (q₁ ≫ ik) U.1.ι := by
  letI := algOfOpen q U.1
  have h := isPullback_chartZ V q ik f₀ hk q₁ q₂ hZ Γ(Y, U.1) U.2.fromSpec (specOver q U.2)
  exact h.of_iso (Iso.refl _) (Iso.refl _) U.2.isoSpec.symm (Iso.refl _) (by simp [chZ]) (by simp [chE])
    (by simp) (by simp [IsAffineOpen.isoSpec_inv_ι])

noncomputable def chIso (U : Y.affineOpens) :
    letI := algOfOpen q U.1
    Spec (CommRingCat.of (thickening T' V Γ(Y, U.1))) ≅ pullback (q₁ ≫ ik) U.1.ι :=
  (isPullback_chZ V q ik f₀ hk q₁ q₂ hZ U).isoPullback

@[reassoc (attr := simp)]
theorem chIso_hom_fst (U : Y.affineOpens) :
    (chIso V q ik f₀ hk q₁ q₂ hZ U).hom ≫ pullback.fst (q₁ ≫ ik) U.1.ι = chZ V q ik f₀ hk q₁ q₂ hZ U :=
  (isPullback_chZ V q ik f₀ hk q₁ q₂ hZ U).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem chIso_inv_chZ (U : Y.affineOpens) :
    (chIso V q ik f₀ hk q₁ q₂ hZ U).inv ≫ chZ V q ik f₀ hk q₁ q₂ hZ U = pullback.fst (q₁ ≫ ik) U.1.ι :=
  (isPullback_chZ V q ik f₀ hk q₁ q₂ hZ U).isoPullback_inv_fst

include hI hsmall hι hιI h₀ hu hv huv

noncomputable def chField (U : Y.affineOpens) :
    letI := algOfOpen q U.1
    Spec (CommRingCat.of (thickening T' V Γ(Y, U.1))) ⟶ A :=
  letI := algOfOpen q U.1
  haveI := flat_algOfOpen q U.2
  locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv Γ(Y, U.1) U.2.fromSpec (specOver q U.2)

theorem chField_res {U U' : Y.affineOpens} (h : U ≤ U') :
    letI := algOfOpen q U.1; letI := algOfOpen q U'.1
    Spec.map (CommRingCat.ofHom (thMap V (resAlg q h)).toRingHom) ≫
        chField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv U' =
      chField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv U := by
  letI := algOfOpen q U.1; letI := algOfOpen q U'.1
  haveI := flat_algOfOpen q U.2; haveI := flat_algOfOpen q U'.2
  exact (locField_nat I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv Γ(Y, U'.1) U'.2.fromSpec
    (specOver q U'.2) Γ(Y, U.1) (resAlg q h) U.2.fromSpec (specOver q U.2)
    (spec_resAlg_fromSpec q U.2 U'.2 h)).symm

omit hI hsmall hι hιI h₀ hu hv huv in

theorem chZ_res {U U' : Y.affineOpens} (h : U ≤ U') :
    letI := algOfOpen q U.1; letI := algOfOpen q U'.1
    Spec.map (CommRingCat.ofHom (thMap V (resAlg q h)).toRingHom) ≫ chZ V q ik f₀ hk q₁ q₂ hZ U' =
      chZ V q ik f₀ hk q₁ q₂ hZ U := by
  letI := algOfOpen q U.1; letI := algOfOpen q U'.1
  exact (chartZ_naturality V (resAlg q h) q ik f₀ hk q₁ q₂ hZ U'.2.fromSpec (specOver q U'.2)
    U.2.fromSpec (specOver q U.2) (spec_resAlg_fromSpec q U.2 U'.2 h)).symm

noncomputable def gfam (U : Y.affineOpens) : pullback (q₁ ≫ ik) U.1.ι ⟶ A :=
  (chIso V q ik f₀ hk q₁ q₂ hZ U).inv ≫ chField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv U

omit hI hsmall hι hιI h₀ hu hv huv in

noncomputable def trV {U U' : Y.affineOpens} (h : U ≤ U') :
    pullback (q₁ ≫ ik) U.1.ι ⟶ pullback (q₁ ≫ ik) U'.1.ι :=
  Scheme.Cover.trans (Y.directedAffineCover.pullback₁ (q₁ ≫ ik)) (homOfLE h : (U : Y.directedAffineCover.I₀) ⟶ U')

omit hI hsmall hι hιI h₀ hu hv huv in
@[reassoc]
theorem trV_fst {U U' : Y.affineOpens} (h : U ≤ U') :
    trV ik q₁ h ≫ pullback.fst (q₁ ≫ ik) U'.1.ι = pullback.fst (q₁ ≫ ik) U.1.ι :=
  Scheme.Cover.trans_map (Y.directedAffineCover.pullback₁ (q₁ ≫ ik)) _

omit hI hsmall hι hιI h₀ hu hv huv in

theorem chIso_trans {U U' : Y.affineOpens} (h : U ≤ U') :
    letI := algOfOpen q U.1; letI := algOfOpen q U'.1
    (chIso V q ik f₀ hk q₁ q₂ hZ U).hom ≫ trV ik q₁ h =
      Spec.map (CommRingCat.ofHom (thMap V (resAlg q h)).toRingHom) ≫ (chIso V q ik f₀ hk q₁ q₂ hZ U').hom := by
  letI := algOfOpen q U.1; letI := algOfOpen q U'.1
  have hfst : ((chIso V q ik f₀ hk q₁ q₂ hZ U).hom ≫ trV ik q₁ h) ≫ pullback.fst (q₁ ≫ ik) U'.1.ι =
      (Spec.map (CommRingCat.ofHom (thMap V (resAlg q h)).toRingHom) ≫ (chIso V q ik f₀ hk q₁ q₂ hZ U').hom) ≫
        pullback.fst (q₁ ≫ ik) U'.1.ι := by
    rw [Category.assoc, Category.assoc, chIso_hom_fst, chZ_res, trV_fst, chIso_hom_fst]
  apply pullback.hom_ext
  · exact hfst
  · rw [← cancel_mono U'.1.ι]
    simp only [Category.assoc, ← pullback.condition]
    simpa only [Category.assoc] using congrArg (· ≫ (q₁ ≫ ik)) hfst

theorem gfam_compat {U U' : Y.affineOpens} (h : U ≤ U') :
    trV ik q₁ h ≫ gfam I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv U' =
      gfam I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv U := by
  rw [← cancel_epi (chIso V q ik f₀ hk q₁ q₂ hZ U).hom, ← Category.assoc, chIso_trans V q ik f₀ hk q₁ q₂ hZ h,
    gfam, gfam]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, chField_res I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv h]

theorem gfam_compat' : ∀ {U U' : (Y.directedAffineCover.pullback₁ (q₁ ≫ ik)).I₀} (hij : U ⟶ U'),
    Scheme.Cover.trans (Y.directedAffineCover.pullback₁ (q₁ ≫ ik)) hij ≫
      gfam I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv U' =
      gfam I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv U :=
  fun {U U'} hij => gfam_compat I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv
    (leOfHom (hij : (U : Y.directedAffineCover.I₀) ⟶ U'))

noncomputable def glued : Z ⟶ A :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected (Y.directedAffineCover.pullback₁ (q₁ ≫ ik))
    (fun U => gfam I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv U)
    (gfam_compat' I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv)

theorem fst_glued (U : Y.affineOpens) :
    pullback.fst (q₁ ≫ ik) U.1.ι ≫ glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv =
      gfam I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv U :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (Y.directedAffineCover.pullback₁ (q₁ ≫ ik)) _
    (gfam_compat' I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv) U

theorem chZ_glued (U : Y.affineOpens) :
    chZ V q ik f₀ hk q₁ q₂ hZ U ≫ glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv =
      chField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv U := by
  rw [← chIso_hom_fst V q ik f₀ hk q₁ q₂ hZ U, Category.assoc, fst_glued, gfam, Iso.hom_inv_id_assoc]

end Glue
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.P2mWs2I1b"

end P2mWs2I1b
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.P2mWs2I1b"

namespace P2mWs2I1b

section Local2

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
  (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
  {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T'))
  {Y₀ : Scheme.{u}} (i₀ : Y₀ ⟶ Y) (q₀ : Y₀ ⟶ Spec (CommRingCat.of (T' ⧸ I)))
  (h₀ : IsPullback i₀ q₀ q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
  {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q)
  (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
  (c : Spec (CommRingCat.of C) ⟶ Y) (hc : c ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C)))

include hI hsmall hι hιI h₀ hu hc

theorem locField_self :
    locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu u hu rfl C c hc =
      thickeningFst T' V C ≫ Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ c ≫ u := by
  obtain ⟨ϑ, hϑ, -⟩ := locField_spec I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu u hu rfl C c hc
  exact (locField_unique I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu u hu rfl C c hc
    (IsTangentOfPair.const I V ι C ϑ hϑ (c ≫ u))).symm

theorem locField_comp_target (v : Y ⟶ A) (hv : v ≫ pA = q) (huv : i₀ ≫ v = i₀ ≫ u)
    {A' : Scheme.{u}} (pA' : A' ⟶ Spec (CommRingCat.of T')) (g : A ⟶ A')
    (hu' : (u ≫ g) ≫ pA' = q) (hv' : (v ≫ g) ≫ pA' = q) (huv' : i₀ ≫ v ≫ g = i₀ ≫ u ≫ g) :
    locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA' (u ≫ g) hu' (v ≫ g) hv' huv' C c hc =
      locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc ≫ g := by
  symm
  apply locField_unique
  have h := IsTangentOfPair.comp I V ι C (locField_spec I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc) g
  simpa only [Category.assoc] using h

omit hι hιI h₀ hu hc in
omit [Module.Flat T' C] [IsArtinianRing T'] in

theorem isPushout_pair :
    IsPushout (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))))
      (Spec.map (CommRingCat.ofHom (pairFst I C))) (Spec.map (CommRingCat.ofHom (pairSnd I C))) := by
  have H : IsPullback (CommRingCat.ofHom (pairFst I C)) (CommRingCat.ofHom (pairSnd I C))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C))))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) :=
    IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C))))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))))
  refine AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent H
    Ideal.Quotient.mk_surjective ?_
  intro x hx
  have hx' : x ∈ I.map (algebraMap T' C) := by
    simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
  have hII : I * I = ⊥ := le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)
  refine ⟨2, ?_⟩
  have : x * x ∈ I.map (algebraMap T' C) * I.map (algebraMap T' C) := Ideal.mul_mem_mul hx' hx'
  rw [← Ideal.map_mul, hII, Ideal.map_bot] at this
  simpa [pow_two] using this

theorem locField_over (v : Y ⟶ A) (hv : v ≫ pA = q) (huv : i₀ ≫ v = i₀ ≫ u) :
    locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc ≫ pA =
      Spec.map (CommRingCat.ofHom (algebraMap T' (thickening T' V C))) := by
  obtain ⟨ϑ, hϑ, φ, h1, h2, h3⟩ := locField_spec I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc
  rw [h3, Category.assoc]
  have hφ : φ ≫ pA = Spec.map (CommRingCat.ofHom ((diag I C).comp (algebraMap T' C))) := by
    apply (isPushout_pair I hI hsmall C).hom_ext
    · rw [← Category.assoc, h1, Category.assoc, hu, hc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← RingHom.comp_assoc, pairFst_comp_diag, RingHom.id_comp]
    · rw [← Category.assoc, h2, Category.assoc, hv, hc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← RingHom.comp_assoc, pairSnd_comp_diag, RingHom.id_comp]
  rw [hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun t => ?_
  change ϑ (diag I C (algebraMap T' C t)) = algebraMap T' (thickening T' V C) t
  rw [← RingHom.comp_apply, schlessinger_comp_diag I V ι C ϑ hϑ, RingHom.comp_apply, toReduction,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

end Local2
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.P2mWs2I1b"

section Props

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
  (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
  {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [Flat q]
  {Y₀ : Scheme.{u}} (i₀ : Y₀ ⟶ Y) (q₀ : Y₀ ⟶ Spec (CommRingCat.of (T' ⧸ I)))
  (h₀ : IsPullback i₀ q₀ q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
  {Yk : Scheme.{u}} (ik : Yk ⟶ Y) (f₀ : Yk ⟶ Spec (CommRingCat.of (ResidueField T')))
  (hk : IsPullback ik f₀ q (Spec.map (CommRingCat.ofHom (residue T'))))
  {Z : Scheme.{u}} (q₁ : Z ⟶ Yk) (q₂ : Z ⟶ SquareZero.spec (ResidueField T') V)
  (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase (ResidueField T') V))
  {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q)

theorem isPullback_chK (U : Y.affineOpens) :
    letI := algOfOpen q U.1
    IsPullback (chartK q ik f₀ hk Γ(Y, U.1) U.2.fromSpec (specOver q U.2))
      (Spec.map (CommRingCat.ofHom (toReduction T' Γ(Y, U.1))) ≫ U.2.isoSpec.inv) ik U.1.ι := by
  letI := algOfOpen q U.1
  have h := isPullback_chartK q ik f₀ hk Γ(Y, U.1) U.2.fromSpec (specOver q U.2)
  exact h.of_iso (Iso.refl _) (Iso.refl _) U.2.isoSpec.symm (Iso.refl _) (by simp) (by simp)
    (by simp) (by simp [IsAffineOpen.isoSpec_inv_ι])

omit [IsArtinianRing T'] [Flat q] in

@[reassoc]
theorem chartK_zeroSection (C : Type u) [CommRing C] [Algebra T' C]
    (c : Spec (CommRingCat.of C) ⟶ Y) (hc : c ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C))) :
    chartK q ik f₀ hk C c hc ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ =
      SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
        (thickening_isPullback V C) ≫ chartZ V q ik f₀ hk q₁ q₂ hZ C c hc := by
  apply hZ.hom_ext
  · rw [Category.assoc, SquareZero.zeroSection_fst, Category.comp_id, Category.assoc, chartZ_q₁,
      SquareZero.zeroSection_fst_assoc]
  · rw [Category.assoc, SquareZero.zeroSection_snd, chartK_f₀_assoc, Category.assoc, chartZ_q₂,
      SquareZero.zeroSection_snd]

include hI hsmall hι hιI h₀ hu

theorem zeroSection_glued (v : Y ⟶ A) (hv : v ≫ pA = q) (huv : i₀ ≫ v = i₀ ≫ u) :
    SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv =
      ik ≫ u := by
  apply Scheme.Cover.hom_ext (Y.directedAffineCover.pullback₁ ik)
  intro U
  change pullback.fst ik U.1.ι ≫ _ = pullback.fst ik U.1.ι ≫ _
  letI := algOfOpen q U.1
  haveI := flat_algOfOpen q U.2
  have hK := isPullback_chK q ik f₀ hk U
  rw [← cancel_epi hK.isoPullback.hom, hK.isoPullback_hom_fst_assoc, hK.isoPullback_hom_fst_assoc,
    chartK_zeroSection_assoc, chartK_ik_assoc]
  change _ ≫ chZ V q ik f₀ hk q₁ q₂ hZ U ≫ _ = _
  rw [chZ_glued]
  exact zeroSection_locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv Γ(Y, U.1) U.2.fromSpec (specOver q U.2)

theorem glued_self :
    glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu u hu rfl = q₁ ≫ ik ≫ u := by
  apply Scheme.Cover.hom_ext (Y.directedAffineCover.pullback₁ (q₁ ≫ ik))
  intro U
  change pullback.fst (q₁ ≫ ik) U.1.ι ≫ _ = pullback.fst (q₁ ≫ ik) U.1.ι ≫ _
  letI := algOfOpen q U.1
  haveI := flat_algOfOpen q U.2
  rw [fst_glued, gfam, ← chIso_inv_chZ_assoc V q ik f₀ hk q₁ q₂ hZ U]
  congr 1
  change locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu u hu rfl Γ(Y, U.1) U.2.fromSpec (specOver q U.2) =
    chartZ V q ik f₀ hk q₁ q₂ hZ Γ(Y, U.1) U.2.fromSpec (specOver q U.2) ≫ q₁ ≫ ik ≫ u
  rw [locField_self, chartZ_q₁_ik_assoc]

theorem glued_comp_target (v : Y ⟶ A) (hv : v ≫ pA = q) (huv : i₀ ≫ v = i₀ ≫ u)
    {A' : Scheme.{u}} (pA' : A' ⟶ Spec (CommRingCat.of T')) (g : A ⟶ A')
    (hu' : (u ≫ g) ≫ pA' = q) (hv' : (v ≫ g) ≫ pA' = q) (huv' : i₀ ≫ v ≫ g = i₀ ≫ u ≫ g) :
    glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA' (u ≫ g) hu' (v ≫ g) hv' huv' =
      glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv ≫ g := by
  apply Scheme.Cover.hom_ext (Y.directedAffineCover.pullback₁ (q₁ ≫ ik))
  intro U
  change pullback.fst (q₁ ≫ ik) U.1.ι ≫ _ = pullback.fst (q₁ ≫ ik) U.1.ι ≫ _
  letI := algOfOpen q U.1
  haveI := flat_algOfOpen q U.2
  rw [fst_glued, gfam, ← Category.assoc, fst_glued, gfam, Category.assoc]
  congr 1
  exact locField_comp_target I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu Γ(Y, U.1) U.2.fromSpec (specOver q U.2)
    v hv huv pA' g hu' hv' huv'

theorem glued_injective (v₁ : Y ⟶ A) (hv₁ : v₁ ≫ pA = q) (huv₁ : i₀ ≫ v₁ = i₀ ≫ u)
    (v₂ : Y ⟶ A) (hv₂ : v₂ ≫ pA = q) (huv₂ : i₀ ≫ v₂ = i₀ ≫ u)
    (h : glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v₁ hv₁ huv₁ =
      glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v₂ hv₂ huv₂) :
    v₁ = v₂ := by
  apply Scheme.Cover.hom_ext Y.directedAffineCover
  intro U
  change U.1.ι ≫ v₁ = U.1.ι ≫ v₂
  letI := algOfOpen q U.1
  haveI := flat_algOfOpen q U.2
  rw [← cancel_epi U.2.isoSpec.inv, IsAffineOpen.isoSpec_inv_ι_assoc, IsAffineOpen.isoSpec_inv_ι_assoc]
  have e : locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v₁ hv₁ huv₁ Γ(Y, U.1) U.2.fromSpec (specOver q U.2) =
      locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v₂ hv₂ huv₂ Γ(Y, U.1) U.2.fromSpec (specOver q U.2) := by
    have h1 := chZ_glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v₁ hv₁ huv₁ U
    have h2 := chZ_glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v₂ hv₂ huv₂ U
    rw [h] at h1
    exact h1.symm.trans h2
  have H := AlgebraicGeometry.SmallExtension.existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq
    I hI hsmall V ι hι hιI Γ(Y, U.1) pA (U.2.fromSpec ≫ u) (by rw [Category.assoc, hu, specOver q U.2]) _
    (zeroSection_locField I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v₁ hv₁ huv₁ Γ(Y, U.1) U.2.fromSpec (specOver q U.2))
    (locField_over I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu Γ(Y, U.1) U.2.fromSpec (specOver q U.2) v₁ hv₁ huv₁)
  refine H.unique ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_⟩
  · rw [Category.assoc, hv₁, specOver q U.2]
  · exact agree_mod I q i₀ q₀ h₀ u v₁ huv₁ Γ(Y, U.1) U.2.fromSpec (specOver q U.2)
  · exact locField_spec I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v₁ hv₁ huv₁ Γ(Y, U.1) U.2.fromSpec (specOver q U.2)
  · rw [Category.assoc, hv₂, specOver q U.2]
  · exact agree_mod I q i₀ q₀ h₀ u v₂ huv₂ Γ(Y, U.1) U.2.fromSpec (specOver q U.2)
  · rw [e]
    exact locField_spec I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v₂ hv₂ huv₂ Γ(Y, U.1) U.2.fromSpec (specOver q U.2)

theorem glued_isTangentOfPair (v : Y ⟶ A) (hv : v ≫ pA = q) (huv : i₀ ≫ v = i₀ ≫ u)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    (c : Spec (CommRingCat.of C) ⟶ Y) (hc : c ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hcU : ∃ U : Y.Opens, IsAffineOpen U ∧ Set.range c.base ⊆ (U : Set Y))
    (cZ : Spec (CommRingCat.of (thickening T' V C)) ⟶ Z)
    (h1 : cZ ≫ q₁ ≫ ik = thickeningFst T' V C ≫ Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ c)
    (h2 : cZ ≫ q₂ = thickeningSnd T' V C) :
    IsTangentOfPair I V ι C (c ≫ u) (c ≫ v)
      (cZ ≫ glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v hv huv) := by
  obtain ⟨U, hU, hsub⟩ := hcU
  let W : Y.affineOpens := ⟨U, hU⟩
  have hrange : Set.range c.base ⊆ Set.range W.1.ι.base := by rwa [Scheme.Opens.range_ι]
  let c₁ : Spec (CommRingCat.of C) ⟶ (W.1 : Scheme.{u}) := IsOpenImmersion.lift W.1.ι c hrange
  have hc₁ : c₁ ≫ W.1.ι = c := IsOpenImmersion.lift_fac _ _ _
  letI := algOfOpen q W.1
  haveI := flat_algOfOpen q W.2
  let χ : Γ(Y, W.1) ⟶ CommRingCat.of C := Spec.preimage (c₁ ≫ W.2.isoSpec.hom)
  have hχ : Spec.map χ = c₁ ≫ W.2.isoSpec.hom := Spec.map_preimage _
  have hχc : Spec.map χ ≫ W.2.fromSpec = c := by
    rw [hχ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hc₁]
  have hχalg : resHom q W.1 ≫ χ = CommRingCat.ofHom (algebraMap T' C) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← fromSpec_comp_eq q W.2, ← Category.assoc, hχc, hc]
  let r : Γ(Y, W.1) →ₐ[T'] C :=
    { χ.hom with
      commutes' := fun t => by
        change (resHom q W.1 ≫ χ).hom t = algebraMap T' C t
        rw [hχalg]; rfl }
  have hr : Spec.map (CommRingCat.ofHom r.toRingHom) ≫ W.2.fromSpec = c := hχc
  have hcZ : cZ = Spec.map (CommRingCat.ofHom (thMap V r).toRingHom) ≫ chZ V q ik f₀ hk q₁ q₂ hZ W := by
    rw [chartZ_unique V q ik f₀ hk q₁ q₂ hZ C c hc cZ h1 h2]
    exact chartZ_naturality V r q ik f₀ hk q₁ q₂ hZ W.2.fromSpec (specOver q W.2) c hc hr
  rw [hcZ, Category.assoc, chZ_glued]
  have hn := locField_nat I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv Γ(Y, W.1) W.2.fromSpec (specOver q W.2)
    C r c hc hr
  have hs := locField_spec I hI hsmall V ι hι hιI q i₀ q₀ h₀ pA u hu v hv huv C c hc
  rw [hn] at hs
  exact hs

end Props
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.P2mWs2I1b"

end P2mWs2I1b
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.P2mWs2I1b"

open P2mWs2I1b in
theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [Flat q]

    {Y₀ : Scheme.{u}} (i₀ : Y₀ ⟶ Y) (q₀ : Y₀ ⟶ Spec (CommRingCat.of (T' ⧸ I)))
    (h₀ : IsPullback i₀ q₀ q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))

    {Yk : Scheme.{u}} (ik : Yk ⟶ Y) (f₀ : Yk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hk : IsPullback ik f₀ q (Spec.map (CommRingCat.ofHom (residue T'))))
    {Z : Scheme.{u}} (q₁ : Z ⟶ Yk) (q₂ : Z ⟶ SquareZero.spec (ResidueField T') V)
    (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase (ResidueField T') V))
    :
    ∃ Φ : ∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q),
        {v : Y ⟶ A // v ≫ pA = q ∧ i₀ ≫ v = i₀ ≫ u} →
          {w : Z ⟶ A // SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w = ik ≫ u},

      (∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q),
        Function.Injective (Φ pA u hu)) ∧

      (∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q),
        (Φ pA u hu ⟨u, hu, rfl⟩).1 = q₁ ≫ ik ≫ u) ∧

      (∀ {A A' : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (pA' : A' ⟶ Spec (CommRingCat.of T'))
        (g : A ⟶ A') (hg : g ≫ pA' = pA) (u : Y ⟶ A) (hu : u ≫ pA = q)
        (v : {v : Y ⟶ A // v ≫ pA = q ∧ i₀ ≫ v = i₀ ≫ u}),
        (Φ pA' (u ≫ g) (by rw [Category.assoc, hg, hu])
            ⟨v.1 ≫ g, by rw [Category.assoc, hg, v.2.1], by rw [← Category.assoc, v.2.2, Category.assoc]⟩).1 =
          (Φ pA u hu v).1 ≫ g) ∧

      ∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q)
        (v : {v : Y ⟶ A // v ≫ pA = q ∧ i₀ ≫ v = i₀ ≫ u})
        (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
        (c : Spec (CommRingCat.of C) ⟶ Y) (hc : c ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C))),
        (∃ U : Y.Opens, IsAffineOpen U ∧ Set.range c.base ⊆ (U : Set Y)) →
        ∀ (cZ : Spec (CommRingCat.of (SmallExtension.thickening T' V C)) ⟶ Z),
        cZ ≫ q₁ ≫ ik = SmallExtension.thickeningFst T' V C ≫
          Spec.map (CommRingCat.ofHom (SmallExtension.toReduction T' C)) ≫ c →
        cZ ≫ q₂ = SmallExtension.thickeningSnd T' V C →
        SmallExtension.IsTangentOfPair I V ι C (c ≫ u) (c ≫ v.1) (cZ ≫ (Φ pA u hu v).1) := by
  refine ⟨fun {A} pA u hu v =>
      ⟨glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v.1 v.2.1 v.2.2,
        zeroSection_glued I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v.1 v.2.1 v.2.2⟩,
    ?_, ?_, ?_, ?_⟩
  · intro A pA u hu v₁ v₂ h
    exact Subtype.ext (glued_injective I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu
      v₁.1 v₁.2.1 v₁.2.2 v₂.1 v₂.2.1 v₂.2.2 (congrArg Subtype.val h))
  · intro A pA u hu
    exact glued_self I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu
  · intro A A' pA pA' g hg u hu v
    exact glued_comp_target I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v.1 v.2.1 v.2.2 pA' g _ _ _
  · intro A pA u hu v C _ _ _ c hc hcU cZ h1 h2
    exact glued_isTangentOfPair I hI hsmall V ι hι hιI q i₀ q₀ h₀ ik f₀ hk q₁ q₂ hZ pA u hu v.1 v.2.1 v.2.2
      C c hc hcU cZ h1 h2

end S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat (solution)
