-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f117fe94-8c5e-508d-b776-46a299040ffb

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
import Theorems.Thm_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct

namespace UnramFF

theorem rat_smul_tmul {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {A B : Type} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B] [Algebra ℚ A] [Algebra ℚ B]
    [IsScalarTower R₀ ℚ A] [IsScalarTower R₀ ℚ B] (q : ℚ) (a : A) (b : B) :
    ((q • a) ⊗ₜ[R₀] b : A ⊗[R₀] B) = a ⊗ₜ[R₀] (q • b) := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : ((q.den : ℤ) : ℚ) * q = (q.num : ℚ) := by
    have := Rat.mul_den_eq_num q
    push_cast
    linarith [this, mul_comm q (q.den : ℚ)]

  have hb : b = (q.den : ℤ) • (((q.den : ℚ))⁻¹ • b) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hd, one_smul]
  have hA : (q.den : ℤ) • (q • a) = (q.num : ℤ) • a := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, hq, Int.cast_smul_eq_zsmul]
  have hB : (q.num : ℤ) • (((q.den : ℚ))⁻¹ • b) = q • b := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, ← hq]
    push_cast
    rw [mul_comm ((q.den : ℚ)) q, mul_assoc, mul_inv_cancel₀ hd, mul_one]
  conv_lhs => rw [hb]
  rw [← TensorProduct.smul_tmul, hA, TensorProduct.smul_tmul, hB]

theorem exists_finsupp_sum_tmul {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {A B : Type} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B] [Algebra ℚ A] [Algebra ℚ B]
    [IsScalarTower R₀ ℚ A] [IsScalarTower R₀ ℚ B]
    {F : Type} [AddCommGroup F] [Module ℚ F] {ι : Type} (bs : Module.Basis ι ℚ F) (eF : F →ₗ[ℚ] A)
    (heF : Function.Surjective eF) (t : A ⊗[R₀] B) :
    ∃ c : ι →₀ B, c.sum (fun i k => (eF (bs i)) ⊗ₜ[R₀] k) = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s k =>
    obtain ⟨x, rfl⟩ := heF s
    refine ⟨(bs.repr x).mapRange (fun r => r • k) (by simp), ?_⟩
    rw [Finsupp.sum_mapRange_index (fun i => by simp)]
    conv_rhs => rw [← bs.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    simp only [Finsupp.sum, TensorProduct.sum_tmul, map_smul, rat_smul_tmul]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨c₁, rfl⟩ := h₁
    obtain ⟨c₂, rfl⟩ := h₂
    refine ⟨c₁ + c₂, ?_⟩
    rw [Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by simp [TensorProduct.tmul_add])]

theorem fst_base_genericPoint {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))]
    (hinj : Function.Injective (algebraMap R₀ (AlgebraicClosure ℚ))) :
    genericPoint X = (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))) := by
  set Y := pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))
  set z := (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑Y) with hz
  have hmem : ∀ U : X.Opens, (U : Set X).Nonempty → z ∈ U := by
    intro U hU
    have := genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap hinj πX (Y := Y) (𝟙 _) U hU
    simpa using this
  have hgen : IsGenericPoint z (Set.univ : Set X) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    rw [specializes_iff_forall_open]
    intro s hs hys
    exact hmem ⟨s, hs⟩ ⟨y, hys⟩
  exact (genericPoint_spec X).eq hgen

theorem core {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))]
    (hinj : Function.Injective (algebraMap R₀ (AlgebraicClosure ℚ)))
    (z : X) (hx : ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))) = z)
    {F : Type} [Field F] [Algebra ℚ F] (eF : F ≃+* X.presheaf.stalk z)
    {Fbar : Type} [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar] (toBar : F →+* Fbar)
    (toBar_algebraMap : ∀ r : ℚ, toBar (algebraMap ℚ F r) = algebraMap (AlgebraicClosure ℚ) Fbar (algebraMap ℚ (AlgebraicClosure ℚ) r))
    (closure_toBar : Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range toBar) = ⊤)
    (linearIndependent_toBar : ∀ s : Finset F,
      LinearIndependent ℚ (fun x : s => (x : F)) → LinearIndependent (AlgebraicClosure ℚ) (fun x : s => toBar (x : F)))
    (eF_symm_germ : ∀ r : R₀, eF.symm ((X.presheaf.germ ⊤ z trivial).hom
        (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom r))) = algebraMap ℚ F (algebraMap R₀ ℚ r)) :
    letI : Algebra R₀ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) :=
      ((X.presheaf.germ ⊤ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))) trivial).hom.comp (πX.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom)).toAlgebra
    ∀ (𝔮 : Ideal ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) ⊗[R₀] (AlgebraicClosure ℚ))) (_ : 𝔮.IsPrime)
      (e : (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).presheaf.stalk (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))) ≃+* Localization.AtPrime 𝔮),
      (∀ s : X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))),
        e (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).stalkMap (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))).hom s) =
          algebraMap ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) ⊗[R₀] (AlgebraicClosure ℚ)) (Localization.AtPrime 𝔮) (s ⊗ₜ[R₀] 1)) →
      (∀ c : (AlgebraicClosure ℚ),
        e ((pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).presheaf.germ ⊤ (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))) trivial
            ((pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).appTop ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv c))) =
          algebraMap ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) ⊗[R₀] (AlgebraicClosure ℚ)) (Localization.AtPrime 𝔮) (1 ⊗ₜ[R₀] c)) →
    ∃ eFbar : Fbar ≃+* ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).functionField,
      (∀ c : (AlgebraicClosure ℚ), eFbar (algebraMap (AlgebraicClosure ℚ) Fbar c) = baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))) c) ∧
      ∀ (U : X.Opens) (hzU : z ∈ U) (t : Γ(X, U)),
        eFbar (toBar (eF.symm ((X.presheaf.germ U z hzU).hom t))) =
          ((pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).presheaf.germ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))) ⁻¹ᵁ U) (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))) (show (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))) ∈ U by rw [hx]; exact hzU)).hom
            (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).app U).hom t) := by
  subst hx
  intro 𝔮 h𝔮 e he1 he2
  letI algR : Algebra R₀ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) := ((X.presheaf.germ ⊤ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))) trivial).hom.comp (πX.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom)).toAlgebra

  letI algQ : Algebra ℚ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) := (eF.toRingHom.comp (algebraMap ℚ F)).toAlgebra
  have algQ_def : ∀ q : ℚ, algebraMap ℚ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) q = eF (algebraMap ℚ F q) := fun _ => rfl
  have algR_def : ∀ r : R₀, algebraMap R₀ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) r =
      (X.presheaf.germ ⊤ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))) trivial).hom (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom r)) := fun _ => rfl
  haveI towQ : IsScalarTower R₀ ℚ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    rw [algQ_def, ← eF_symm_germ, RingEquiv.apply_symm_apply, algR_def]

  letI algRF : Algebra R₀ Fbar := ((algebraMap (AlgebraicClosure ℚ) Fbar).comp (algebraMap R₀ (AlgebraicClosure ℚ))).toAlgebra
  haveI towF : IsScalarTower R₀ (AlgebraicClosure ℚ) Fbar := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let f : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) →ₐ[R₀] Fbar :=
    { toRingHom := toBar.comp eF.symm.toRingHom
      commutes' := fun r => by
        show toBar (eF.symm (algebraMap R₀ (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) r)) = algebraMap (AlgebraicClosure ℚ) Fbar (algebraMap R₀ (AlgebraicClosure ℚ) r)
        rw [algR_def, eF_symm_germ, toBar_algebraMap, ← IsScalarTower.algebraMap_apply R₀ ℚ (AlgebraicClosure ℚ)] }
  let g : (AlgebraicClosure ℚ) →ₐ[R₀] Fbar := IsScalarTower.toAlgHom R₀ (AlgebraicClosure ℚ) Fbar
  let Ψ : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) ⊗[R₀] (AlgebraicClosure ℚ) →ₐ[R₀] Fbar := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have Ψ_tmul : ∀ (s : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))))) (c : (AlgebraicClosure ℚ)), Ψ (s ⊗ₜ[R₀] c) = toBar (eF.symm s) * algebraMap (AlgebraicClosure ℚ) Fbar c := by
    intro s c
    show Algebra.TensorProduct.lift f g _ (s ⊗ₜ[R₀] c) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl

  have Ψ_surj : Function.Surjective Ψ := by
    classical
    letI algF : Algebra F Fbar := toBar.toAlgebra
    have algF_def : ∀ x : F, algebraMap F Fbar x = toBar x := fun _ => rfl
    let A₁ : Subalgebra F Fbar := Algebra.adjoin F (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar))
    have hA₁ : A₁ ≤ integralClosure F Fbar := by
      apply Algebra.adjoin_le
      rintro x ⟨c, rfl⟩
      rw [SetLike.mem_coe, mem_integralClosure_iff]
      obtain ⟨p, hp, hpc⟩ := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c).isIntegral
      refine ⟨p.map (algebraMap ℚ F), hp.map _, ?_⟩
      have h2 := congrArg (algebraMap (AlgebraicClosure ℚ) Fbar) hpc
      rw [map_zero, Polynomial.hom_eval₂] at h2
      rw [Polynomial.eval₂_map, show (algebraMap F Fbar).comp (algebraMap ℚ F) =
          (algebraMap (AlgebraicClosure ℚ) Fbar).comp (algebraMap ℚ (AlgebraicClosure ℚ)) from
        Subsingleton.elim _ _]
      exact h2
    let K₁ : Subfield Fbar :=
      { toSubring := A₁.toSubring
        inv_mem' := fun x hx => by
          have hint : IsIntegral F x := (mem_integralClosure_iff F Fbar).mp (hA₁ hx)
          exact Subalgebra.inv_mem_of_algebraic A₁ (x := ⟨x, hx⟩) hint.isAlgebraic }
    have htop : (⊤ : Subfield Fbar) ≤ K₁ := by
      rw [← closure_toBar, Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | ⟨x, rfl⟩)
      · exact Algebra.subset_adjoin ⟨c, rfl⟩
      · rw [← algF_def]; exact Subalgebra.algebraMap_mem A₁ x
    let S₂ : Subalgebra F Fbar :=
      { carrier := Set.range Ψ
        mul_mem' := by rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u * v, map_mul Ψ u v⟩
        one_mem' := ⟨1, map_one Ψ⟩
        add_mem' := by rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u + v, map_add Ψ u v⟩
        zero_mem' := ⟨0, map_zero Ψ⟩
        algebraMap_mem' := fun x => ⟨eF x ⊗ₜ[R₀] 1, by rw [Ψ_tmul, RingEquiv.symm_apply_apply, map_one, mul_one]; rfl⟩ }
    have hA₁S : A₁ ≤ S₂ := by
      apply Algebra.adjoin_le
      rintro y ⟨c, rfl⟩
      exact ⟨1 ⊗ₜ[R₀] c, by rw [Ψ_tmul, map_one, map_one, one_mul]⟩
    intro y
    have hy : y ∈ S₂ := hA₁S (htop (Subfield.mem_top y))
    exact hy

  have Ψ_inj : Function.Injective Ψ := by
    classical
    let eFl : F →ₗ[ℚ] (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) :=
      { toFun := eF
        map_add' := fun x y => map_add eF x y
        map_smul' := fun q x => by
          show eF (q • x) = q • eF x
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, algQ_def] }
    have eFl_apply : ∀ x, eFl x = eF x := fun _ => rfl
    let bs := Module.Basis.ofVectorSpace ℚ F
    have key : ∀ c : ↑(Module.Basis.ofVectorSpaceIndex ℚ F) →₀ (AlgebraicClosure ℚ),
        Ψ (c.sum fun i k => eF (bs i) ⊗ₜ[R₀] k) = 0 → c = 0 := by
      intro c hc
      rw [map_finsuppSum] at hc
      simp only [Ψ_tmul, RingEquiv.symm_apply_apply] at hc

      have hli : LinearIndependent (AlgebraicClosure ℚ) (fun i : ↥c.support => toBar (bs (i : ↑(Module.Basis.ofVectorSpaceIndex ℚ F)))) := by
        let s : Finset F := c.support.image bs
        have hsub : ((s : Set F)) ⊆ Set.range bs := by
          intro x hx
          simp only [s, Finset.coe_image] at hx
          obtain ⟨i, -, rfl⟩ := hx
          exact ⟨i, rfl⟩
        have hs : LinearIndependent ℚ (fun x : (s : Set F) => (x : F)) :=
          (bs.linearIndependent.linearIndepOn_id.mono hsub).linearIndependent
        have hs' := linearIndependent_toBar s hs
        let φ : ↥c.support → ↥s := fun i => ⟨bs i, Finset.mem_image_of_mem bs i.2⟩
        have hφ : Function.Injective φ := fun i j h => Subtype.ext (bs.injective (Subtype.ext_iff.mp h))
        exact hs'.comp φ hφ
      rw [Fintype.linearIndependent_iff] at hli
      have hsum : ∑ i : ↥c.support, c i • toBar (bs i) = 0 := by
        rw [Finset.sum_coe_sort c.support (fun i => c i • toBar (bs i))]
        rw [Finsupp.sum] at hc
        refine (Finset.sum_congr rfl fun i _ => ?_).trans hc
        rw [Algebra.smul_def, mul_comm]
      have h0 := hli (fun i => c i) hsum
      ext i
      by_cases hi : i ∈ c.support
      · exact h0 ⟨i, hi⟩
      · exact Finsupp.notMem_support_iff.mp hi
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨c, rfl⟩ := exists_finsupp_sum_tmul (R₀ := R₀) bs eFl eF.surjective t
    simp only [eFl_apply] at ht ⊢
    rw [key c ht, Finsupp.sum_zero_index]
  let ΨE : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) ⊗[R₀] (AlgebraicClosure ℚ) ≃+* Fbar := RingEquiv.ofBijective Ψ.toRingHom ⟨Ψ_inj, Ψ_surj⟩
  have ΨE_apply : ∀ t, ΨE t = Ψ t := fun _ => rfl

  have hT : IsField ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) ⊗[R₀] (AlgebraicClosure ℚ)) := MulEquiv.isField (Field.toIsField Fbar) ΨE.toMulEquiv
  have hbij : Function.Bijective (algebraMap ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) ⊗[R₀] (AlgebraicClosure ℚ)) (Localization.AtPrime 𝔮)) :=
    by convert IsField.localization_map_bijective (Rₘ := Localization.AtPrime 𝔮) (M := 𝔮.primeCompl) (fun h => h 𝔮.zero_mem) hT
  let lam : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))))) ⊗[R₀] (AlgebraicClosure ℚ) ≃+* Localization.AtPrime 𝔮 := RingEquiv.ofBijective (algebraMap _ (Localization.AtPrime 𝔮)) hbij
  have lam_apply : ∀ t, lam t = algebraMap _ (Localization.AtPrime 𝔮) t := fun _ => rfl

  refine ⟨ΨE.symm.trans (lam.trans e.symm), ?_, ?_⟩
  · intro c
    have h1 : ΨE.symm (algebraMap (AlgebraicClosure ℚ) Fbar c) = (1 : (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))))) ⊗ₜ[R₀] c := by
      rw [RingEquiv.symm_apply_eq, ΨE_apply, Ψ_tmul, map_one, map_one, one_mul]
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h1, RingEquiv.symm_apply_eq]
    exact (he2 c).symm
  · intro U hzU t
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
    have h1 : ΨE.symm (toBar (eF.symm ((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))) hzU).hom t))) =
        ((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))) hzU).hom t) ⊗ₜ[R₀] (1 : (AlgebraicClosure ℚ)) := by
      rw [RingEquiv.symm_apply_eq, ΨE_apply, Ψ_tmul, map_one, mul_one]
    calc lam (ΨE.symm (toBar (eF.symm ((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))) hzU).hom t))))
        = lam (((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))) hzU).hom t) ⊗ₜ[R₀] (1 : (AlgebraicClosure ℚ))) := congrArg lam h1
      _ = e (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).stalkMap (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))).hom ((X.presheaf.germ U ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))) hzU).hom t)) := (he1 _).symm
      _ = _ := congrArg e (Scheme.Hom.germ_stalkMap_apply (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))) U (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))) hzU t)

end UnramFF

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve in
open scoped TensorProduct in
theorem solution
    {R₀ : Type} [CommRing R₀] [Algebra R₀ ℚ]
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral
      ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))]
    (hinj : Function.Injective (algebraMap R₀ (AlgebraicClosure ℚ)))
    {F : Type} [Field F] [Algebra ℚ F] (eF : F ≃+* X.functionField)
    {Fbar : Type} [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar] (toBar : F →+* Fbar)
    (toBar_algebraMap : ∀ r : ℚ,
      toBar (algebraMap ℚ F r) = algebraMap (AlgebraicClosure ℚ) Fbar (algebraMap ℚ (AlgebraicClosure ℚ) r))
    (closure_toBar : Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range toBar) = ⊤)
    (linearIndependent_toBar : ∀ s : Finset F,
      LinearIndependent ℚ (fun x : s => (x : F)) →
        LinearIndependent (AlgebraicClosure ℚ) (fun x : s => toBar (x : F)))

    (eF_symm_germ : ∀ r : R₀,
      eF.symm ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom
        (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom r))) =
      algebraMap ℚ F (algebraMap R₀ ℚ r)) :
    ∃ eFbar : Fbar ≃+* ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).functionField,
      (∀ z : AlgebraicClosure ℚ, eFbar (algebraMap (AlgebraicClosure ℚ) Fbar z) =
        baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))) z) ∧
      ∀ (U : X.Opens) [Nonempty (U : Scheme.{0})]
        [Nonempty (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))) ⁻¹ᵁ U :
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).Opens) : Scheme.{0})]
        (t : Γ(X, U)),
        eFbar (toBar (eF.symm (X.germToFunctionField U t))) =
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).germToFunctionField
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))) ⁻¹ᵁ U)
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).app U t) := by
  have hz : genericPoint X = (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ)))))) := UnramFF.fst_base_genericPoint πX hinj
  obtain ⟨𝔮, h𝔮, e, -, he1, he2⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd X πX (AlgebraicClosure ℚ) (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap R₀ (AlgebraicClosure ℚ))))))
  obtain ⟨eFbar, h1, h2⟩ := UnramFF.core πX hinj (genericPoint X) hz.symm eF toBar toBar_algebraMap closure_toBar
    linearIndependent_toBar eF_symm_germ 𝔮 h𝔮 e he1 he2
  refine ⟨eFbar, h1, fun U hU _ t => ?_⟩
  have hmem : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by obtain ⟨x⟩ := hU; exact ⟨x.1, trivial, x.2⟩)
  exact h2 U hmem t

end S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent (solution)
