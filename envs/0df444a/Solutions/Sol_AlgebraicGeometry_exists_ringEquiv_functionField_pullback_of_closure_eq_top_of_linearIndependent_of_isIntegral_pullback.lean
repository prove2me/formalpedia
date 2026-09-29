-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent_of_isIntegral_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e0e0904a-e2cd-5dc8-b02c-fa00f80b77fe

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
import Theorems.Thm_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent_of_isIntegral_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct

namespace FFBC

theorem exists_finsupp_sum_tmul {K : Type} [Field K] {S K' : Type} [CommRing S] [CommRing K'] [Algebra K S] [Algebra K K']
    {F : Type} [AddCommGroup F] [Module K F] {ι : Type} (bs : Module.Basis ι K F) (eF : F →ₗ[K] S)
    (heF : Function.Surjective eF) (t : S ⊗[K] K') :
    ∃ c : ι →₀ K', c.sum (fun i k => (eF (bs i)) ⊗ₜ[K] k) = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s k =>
    obtain ⟨x, rfl⟩ := heF s
    refine ⟨(bs.repr x).mapRange (fun r => r • k) (by simp), ?_⟩
    rw [Finsupp.sum_mapRange_index (fun i => by simp)]
    conv_rhs => rw [← bs.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    simp only [Finsupp.sum, TensorProduct.sum_tmul, map_smul, TensorProduct.smul_tmul]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨c₁, rfl⟩ := h₁
    obtain ⟨c₂, rfl⟩ := h₂
    refine ⟨c₁ + c₂, ?_⟩
    rw [Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by simp [TensorProduct.tmul_add])]

theorem core_alg
    {K : Type} [Field K] {K' : Type} [Field K'] [Algebra K K']
    {S : Type} [CommRing S] [Algebra K S]
    {F : Type} [Field F] [Algebra K F] (eF : F ≃+* S)
    (eF_algebraMap : ∀ a : K, eF (algebraMap K F a) = algebraMap K S a)
    {F' : Type} [Field F'] [Algebra K' F'] (to' : F →+* F')
    (to'_algebraMap : ∀ a : K, to' (algebraMap K F a) = algebraMap K' F' (algebraMap K K' a))
    (closure_to' : Subfield.closure (Set.range (algebraMap K' F') ∪ Set.range to') = ⊤)
    (linearIndependent_to' : ∀ s : Finset F,
      LinearIndependent K (fun x : s => (x : F)) → LinearIndependent K' (fun x : s => to' (x : F)))
    (𝔮 : Ideal (S ⊗[K] K')) [𝔮.IsPrime]
    {L : Type} [CommRing L] (hL : IsField L) (e : L ≃+* Localization.AtPrime 𝔮) :
    ∃ Θ : F' ≃+* L,
      (∀ c : K', Θ (algebraMap K' F' c) = e.symm (algebraMap (S ⊗[K] K') (Localization.AtPrime 𝔮) (1 ⊗ₜ[K] c))) ∧
      (∀ s : S, Θ (to' (eF.symm s)) = e.symm (algebraMap (S ⊗[K] K') (Localization.AtPrime 𝔮) (s ⊗ₜ[K] 1))) := by
  classical
  letI algKF' : Algebra K F' := ((algebraMap K' F').comp (algebraMap K K')).toAlgebra
  haveI towF' : IsScalarTower K K' F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let f : S →ₐ[K] F' :=
    { toRingHom := to'.comp eF.symm.toRingHom
      commutes' := fun a => by
        show to' (eF.symm (algebraMap K S a)) = algebraMap K' F' (algebraMap K K' a)
        rw [← eF_algebraMap, RingEquiv.symm_apply_apply, to'_algebraMap] }
  let g : K' →ₐ[K] F' := IsScalarTower.toAlgHom K K' F'
  let Ψ : S ⊗[K] K' →ₐ[K] F' := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have Ψ_tmul : ∀ (s : S) (c : K'), Ψ (s ⊗ₜ[K] c) = to' (eF.symm s) * algebraMap K' F' c := by
    intro s c
    show Algebra.TensorProduct.lift f g _ (s ⊗ₜ[K] c) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl

  have Ψ_inj : Function.Injective Ψ := by
    let eFl : F →ₗ[K] S :=
      { toFun := eF
        map_add' := fun x y => map_add eF x y
        map_smul' := fun q x => by
          show eF (q • x) = q • eF x
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, eF_algebraMap] }
    have eFl_apply : ∀ x, eFl x = eF x := fun _ => rfl
    let bs := Module.Basis.ofVectorSpace K F
    have key : ∀ c : ↑(Module.Basis.ofVectorSpaceIndex K F) →₀ K',
        Ψ (c.sum fun i k => eF (bs i) ⊗ₜ[K] k) = 0 → c = 0 := by
      intro c hc
      rw [map_finsuppSum] at hc
      simp only [Ψ_tmul, RingEquiv.symm_apply_apply] at hc
      have hli : LinearIndependent K' (fun i : ↥c.support => to' (bs (i : ↑(Module.Basis.ofVectorSpaceIndex K F)))) := by
        let s : Finset F := c.support.image bs
        have hsub : ((s : Set F)) ⊆ Set.range bs := by
          intro x hx
          simp only [s, Finset.coe_image] at hx
          obtain ⟨i, -, rfl⟩ := hx
          exact ⟨i, rfl⟩
        have hs : LinearIndependent K (fun x : (s : Set F) => (x : F)) :=
          (bs.linearIndependent.linearIndepOn_id.mono hsub).linearIndependent
        have hs' := linearIndependent_to' s hs
        let φ : ↥c.support → ↥s := fun i => ⟨bs i, Finset.mem_image_of_mem bs i.2⟩
        have hφ : Function.Injective φ := fun i j h => Subtype.ext (bs.injective (Subtype.ext_iff.mp h))
        exact hs'.comp φ hφ
      rw [Fintype.linearIndependent_iff] at hli
      have hsum : ∑ i : ↥c.support, c i • to' (bs i) = 0 := by
        rw [Finset.sum_coe_sort c.support (fun i => c i • to' (bs i))]
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
    obtain ⟨c, rfl⟩ := exists_finsupp_sum_tmul bs eFl eF.surjective t
    simp only [eFl_apply] at ht ⊢
    rw [key c ht, Finsupp.sum_zero_index]

  have hunit : ∀ y : 𝔮.primeCompl, IsUnit (Ψ.toRingHom y) := by
    intro y
    rw [isUnit_iff_ne_zero]
    intro h0
    have hy0 : (y : S ⊗[K] K') = 0 := Ψ_inj (by rw [map_zero]; exact h0)
    exact y.2 (by rw [hy0]; exact 𝔮.zero_mem)
  let φ : Localization.AtPrime 𝔮 →+* F' := IsLocalization.lift (M := 𝔮.primeCompl) hunit
  have φ_alg : ∀ t : S ⊗[K] K', φ (algebraMap (S ⊗[K] K') (Localization.AtPrime 𝔮) t) = Ψ t :=
    fun t => IsLocalization.lift_eq hunit t

  have hT : IsField (Localization.AtPrime 𝔮) := MulEquiv.isField hL e.symm.toMulEquiv
  have φ_inj : Function.Injective φ := by
    haveI := Ring.isField_iff_isSimpleOrder_ideal.mp hT
    rcases eq_bot_or_eq_top (RingHom.ker φ) with h | h
    · exact (RingHom.injective_iff_ker_eq_bot φ).mpr h
    · exfalso
      have h1 : (1 : Localization.AtPrime 𝔮) ∈ RingHom.ker φ := by rw [h]; trivial
      rw [RingHom.mem_ker, map_one] at h1
      exact one_ne_zero h1

  have φ_surj : Function.Surjective φ := by
    let Kφ : Subfield F' :=
      { toSubring := φ.range
        inv_mem' := fun x hx => by
          obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hx
          by_cases ha : a = 0
          · rw [ha, map_zero, inv_zero]; exact φ.range.zero_mem
          · obtain ⟨b, hb⟩ := hT.mul_inv_cancel ha
            refine RingHom.mem_range.mpr ⟨b, ?_⟩
            symm
            apply inv_eq_of_mul_eq_one_right
            rw [← map_mul, hb, map_one] }
    have htop : (⊤ : Subfield F') ≤ Kφ := by
      rw [← closure_to', Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | ⟨x, rfl⟩)
      · exact RingHom.mem_range.mpr ⟨algebraMap _ _ ((1 : S) ⊗ₜ[K] c), by rw [φ_alg, Ψ_tmul, map_one, map_one, one_mul]⟩
      · exact RingHom.mem_range.mpr ⟨algebraMap _ _ (eF x ⊗ₜ[K] (1 : K')), by
          rw [φ_alg, Ψ_tmul, RingEquiv.symm_apply_apply, map_one, mul_one]⟩
    intro y
    exact RingHom.mem_range.mp (htop (Subfield.mem_top y))
  let ΦE : Localization.AtPrime 𝔮 ≃+* F' := RingEquiv.ofBijective φ ⟨φ_inj, φ_surj⟩
  have ΦE_apply : ∀ t, ΦE t = φ t := fun _ => rfl
  refine ⟨ΦE.symm.trans e.symm, fun c => ?_, fun s => ?_⟩
  · rw [RingEquiv.trans_apply]
    congr 1
    rw [RingEquiv.symm_apply_eq, ΦE_apply, φ_alg, Ψ_tmul, map_one, map_one, one_mul]
  · rw [RingEquiv.trans_apply]
    congr 1
    rw [RingEquiv.symm_apply_eq, ΦE_apply, φ_alg, Ψ_tmul, map_one, mul_one]

theorem fst_base_genericPoint {K : Type} [Field K] {K' : Type} [Field K'] [Algebra K K']
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of K)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))] :
    genericPoint X = (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) := by
  set Y := pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))
  set z := (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) with hz
  have hmem : ∀ U : X.Opens, (U : Set X).Nonempty → z ∈ U := by
    intro U hU
    have := genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap (algebraMap K K').injective πX
      (Y := Y) (𝟙 _) U hU
    simpa using this
  have hgen : IsGenericPoint z (Set.univ : Set X) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    rw [specializes_iff_forall_open]
    intro s hs hys
    exact hmem ⟨s, hs⟩ ⟨y, hys⟩
  exact (genericPoint_spec X).eq hgen

theorem geom {K : Type} [Field K] {K' : Type} [Field K'] [Algebra K K']
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of K)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))]
    (z : X) (hx : (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) = z)
    {F : Type} [Field F] [Algebra K F] (eF : F ≃+* X.presheaf.stalk z)
    (eF_algebraMap : ∀ a : K, eF (algebraMap K F a) =
      (X.presheaf.germ ⊤ z trivial).hom (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)))
    {F' : Type} [Field F'] [Algebra K' F'] (to' : F →+* F')
    (to'_algebraMap : ∀ a : K, to' (algebraMap K F a) = algebraMap K' F' (algebraMap K K' a))
    (closure_to' : Subfield.closure (Set.range (algebraMap K' F') ∪ Set.range to') = ⊤)
    (linearIndependent_to' : ∀ s : Finset F,
      LinearIndependent K (fun x : s => (x : F)) → LinearIndependent K' (fun x : s => to' (x : F))) :
    letI : Algebra K (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))))) :=
      ((X.presheaf.germ ⊤ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))))) trivial).hom.comp (πX.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    ∀ (𝔮 : Ideal ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))))) ⊗[K] K')) (_ : 𝔮.IsPrime)
      (e : (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).presheaf.stalk (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) ≃+* Localization.AtPrime 𝔮),
      (∀ s : X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))))),
        e (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).stalkMap (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))))).hom s) = algebraMap ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))))) ⊗[K] K') (Localization.AtPrime 𝔮) (s ⊗ₜ[K] 1)) →
      (∀ c : K',
        e ((pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).presheaf.germ ⊤ (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) trivial ((pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).appTop ((Scheme.ΓSpecIso (CommRingCat.of K')).inv c))) =
          algebraMap ((X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))))) ⊗[K] K') (Localization.AtPrime 𝔮) (1 ⊗ₜ[K] c)) →
    ∃ eF' : F' ≃+* ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField,
      (∀ c : K', eF' (algebraMap K' F' c) = baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))) c) ∧
      ∀ (U : X.Opens) (hzU : z ∈ U) (t : Γ(X, U)),
        eF' (to' (eF.symm ((X.presheaf.germ U z hzU).hom t))) =
          ((pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).presheaf.germ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U) (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) (show (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) ∈ U by rw [hx]; exact hzU)).hom (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).app U).hom t) := by
  subst hx
  intro 𝔮 h𝔮 e he1 he2
  letI algK : Algebra K (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))))) :=
    ((X.presheaf.germ ⊤ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))))) trivial).hom.comp (πX.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
  have algK_def : ∀ a : K, algebraMap K (X.presheaf.stalk ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))))) a =
      (X.presheaf.germ ⊤ ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))))) trivial).hom (πX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) := fun _ => rfl
  have hL : IsField ↑((pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).presheaf.stalk (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))))) := Field.toIsField ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField
  obtain ⟨Θ, hΘ1, hΘ2⟩ := core_alg eF (fun a => by rw [eF_algebraMap, algK_def]) to' to'_algebraMap closure_to'
    linearIndependent_to' 𝔮 hL e
  refine ⟨Θ, fun c => ?_, fun U hzU t => ?_⟩
  · rw [hΘ1, RingEquiv.symm_apply_eq]
    exact (he2 c).symm
  · rw [hΘ2, RingEquiv.symm_apply_eq, ← he1]
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))) U (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) hzU t

end FFBC

open FFBC in
theorem solution
    {K : Type} [Field K] {K' : Type} [Field K'] [Algebra K K']
    {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of K)) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral
      ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))]
    {F : Type} [Field F] [Algebra K F] (eF : F ≃+* X.functionField)

    (eF_algebraMap : ∀ a : K, eF (algebraMap K F a) = baseToFunctionField πX a)
    {F' : Type} [Field F'] [Algebra K' F'] (to' : F →+* F')
    (to'_algebraMap : ∀ a : K,
      to' (algebraMap K F a) = algebraMap K' F' (algebraMap K K' a))
    (closure_to' : Subfield.closure
      (Set.range (algebraMap K' F') ∪ Set.range to') = ⊤)
    (linearIndependent_to' : ∀ s : Finset F,
      LinearIndependent K (fun x : s => (x : F)) →
        LinearIndependent K' (fun x : s => to' (x : F))) :
    ∃ eF' : F' ≃+* ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField,
      (∀ z : K', eF' (algebraMap K' F' z) =
        baseToFunctionField (pullback.snd πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))) z) ∧
      ∀ (U : X.Opens) [Nonempty (U : Scheme.{0})]
        [Nonempty (((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U :
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).Opens) : Scheme.{0})]
        (t : Γ(X, U)),
        eF' (to' (eF.symm (X.germToFunctionField U t))) =
          (pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).germToFunctionField
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U)
            ((pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).app U t) := by
  have hz : genericPoint X = (pullback.fst πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) := fst_base_genericPoint πX
  obtain ⟨𝔮, h𝔮, e, -, he1, he2⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd X πX K' (genericPoint ↑(pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K K')))))
  obtain ⟨eF', h1, h2⟩ := geom πX (genericPoint X) hz.symm eF eF_algebraMap to' to'_algebraMap closure_to'
    linearIndependent_to' 𝔮 h𝔮 e he1 he2
  refine ⟨eF', h1, fun U hU _ t => ?_⟩
  have hmem : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by obtain ⟨x⟩ := hU; exact ⟨x.1, trivial, x.2⟩)
  exact h2 U hmem t

end S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent_of_isIntegral_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_closure_eq_top_of_linearIndependent_of_isIntegral_pullback (solution)
