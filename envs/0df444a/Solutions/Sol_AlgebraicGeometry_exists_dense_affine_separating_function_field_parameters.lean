-- Prove2me | solution 1 for AlgebraicGeometry.exists_dense_affine_separating_function_field_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T17:00:56.752293+00:00
-- url     : https://prove2.me/submissions/6a5de2d0-b2cf-4360-8df6-2c7f9bda592e

import Mathlib

universe u


open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace PhilipponAlterationProjection

noncomputable abbrev functionFieldAlgebra {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) : Algebra K X.functionField :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra

noncomputable abbrev chartAlgebra {K : Type u} [Field K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) (U : X.Opens) : Algebra K Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom.toAlgebra

lemma chart_functionField_tower {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    letI := functionFieldAlgebra π
    letI := chartAlgebra π U
    IsScalarTower K Γ(X, U) X.functionField := by
  letI := functionFieldAlgebra π
  letI := chartAlgebra π U
  apply IsScalarTower.of_algebraMap_eq'
  symm
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp) ≫
    X.germToFunctionField U).hom =
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom
  have h : π.appLE ⊤ U (by simp) ≫ X.germToFunctionField U =
      π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    simp only [Scheme.Hom.appLE, Scheme.germToFunctionField, Category.assoc,
      X.presheaf.germ_res]
    rfl
  exact congrArg CommRingCat.Hom.hom
    (congrArg (fun q => (Scheme.ΓSpecIso (.of K)).inv ≫ q) h)

lemma chart_finiteType {K : Type u} [Field K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := chartAlgebra π U
    Algebra.FiniteType K Γ(X, U) := by
  have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) π inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  exact RingHom.FiniteType.comp h
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)

lemma functionField_essFiniteType {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    Algebra.EssFiniteType K X.functionField := by
  letI := functionFieldAlgebra π
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  letI := chartAlgebra π U
  letI := chart_functionField_tower π U
  letI := chart_finiteType π U hU
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors Γ(X, U))
  exact Algebra.EssFiniteType.comp K Γ(X, U) X.functionField

/-- A finite separating transcendence basis of the actual function field. -/
theorem exists_separating_function_field_parameters
    (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    ∃ s : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : s → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField := by
  letI := functionFieldAlgebra π
  letI := functionField_essFiniteType π
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K X.functionField
  have hr : Set.range ((↑) : s → X.functionField) = (s : Set X.functionField) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField := by
    have h := hs.isAlgebraic_field
    rw [hr] at h
    exact h
  haveI : Algebra.EssFiniteType (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField :=
    Algebra.EssFiniteType.of_comp K _ _
  exact ⟨s, hs, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep⟩

end PhilipponAlterationProjection



open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace PhilipponAlterationProjection

/-- Finitely many rational functions are regular on one dense affine open. -/
lemma exists_common_affine_germ_representatives {X : Scheme.{u}} [IsIntegral X]
    (s : Finset X.functionField) :
    ∃ (W : X.Opens), IsAffineOpen W ∧ genericPoint X ∈ W ∧
      ∃ hW : Nonempty W,
      ∃ a : s → Γ(X, W),
        ∀ f : s, @Scheme.germToFunctionField X _ W hW (a f) = f.val := by
  classical
  choose U hU g hg using fun f : X.functionField => X.presheaf.exists_germ_eq f
  have hη : genericPoint X ∈ s.inf U := by
    change genericPoint X ∈ ((s.inf U : X.Opens) : Set X)
    rw [Opens.coe_finset_inf, Finset.inf_eq_iInf]
    exact Set.mem_iInter₂.mpr fun f _ => hU f
  obtain ⟨W, hW, hηW, hWV⟩ := exists_isAffineOpen_mem_and_subset hη
  let hne : Nonempty W := ⟨⟨genericPoint X, hηW⟩⟩
  have hle : ∀ f : s, W ≤ U f.val :=
    fun f => (show W ≤ s.inf U from hWV).trans (Finset.inf_le f.property)
  refine ⟨W, hW, hηW, hne, fun f => X.presheaf.map (homOfLE (hle f)).op (g f.val), ?_⟩
  intro f
  change X.presheaf.germ W (genericPoint X) _
    (X.presheaf.map (homOfLE (hle f)).op (g f.val)) = f.val
  rw [X.presheaf.germ_res_apply (homOfLE (hle f)) (genericPoint X) hηW]
  exact hg f.val

end PhilipponAlterationProjection



open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace PhilipponAlterationProjection

lemma fromSpec_comp_structure {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (U : X.Opens) (hU : IsAffineOpen U) :
    hU.fromSpec ≫ π = Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)) := by
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec π (isAffineOpen_top _) hU (by simp)).symm

noncomputable def parameterChartMap {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (U : X.Opens) (hU : IsAffineOpen U)
    {ι : Type u} (a : ι → Γ(X, U)) :
    (U : Scheme) ⟶ Spec (.of (MvPolynomial ι K)) := by
  letI := chartAlgebra π U
  exact hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) a).toRingHom)

lemma parameterChartMap_over {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (U : X.Opens) (hU : IsAffineOpen U)
    {ι : Type u} (a : ι → Γ(X, U)) :
    parameterChartMap π U hU a ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial ι K)) = U.ι ≫ π := by
  letI := chartAlgebra π U
  have h : CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial ι K) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (R := K) a).toRingHom =
      (Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp) := by
    ext k
    exact (MvPolynomial.aeval (R := K) a).commutes k
  simp only [parameterChartMap, Category.assoc, ← Spec.map_comp, h]
  rw [← fromSpec_comp_structure π U hU, ← Category.assoc]
  simp only [← IsAffineOpen.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]

lemma parameterChartMap_dominant {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (U : X.Opens) (hU : IsAffineOpen U)
    {ι : Type u} (a : ι → Γ(X, U))
    (ha : letI := chartAlgebra π U; Function.Injective (MvPolynomial.aeval (R := K) a)) :
    IsDominant (parameterChartMap π U hU a) := by
  letI := chartAlgebra π U
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) a).toRingHom)) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
      (MvPolynomial.aeval (R := K) a).toRingHom).mpr
    rw [(RingHom.injective_iff_ker_eq_bot
      (MvPolynomial.aeval (R := K) a).toRingHom).mp ha]
    exact bot_le
  unfold parameterChartMap
  infer_instance

/-- A dominant map on a dense affine open, whose coordinate germs form a separating basis. -/
theorem exists_dense_affine_separating_parameters
    (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    ∃ s : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : s → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      ∃ (U : X.Opens) (hU : IsAffineOpen U), Dense (U : Set X) ∧
        ∃ hne : Nonempty U, ∃ a : s → Γ(X, U),
          (∀ t : s, @Scheme.germToFunctionField X _ U hne (a t) = t.val) ∧
          IsDominant (parameterChartMap π U hU a) ∧
          parameterChartMap π U hU a ≫
            Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial s K)) = U.ι ≫ π := by
  letI := functionFieldAlgebra π
  obtain ⟨s, hs, hfin, hsep⟩ := exists_separating_function_field_parameters K π
  obtain ⟨U, hU, hη, hne, a, ha⟩ := exists_common_affine_germ_representatives s
  letI := hne
  letI := chartAlgebra π U
  letI := chart_functionField_tower π U
  let g : Γ(X, U) →ₐ[K] X.functionField := IsScalarTower.toAlgHom K Γ(X, U) X.functionField
  have heval : g.comp (MvPolynomial.aeval (R := K) a) = MvPolynomial.aeval (R := K) ((↑) : s → X.functionField) := by
    ext t
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    exact ha t
  have hinj : Function.Injective (MvPolynomial.aeval (R := K) a) := by
    intro p q hpq
    apply (algebraicIndependent_iff_injective_aeval.mp hs.1)
    have h := congrArg g hpq
    change (g.comp (MvPolynomial.aeval (R := K) a)) p = (g.comp (MvPolynomial.aeval (R := K) a)) q at h
    rwa [heval] at h
  exact ⟨s, hs, hfin, hsep, U, hU, U.isOpen.dense ⟨genericPoint X, hη⟩,
    hne, a, ha, parameterChartMap_dominant π U hU a hinj, parameterChartMap_over π U hU a⟩

end PhilipponAlterationProjection


theorem solution
    (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    ∃ s : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : s → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      ∃ (U : X.Opens) (hU : IsAffineOpen U), Dense (U : Set X) ∧
        ∃ hne : Nonempty U, ∃ a : s → Γ(X, U),
          (∀ t : s, @Scheme.germToFunctionField X _ U hne (a t) = t.val) ∧
          ∃ f : (U : Scheme) ⟶ Spec (.of (MvPolynomial s K)),
            f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
              (MvPolynomial.eval₂Hom
                ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom a)) ∧
            IsDominant f ∧
            f ≫
            Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial s K)) = U.ι ≫ π := by
  letI := PhilipponAlterationProjection.functionFieldAlgebra π
  obtain ⟨s, hs, hfin, hsep, U, hU, hd, hne, a, ha, hdom, hover⟩ :=
    PhilipponAlterationProjection.exists_dense_affine_separating_parameters K π
  exact ⟨s, hs, hfin, hsep, U, hU, hd, hne, a, ha,
    PhilipponAlterationProjection.parameterChartMap π U hU a, rfl, hdom, hover⟩
