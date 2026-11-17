-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_numberField_finiteFrame_descent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:39.724039+00:00
-- url     : https://prove2.me/submissions/7d698b01-8bbe-47b9-8e56-615d7f342a6b

import Mathlib
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_finiteBySections
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Modules

/-- A chosen finite presentation descends once its sections have descended.
The cartesian comparison retains the projective dimension and the entire tuple. -/
private theorem exists_finite_projPresentation_of_descended_sections
    {K E : Type} [Field K] [Field E] [Algebra K E]
    {X Y : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
    (g : Y ⟶ Spec (CommRingCat.of E)) (c : Y ⟶ X)
    (hc : IsPullback c g f (Spec.map (CommRingCat.ofHom (algebraMap K E))))
    (M : X.Modules) (hM : IsInvertible M) {N : ℕ}
    (P : ((Scheme.Modules.pullback c).obj M).ProjPresentation g N)
    (hfinite : IsFinite P.toProj)
    (σ : Fin (N + 1) → Γ(M, ⊤))
    (hσ : ∀ i, P.σ i = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M).app ⊤) (σ i)) :
    ∃ Q : M.ProjPresentation f N, Q.σ = σ ∧ IsFinite Q.toProj ∧
      IsPullback c P.toProj Q.toProj (ProjSpace.map K E N) := by
  classical
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K E))) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of E)))
    exact ⟨x, Subsingleton.elim _ _⟩
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap K E))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI : Algebra K E := (algebraMap K E).toAlgebra
    change Module.Flat K E
    infer_instance
  haveI : Surjective c := MorphismProperty.of_isPullback (P := @Surjective) hc.flip hsurj
  let U : Fin (N + 1) → Y.Opens := fun i =>
    P.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) E) (MvPolynomial.X i)
  have hU : iSup U = ⊤ := by
    apply top_le_iff.mp
    intro y _
    have hy : P.toProj.base y ∈ (⨆ i : Fin (N + 1),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) E) (MvPolynomial.X i)) := by
      rw [Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X E N)]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨V, hV, hframe⟩ :=
    IsInvertible.exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective c M hM σ P.σ hσ
      P.σ U hU (fun i W hW => P.frame i W hW) (fun i => by
        refine ⟨Pi.single i 1, ?_⟩
        simp)
  obtain ⟨Q, hQσ, _⟩ := exists_projPresentation_of_iSup_eq_top f M N σ V hV hframe
  obtain ⟨Q', hQ'σ, _, hsquare⟩ := Q.exists_baseChange_of_isPullback hc
  have hmap : Q'.toProj = P.toProj := by
    apply Q'.toProj_eq_of_forall_sections_eq_univ P
    intro i
    rw [hQ'σ i, hQσ, ← hσ i]
  have hsquare' : IsPullback c P.toProj Q.toProj (ProjSpace.map K E N) := by
    rw [← hmap]
    exact hsquare
  letI hproper := IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact.{0}
  letI haffine := IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasiCompact.{0}
  letI hfiniteDesc : MorphismProperty.DescendsAlong (@IsFinite : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    rw [IsFinite.eq_isProper_inf_isAffineHom]
    exact @MorphismProperty.DescendsAlong.inf Scheme.{0} inferInstance
      (@IsProper) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) (@IsAffineHom) hproper haffine
  have hprojective := ProjSpace.isPullback_map K E N
  have hfpqc : ((@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})) (ProjSpace.map K E N) :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hprojective.flip hsurj,
       MorphismProperty.of_isPullback (P := @Flat) hprojective.flip hflat⟩,
       MorphismProperty.of_isPullback (P := @QuasiCompact) hprojective.flip inferInstance⟩
  exact ⟨Q, hQσ, MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsquare'.flip hfpqc hfinite,
    hsquare'⟩

private theorem exists_pullback_tower_comparison
    {A S T U : Scheme.{0}} (f : A ⟶ S) (u : T ⟶ S) (v : U ⟶ T) (w : U ⟶ S)
    (hw : v ≫ u = w) :
    ∃ c : Limits.pullback f w ⟶ Limits.pullback f u,
      c ≫ Limits.pullback.fst f u = Limits.pullback.fst f w ∧
      c ≫ Limits.pullback.snd f u = Limits.pullback.snd f w ≫ v ∧
      IsPullback c (Limits.pullback.snd f w) (Limits.pullback.snd f u) v := by
  let c := Limits.pullback.lift (Limits.pullback.fst f w) (Limits.pullback.snd f w ≫ v)
    (by rw [Category.assoc, hw]; exact Limits.pullback.condition)
  have hfst : c ≫ Limits.pullback.fst f u = Limits.pullback.fst f w := Limits.pullback.lift_fst _ _ _
  have hsnd : c ≫ Limits.pullback.snd f u = Limits.pullback.snd f w ≫ v := Limits.pullback.lift_snd _ _ _
  refine ⟨c, hfst, hsnd, ?_⟩
  have houter : IsPullback (c ≫ Limits.pullback.fst f u) (Limits.pullback.snd f w) f (v ≫ u) := by
    rw [hfst, hw]
    exact IsPullback.of_hasPullback f w
  exact houter.of_right hsnd (IsPullback.of_hasPullback f u)

/-- Invertible modules and their chosen finite section tuples descend along the
finite intermediate fields of the algebraic closure of the rational numbers. -/
theorem _root_.solution {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of ℚ))
    (hA : AbelianSchemePropertyBundle ℚ f) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ F)
      (𝓛 : (CategoryTheory.Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap ℚ ↥F)))).Modules) (N : ℕ)
      (P : 𝓛.ProjPresentation (CategoryTheory.Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap ℚ ↥F)))) N),
      Scheme.Modules.IsInvertible 𝓛 ∧ IsFinite P.toProj := by
  classical
  haveI := hA.proper
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let b := Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
  let B := Limits.pullback f b
  let g : B ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)) := Limits.pullback.snd f b
  have hB := hA.of_isPullback (IsPullback.of_hasPullback f b)
  obtain ⟨M, hM, N, P, hP⟩ := GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections (AlgebraicClosure ℚ) g hB
  obtain ⟨F₀, hF₀, M₀, hM₀, hcmp₀⟩ :=
    exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic ℚ (AlgebraicClosure ℚ) f M hM
  letI := hF₀
  let u₀ := Spec.map (CommRingCat.ofHom (algebraMap ℚ F₀))
  let v₀ := Spec.map (CommRingCat.ofHom (algebraMap F₀ (AlgebraicClosure ℚ)))
  have hw₀ : v₀ ≫ u₀ = b := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  obtain ⟨c₀, hc₀fst, hc₀snd, hc₀⟩ := exists_pullback_tower_comparison f u₀ v₀ b hw₀
  obtain ⟨e₀⟩ := hcmp₀ c₀ hc₀fst hc₀snd
  obtain ⟨P₀, hP₀, hP₀σ⟩ := P.exists_of_iso e₀.symm
  have hP₀finite : IsFinite P₀.toProj := by rw [hP₀]; exact hP
  let I := {F : IntermediateField ℚ (AlgebraicClosure ℚ) // FiniteDimensional ℚ F ∧ F₀ ≤ F}
  let i₀ : I := ⟨F₀, hF₀, le_rfl⟩
  let G : I → Type := fun i => ↥i.1
  let φ : ∀ i j : I, i ≤ j → G i →+* G j := fun _ _ h => (IntermediateField.inclusion h).toRingHom
  let ψ : ∀ i : I, G i →+* AlgebraicClosure ℚ := fun i => algebraMap i.1 (AlgebraicClosure ℚ)
  letI : Nonempty I := ⟨i₀⟩
  letI : ∀ i, CommRing (G i) := fun i => inferInstanceAs (CommRing i.1)
  letI : DirectedSystem G (fun i j h => ⇑(φ i j h)) :=
    { map_self := by intros; rfl
      map_map := by intros; rfl }
  have hjoin : ∀ i j : I, FiniteDimensional ℚ ↥(i.1 ⊔ j.1) := by
    intro i j
    letI := i.2.1
    letI := j.2.1
    exact IntermediateField.finiteDimensional_sup i.1 j.1
  letI : IsDirected I (· ≤ ·) := ⟨fun i j => by
    refine ⟨⟨i.1 ⊔ j.1, hjoin i j, i.2.2.trans le_sup_left⟩, ?_, ?_⟩
    · change i.1 ≤ i.1 ⊔ j.1
      exact le_sup_left
    · change j.1 ≤ i.1 ⊔ j.1
      exact le_sup_right⟩
  have hlim : IsDirectLimit (fun i j h => ⇑(φ i j h)) (fun i => ⇑(ψ i)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      let E := IntermediateField.adjoin ℚ {x}
      have hE : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral x)
      let j : I := ⟨F₀ ⊔ E, by
        letI := hE
        exact IntermediateField.finiteDimensional_sup F₀ E, le_sup_left⟩
      refine ⟨j, ⟨x, ?_⟩, rfl⟩
      change x ∈ F₀ ⊔ E
      apply (show E ≤ F₀ ⊔ E from le_sup_right)
      exact IntermediateField.mem_adjoin_simple_self ℚ x
    · intro i j x y hxy
      refine ⟨⟨i.1 ⊔ j.1, hjoin i j, i.2.2.trans le_sup_left⟩, ?_, ?_, ?_⟩
      · change i.1 ≤ i.1 ⊔ j.1
        exact le_sup_left
      · change j.1 ≤ i.1 ⊔ j.1
        exact le_sup_right
      · exact Subtype.ext hxy
    · intro i j hij x
      rfl
  haveI : QuasiCompact (Limits.pullback.snd f u₀) := inferInstance
  haveI : QuasiSeparated (Limits.pullback.snd f u₀) := inferInstance
  obtain ⟨j, hij, τ, hτ⟩ := IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit
    φ ψ hlim i₀ (Limits.pullback.snd f u₀) c₀ g hc₀ M₀ hM₀ P₀.σ
  let u := Spec.map (CommRingCat.ofHom (φ i₀ j hij))
  let v := Spec.map (CommRingCat.ofHom (ψ j))
  have hw : v ≫ u = v₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨c, hcfst, hcsnd, hc⟩ := exists_pullback_tower_comparison
    (Limits.pullback.snd f u₀) u v v₀ hw
  let cB := hc₀.isoPullback.hom ≫ c
  have hcBfst : cB ≫ Limits.pullback.fst (Limits.pullback.snd f u₀) u = c₀ := by
    rw [Category.assoc, hcfst, hc₀.isoPullback_hom_fst]
  have hcBsnd : cB ≫ Limits.pullback.snd (Limits.pullback.snd f u₀) u = g ≫ v := by
    rw [Category.assoc, hcsnd, ← Category.assoc, hc₀.isoPullback_hom_snd]
  have hcB : IsPullback cB g (Limits.pullback.snd (Limits.pullback.snd f u₀) u) v := by
    have houter : IsPullback
        (cB ≫ Limits.pullback.fst (Limits.pullback.snd f u₀) u)
        g (Limits.pullback.snd f u₀) (v ≫ u) := by
      rw [hcBfst, hw]
      exact hc₀
    exact houter.of_right hcBsnd (IsPullback.of_hasPullback _ _)
  obtain ⟨eτ, heτ⟩ := hτ cB hcBfst hcBsnd
  obtain ⟨Pτ, hPτmap, hPτσ⟩ := P₀.exists_of_iso eτ.symm
  have hPτfinite : IsFinite Pτ.toProj := by rw [hPτmap]; exact hP₀finite
  have hPτsections : ∀ i, Pτ.σ i =
      (((Scheme.Modules.pullbackPushforwardAdjunction cB).unit.app _).app ⊤) (τ i) := by
    intro i
    rw [hPτσ i, ← heτ i]
    change (eτ.hom ≫ eτ.inv).app ⊤ _ = _
    rw [Iso.hom_inv_id]
    rfl
  obtain ⟨Q, hQσ, hQfinite, hQsquare⟩ := exists_finite_projPresentation_of_descended_sections
    (Limits.pullback.snd (Limits.pullback.snd f u₀) u) g cB hcB
    _ (hM₀.pullback _) Pτ hPτfinite τ hPτsections
  let uj := Spec.map (CommRingCat.ofHom (algebraMap ℚ j.1))
  have hwj : u ≫ u₀ = uj := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨d, hdfst, hdsnd, hd⟩ := exists_pullback_tower_comparison f u₀ u uj hwj
  let e := hd.isoPullback
  obtain ⟨R, hRσ, hRmap⟩ := Q.exists_projPresentation_pullback_sigma_eq_toProj_eq e.hom
  have hRbase : e.hom ≫ Limits.pullback.snd (Limits.pullback.snd f u₀) u = Limits.pullback.snd f uj :=
    hd.isoPullback_hom_snd
  have hRfinite : IsFinite R.toProj := by
    rw [hRmap]
    letI := hQfinite
    infer_instance
  let MF := (Scheme.Modules.pullback e.hom).obj
    ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f u₀) u)).obj M₀)
  refine ⟨j.1, j.2.1, MF, N, ?_⟩
  have hresult : ∃ S : MF.ProjPresentation
        (e.hom ≫ Limits.pullback.snd (Limits.pullback.snd f u₀) u) N,
      IsInvertible MF ∧ IsFinite S.toProj :=
    ⟨R, (hM₀.pullback _).pullback _, hRfinite⟩
  exact Eq.mp (congrArg
    (fun t : Limits.pullback f uj ⟶ Spec (CommRingCat.of j.1) =>
      ∃ S : MF.ProjPresentation t N, IsInvertible MF ∧ IsFinite S.toProj) hRbase) hresult

end AlgebraicGeometry.Scheme.Modules
