-- Prove2me | solution 1 for AlgebraicGeometry.exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c0a04780-28e3-5702-9195-93d0feaddb64

import Mathlib
import Theorems.Thm_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

namespace SchemeSpread

private noncomputable abbrev _root_.SchemeSpread.ι (F K : Type) [CommRing F] [CommRing K] [Algebra F K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F K))

p2m_export "SchemeSpread" "ι"
section Tower

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem ι_comp (L : IntermediateField F K) : ι L K ≫ ι F L = ι F K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq F L K]

scoped instance surjective_ι : Surjective (ι F K) := by
  refine ⟨fun x => ?_⟩
  haveI : Subsingleton ↥(Spec (CommRingCat.of F)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum F))
  exact ⟨(⊥ : PrimeSpectrum K), Subsingleton.elim _ _⟩

example (L : IntermediateField F K) (L' : IntermediateField L K)
    (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Spec (CommRingCat.of L')) : X₀ ⟶ Spec (CommRingCat.of (L'.restrictScalars F)) := f₀

example (L : IntermediateField F K) (L' : IntermediateField L K) : ι (L'.restrictScalars F) K = ι L' K := rfl

theorem finiteDimensional_restrictScalars (L : IntermediateField F K) (L' : IntermediateField L K)
    [FiniteDimensional F L] [FiniteDimensional L L'] : FiniteDimensional F (L'.restrictScalars F) := by
  have : FiniteDimensional F L' := FiniteDimensional.trans F L L'
  exact this

end Tower

structure Model (F K : Type) [Field F] [Field K] [Algebra F K] (Z : Scheme.{0}) (fZ : Z ⟶ Spec (CommRingCat.of K)) where
  X₀ : Scheme.{0}
  f₀ : X₀ ⟶ Spec (CommRingCat.of F)
  qc : CompactSpace X₀
  qs : QuasiSeparatedSpace X₀
  lft : LocallyOfFiniteType f₀
  g : Z ⟶ X₀
  pb : IsPullback g fZ f₀ (ι F K)

namespace Model

variable {F K : Type} [Field F] [Field K] [Algebra F K] {Z : Scheme.{0}} {fZ : Z ⟶ Spec (CommRingCat.of K)}

section BaseChange

variable (m : Model F K Z fZ) (L : IntermediateField F K)

theorem w_baseChange : m.g ≫ m.f₀ = (fZ ≫ ι L K) ≫ ι F L := by
  rw [Category.assoc, ι_comp]; exact m.pb.w

noncomputable def gL : Z ⟶ pullback m.f₀ (ι F L) :=
  pullback.lift m.g (fZ ≫ ι L K) (m.w_baseChange L)

@[reassoc (attr := simp)]
theorem gL_fst : m.gL L ≫ pullback.fst m.f₀ (ι F L) = m.g := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem gL_snd : m.gL L ≫ pullback.snd m.f₀ (ι F L) = fZ ≫ ι L K := pullback.lift_snd _ _ _

theorem isPullback_gL : IsPullback (m.gL L) fZ (pullback.snd m.f₀ (ι F L)) (ι L K) :=
  IsPullback.of_right (by simpa only [gL_fst, ι_comp] using m.pb) (m.gL_snd L) (IsPullback.of_hasPullback _ _)

@[reducible] noncomputable def baseChange : Model L K Z fZ where
  X₀ := pullback m.f₀ (ι F L)
  f₀ := pullback.snd m.f₀ (ι F L)
  qc := by
    haveI := m.qc
    haveI : IsAffineHom (ι F L) := inferInstance
    infer_instance
  qs := by
    haveI := m.qs
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst m.f₀ (ι F L))
  lft := by haveI := m.lft; infer_instance
  g := m.gL L
  pb := m.isPullback_gL L

@[scoped simp] theorem baseChange_X₀ : (m.baseChange L).X₀ = pullback m.f₀ (ι F L) := rfl
@[scoped simp] theorem baseChange_f₀ : (m.baseChange L).f₀ = pullback.snd m.f₀ (ι F L) := rfl
@[scoped simp] theorem baseChange_g : (m.baseChange L).g = m.gL L := rfl

theorem gL_preimage (W : m.X₀.Opens) :
    m.gL L ⁻¹ᵁ (pullback.fst m.f₀ (ι F L) ⁻¹ᵁ W) = m.g ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, gL_fst]

theorem baseChange_g_preimage (W : m.X₀.Opens) :
    (m.baseChange L).g ⁻¹ᵁ (pullback.fst m.f₀ (ι F L) ⁻¹ᵁ W) = m.g ⁻¹ᵁ W :=
  m.gL_preimage L W

end BaseChange

end Model
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Inputs

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
  {Z : Scheme.{0}} {fZ : Z ⟶ Spec (CommRingCat.of K)}

theorem exists_open_descends (m : Model F K Z fZ) (U : Z.Opens) (hU : IsCompact (U : Set Z)) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L) (V : (m.baseChange L).X₀.Opens),
      IsCompact (V : Set (m.baseChange L).X₀) ∧ (m.baseChange L).g ⁻¹ᵁ V = U := by
  let e := m.pb.isoPullback
  have hU' : IsCompact ((e.inv ⁻¹ᵁ U : (pullback m.f₀ (ι F K)).Opens) : Set ↥(pullback m.f₀ (ι F K))) :=
    QuasiCompact.isCompact_preimage (f := e.inv) (U : Set Z) U.isOpen hU
  obtain ⟨L, hL, hι, V, hVc, hV⟩ :=
    AlgebraicGeometry.exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic
      F K m.X₀ m.f₀ (e.inv ⁻¹ᵁ U) hU'
  refine ⟨L, hL, V, hVc, ?_⟩
  have hg : (m.baseChange L).g = e.hom ≫ pullback.map m.f₀ (ι F K) m.f₀ (ι F L) (𝟙 m.X₀) (ι L K) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; simp [e]
    · rw [Category.assoc, pullback.lift_snd]; simp [e]
  rw [hg, Scheme.Hom.comp_preimage, hV, ← Scheme.Hom.comp_preimage, Iso.hom_inv_id, Scheme.Hom.id_preimage]

theorem exists_iso_descends (m n : Model F K Z fZ) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L) (e₀ : (m.baseChange L).X₀ ≅ (n.baseChange L).X₀),
      e₀.hom ≫ (n.baseChange L).f₀ = (m.baseChange L).f₀ ∧ (n.baseChange L).g = (m.baseChange L).g ≫ e₀.hom := by
  haveI := m.qc; haveI := m.qs; haveI := m.lft; haveI := n.qc; haveI := n.qs; haveI := n.lft
  let eX := m.pb.isoPullback
  let eY := n.pb.isoPullback
  let e : pullback m.f₀ (ι F K) ≅ pullback n.f₀ (ι F K) := eX.symm ≪≫ eY
  have he : e.hom ≫ pullback.snd n.f₀ (ι F K) = pullback.snd m.f₀ (ι F K) := by
    simp [e, eX, eY]
  obtain ⟨L, hL, e₀, hι, h1, h2⟩ :=
    AlgebraicGeometry.exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic
      F K m.X₀ n.X₀ m.f₀ n.f₀ e he
  refine ⟨L, hL, e₀, h1, ?_⟩
  have hgm : (m.baseChange L).g = eX.hom ≫ pullback.map m.f₀ (ι F K) m.f₀ (ι F L) (𝟙 m.X₀) (ι L K) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; simp [eX]
    · rw [Category.assoc, pullback.lift_snd]; simp [eX]
  have hgn : (n.baseChange L).g = eY.hom ≫ pullback.map n.f₀ (ι F K) n.f₀ (ι F L) (𝟙 n.X₀) (ι L K) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; simp [eY]
    · rw [Category.assoc, pullback.lift_snd]; simp [eY]
  have : eY.hom = eX.hom ≫ e.hom := by simp [e]
  rw [hgn, this, Category.assoc, h2, hgm, Category.assoc]

end Inputs
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

namespace Model

variable {F K : Type} [Field F] [Field K] [Algebra F K] {Z : Scheme.{0}} {fZ : Z ⟶ Spec (CommRingCat.of K)}
  (m : Model F K Z fZ) {L L' : IntermediateField F K}

noncomputable abbrev incl (h : L ≤ L') : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)

theorem incl_comp_ι (h : L ≤ L') : incl h ≫ ι F L = ι F L' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem ι_comp_incl (h : L ≤ L') : ι L' K ≫ incl h = ι L K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

scoped instance isAffineHom_incl (h : L ≤ L') : IsAffineHom (incl (F := F) (K := K) h) := inferInstance

noncomputable def transition (h : L ≤ L') : (m.baseChange L').X₀ ⟶ (m.baseChange L).X₀ :=
  pullback.map m.f₀ (ι F L') m.f₀ (ι F L) (𝟙 _) (incl h) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, incl_comp_ι])

@[reassoc (attr := simp)]
theorem transition_fst (h : L ≤ L') :
    m.transition h ≫ pullback.fst m.f₀ (ι F L) = pullback.fst m.f₀ (ι F L') := by
  rw [transition, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem transition_snd (h : L ≤ L') :
    m.transition h ≫ pullback.snd m.f₀ (ι F L) = pullback.snd m.f₀ (ι F L') ≫ incl h := by
  rw [transition, pullback.lift_snd]

@[reassoc (attr := simp)]
theorem gL_transition (h : L ≤ L') : m.gL L' ≫ m.transition h = m.gL L := by
  apply pullback.hom_ext
  · rw [Category.assoc, transition_fst, gL_fst, gL_fst]
  · rw [Category.assoc, transition_snd, gL_snd_assoc, gL_snd, ι_comp_incl]

theorem isPullback_transition (h : L ≤ L') :
    IsPullback (m.transition h) (pullback.snd m.f₀ (ι F L')) (pullback.snd m.f₀ (ι F L)) (incl h) :=
  IsPullback.of_right (by simpa only [transition_fst, incl_comp_ι] using (IsPullback.of_hasPullback m.f₀ (ι F L')))
    (m.transition_snd h) (IsPullback.of_hasPullback _ _)

scoped instance quasiCompact_transition (h : L ≤ L') : QuasiCompact (m.transition h) :=
  MorphismProperty.of_isPullback (m.isPullback_transition h).flip inferInstance

end Model
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section TwoOpens

variable {X : Scheme.{0}} (U V : X.Opens)

theorem range_ι_preimage_ι : Set.range ((U.ι ⁻¹ᵁ V).ι ≫ U.ι) = (U : Set X) ∩ (V : Set X) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨((U.ι ⁻¹ᵁ V).ι y).2, y.2⟩
  · rintro ⟨hU, hV⟩
    exact ⟨⟨⟨x, hU⟩, hV⟩, rfl⟩

noncomputable def crossing : (U.ι ⁻¹ᵁ V).toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι ((U.ι ⁻¹ᵁ V).ι ≫ U.ι) (by
    rw [range_ι_preimage_ι, Scheme.Opens.range_ι]
    exact Set.inter_subset_right)

@[reassoc (attr := simp)]
theorem crossing_ι : crossing U V ≫ V.ι = (U.ι ⁻¹ᵁ V).ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _

scoped instance isOpenImmersion_crossing : IsOpenImmersion (crossing U V) := by
  haveI : IsOpenImmersion (crossing U V ≫ V.ι) := by rw [crossing_ι]; infer_instance
  exact IsOpenImmersion.of_comp (crossing U V) V.ι

theorem opensRange_crossing : (crossing U V).opensRange = V.ι ⁻¹ᵁ U := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change V.ι (crossing U V y) ∈ U
    rw [← Scheme.Hom.comp_apply, crossing_ι]
    exact ((U.ι ⁻¹ᵁ V).ι y).2
  · intro hx
    refine ⟨⟨⟨V.ι x, hx⟩, x.2⟩, ?_⟩
    apply V.ι.injective
    rw [← Scheme.Hom.comp_apply, crossing_ι]
    rfl

theorem isPullback_crossing : IsPullback (U.ι ⁻¹ᵁ V).ι (crossing U V) U.ι V.ι :=
  (IsOpenImmersion.isPullback (crossing U V) (U.ι ⁻¹ᵁ V).ι V.ι U.ι (crossing_ι U V).symm
    (by rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι])).flip

theorem isCompact_ι_preimage [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X)) :
    IsCompact ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U) := by
  have h : IsCompact ((U : Set X) ∩ V) := QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen hU V.isOpen hV
  rw [U.ι.isOpenEmbedding.isInducing.isCompact_iff]
  convert h
  rw [← range_ι_preimage_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]

end TwoOpens
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Phases

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
  {X : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of K)} (U V : X.Opens)

theorem phase1 [QuasiSeparatedSpace X] (hUc : IsCompact (U : Set X)) (hVc : IsCompact (V : Set X))
    (mU : Model F K U (U.ι ≫ fX)) (mV : Model F K V (V.ι ≫ fX)) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L)
      (mU' : Model L K U (U.ι ≫ fX)) (mV' : Model L K V (V.ι ≫ fX))
      (WU : mU'.X₀.Opens) (WV : mV'.X₀.Opens),
      IsCompact (WU : Set mU'.X₀) ∧ IsCompact (WV : Set mV'.X₀) ∧
      mU'.g ⁻¹ᵁ WU = U.ι ⁻¹ᵁ V ∧ mV'.g ⁻¹ᵁ WV = V.ι ⁻¹ᵁ U := by
  obtain ⟨L₁, hL₁, WU₁, hWU₁c, hWU₁⟩ := exists_open_descends mU (U.ι ⁻¹ᵁ V) (isCompact_ι_preimage U V hUc hVc)
  obtain ⟨L₂, hL₂, WV₁, hWV₁c, hWV₁⟩ := exists_open_descends mV (V.ι ⁻¹ᵁ U) (isCompact_ι_preimage V U hVc hUc)
  haveI := hL₁
  haveI := hL₂
  refine ⟨L₁ ⊔ L₂, inferInstance, mU.baseChange (L₁ ⊔ L₂), mV.baseChange (L₁ ⊔ L₂),
    mU.transition le_sup_left ⁻¹ᵁ WU₁, mV.transition le_sup_right ⁻¹ᵁ WV₁, ?_, ?_, ?_, ?_⟩
  · exact QuasiCompact.isCompact_preimage (f := mU.transition le_sup_left) _ WU₁.isOpen hWU₁c
  · exact QuasiCompact.isCompact_preimage (f := mV.transition le_sup_right) _ WV₁.isOpen hWV₁c
  · rw [← hWU₁, Model.baseChange_g, Model.baseChange_g, ← Scheme.Hom.comp_preimage, Model.gL_transition]
  · rw [← hWV₁, Model.baseChange_g, Model.baseChange_g, ← Scheme.Hom.comp_preimage, Model.gL_transition]

noncomputable def modelCapLeft [QuasiSeparatedSpace X] (mU : Model F K U (U.ι ≫ fX)) (WU : mU.X₀.Opens)
    (hWUc : IsCompact (WU : Set mU.X₀)) (hWU : mU.g ⁻¹ᵁ WU = U.ι ⁻¹ᵁ V) :
    Model F K (U.ι ⁻¹ᵁ V) ((U.ι ⁻¹ᵁ V).ι ≫ U.ι ≫ fX) where
  X₀ := WU
  f₀ := WU.ι ≫ mU.f₀
  qc := isCompact_iff_compactSpace.mp hWUc
  qs := by haveI := mU.qs; exact WU.ι.isOpenEmbedding.quasiSeparatedSpace
  lft := by haveI := mU.lft; infer_instance
  g := mU.g.resLE WU (U.ι ⁻¹ᵁ V) (by rw [hWU])
  pb := by
    have sq : IsPullback (mU.g.resLE WU (U.ι ⁻¹ᵁ V) (by rw [hWU])) (U.ι ⁻¹ᵁ V).ι WU.ι mU.g :=
      IsOpenImmersion.isPullback _ _ _ _ (by rw [Scheme.Hom.resLE_comp_ι])
        (by rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, hWU])
    exact sq.paste_vert mU.pb

omit [Algebra.IsAlgebraic F K] in
theorem range_crossing_comp_subset (mV : Model F K V (V.ι ≫ fX)) (WV : mV.X₀.Opens)
    (hWV : mV.g ⁻¹ᵁ WV = V.ι ⁻¹ᵁ U) : Set.range (crossing U V ≫ mV.g) ⊆ Set.range WV.ι := by
  rintro _ ⟨y, rfl⟩
  have hy : crossing U V y ∈ mV.g ⁻¹ᵁ WV := by rw [hWV, ← opensRange_crossing]; exact ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact hy

noncomputable def modelCapRight [QuasiSeparatedSpace X] (mV : Model F K V (V.ι ≫ fX)) (WV : mV.X₀.Opens)
    (hWVc : IsCompact (WV : Set mV.X₀)) (hWV : mV.g ⁻¹ᵁ WV = V.ι ⁻¹ᵁ U) :
    Model F K (U.ι ⁻¹ᵁ V) ((U.ι ⁻¹ᵁ V).ι ≫ U.ι ≫ fX) where
  X₀ := WV
  f₀ := WV.ι ≫ mV.f₀
  qc := isCompact_iff_compactSpace.mp hWVc
  qs := by haveI := mV.qs; exact WV.ι.isOpenEmbedding.quasiSeparatedSpace
  lft := by haveI := mV.lft; infer_instance
  g := IsOpenImmersion.lift WV.ι (crossing U V ≫ mV.g) (range_crossing_comp_subset U V mV WV hWV)
  pb := by
    have sq : IsPullback (IsOpenImmersion.lift WV.ι (crossing U V ≫ mV.g) (range_crossing_comp_subset U V mV WV hWV))
        (crossing U V) WV.ι mV.g :=
      IsOpenImmersion.isPullback _ _ _ _ (by rw [IsOpenImmersion.lift_fac])
        (by rw [Scheme.Opens.opensRange_ι, opensRange_crossing, hWV])
    have := sq.paste_vert mV.pb
    rwa [crossing_ι_assoc] at this

theorem phase2 [QuasiSeparatedSpace X] (mU : Model F K U (U.ι ≫ fX)) (mV : Model F K V (V.ι ≫ fX))
    (WU : mU.X₀.Opens) (WV : mV.X₀.Opens) (hWUc : IsCompact (WU : Set mU.X₀)) (hWVc : IsCompact (WV : Set mV.X₀))
    (hWU : mU.g ⁻¹ᵁ WU = U.ι ⁻¹ᵁ V) (hWV : mV.g ⁻¹ᵁ WV = V.ι ⁻¹ᵁ U) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L)
      (W₀ : Scheme.{0}) (iU : W₀ ⟶ (mU.baseChange L).X₀) (iV : W₀ ⟶ (mV.baseChange L).X₀)
      (_ : IsOpenImmersion iU) (_ : IsOpenImmersion iV) (gW : (U.ι ⁻¹ᵁ V).toScheme ⟶ W₀),
      iU ≫ (mU.baseChange L).f₀ = iV ≫ (mV.baseChange L).f₀ ∧
      (mU.baseChange L).g ⁻¹ᵁ iU.opensRange ≤ U.ι ⁻¹ᵁ V ∧
      (mV.baseChange L).g ⁻¹ᵁ iV.opensRange ≤ V.ι ⁻¹ᵁ U ∧
      gW ≫ iU = (U.ι ⁻¹ᵁ V).ι ≫ (mU.baseChange L).g ∧
      gW ≫ iV = crossing U V ≫ (mV.baseChange L).g := by
  let mWU := modelCapLeft U V mU WU hWUc hWU
  let mWV := modelCapRight U V mV WV hWVc hWV
  obtain ⟨L, hL, e₀, he₀f, he₀g⟩ := exists_iso_descends mWU mWV

  let jU : (mWU.baseChange L).X₀ ⟶ (mU.baseChange L).X₀ :=
    pullback.map mWU.f₀ (ι F L) mU.f₀ (ι F L) WU.ι (𝟙 _) (𝟙 _) ((Category.comp_id _).trans rfl)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  let jV : (mWV.baseChange L).X₀ ⟶ (mV.baseChange L).X₀ :=
    pullback.map mWV.f₀ (ι F L) mV.f₀ (ι F L) WV.ι (𝟙 _) (𝟙 _) ((Category.comp_id _).trans rfl)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  haveI hWUι : IsOpenImmersion (WU.ι : mWU.X₀ ⟶ mU.X₀) := inferInstanceAs (IsOpenImmersion WU.ι)
  haveI hWVι : IsOpenImmersion (WV.ι : mWV.X₀ ⟶ mV.X₀) := inferInstanceAs (IsOpenImmersion WV.ι)
  have hjU : IsOpenImmersion jU :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) hWUι inferInstance rfl (Category.id_comp _).symm
  have hjV : IsOpenImmersion jV :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) hWVι inferInstance rfl (Category.id_comp _).symm
  have jU_fst : jU ≫ pullback.fst mU.f₀ (ι F L) = pullback.fst mWU.f₀ (ι F L) ≫ WU.ι := pullback.lift_fst _ _ _
  have jU_snd : jU ≫ pullback.snd mU.f₀ (ι F L) = pullback.snd mWU.f₀ (ι F L) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have jV_fst : jV ≫ pullback.fst mV.f₀ (ι F L) = pullback.fst mWV.f₀ (ι F L) ≫ WV.ι := pullback.lift_fst _ _ _
  have jV_snd : jV ≫ pullback.snd mV.f₀ (ι F L) = pullback.snd mWV.f₀ (ι F L) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  haveI : IsOpenImmersion (e₀.hom ≫ jV) := by haveI := hjV; infer_instance
  refine ⟨L, hL, (mWU.baseChange L).X₀, jU, e₀.hom ≫ jV, hjU, inferInstance, (mWU.baseChange L).g, ?_, ?_, ?_, ?_, ?_⟩
  ·
    change jU ≫ pullback.snd mU.f₀ (ι F L) = (e₀.hom ≫ jV) ≫ pullback.snd mV.f₀ (ι F L)
    rw [jU_snd, Category.assoc, jV_snd]
    exact he₀f.symm
  ·
    intro x hx
    obtain ⟨w, hw⟩ := hx
    have : (mU.baseChange L).g x ∈ pullback.fst mU.f₀ (ι F L) ⁻¹ᵁ WU := by
      change pullback.fst mU.f₀ (ι F L) ((mU.baseChange L).g x) ∈ WU
      have e1 : (jU ≫ pullback.fst mU.f₀ (ι F L)) w = (pullback.fst mWU.f₀ (ι F L) ≫ WU.ι) w := by rw [jU_fst]
      simp only [Scheme.Hom.comp_apply] at e1
      rw [← hw, e1]
      exact (pullback.fst mWU.f₀ (ι F L) w).2
    rw [← hWU, ← mU.baseChange_g_preimage L]
    exact this
  ·
    intro x hx
    obtain ⟨w, hw⟩ := hx
    have : (mV.baseChange L).g x ∈ pullback.fst mV.f₀ (ι F L) ⁻¹ᵁ WV := by
      change pullback.fst mV.f₀ (ι F L) ((mV.baseChange L).g x) ∈ WV
      have e1 : ((e₀.hom ≫ jV) ≫ pullback.fst mV.f₀ (ι F L)) w = (e₀.hom ≫ pullback.fst mWV.f₀ (ι F L) ≫ WV.ι) w := by
        rw [Category.assoc, jV_fst]
      rw [← hw]
      simp only [Scheme.Hom.comp_apply] at e1 ⊢
      rw [e1]
      exact (pullback.fst mWV.f₀ (ι F L) (e₀.hom w)).2
    rw [← hWV, ← mV.baseChange_g_preimage L]
    exact this
  ·
    apply pullback.hom_ext
    · rw [Category.assoc, jU_fst, Category.assoc, Model.baseChange_g, Model.baseChange_g, Model.gL_fst_assoc,
        Model.gL_fst]
      exact Scheme.Hom.resLE_comp_ι _ _
    · rw [Category.assoc, jU_snd, Category.assoc, Model.baseChange_g, Model.baseChange_g, Model.gL_snd, Model.gL_snd,
        Category.assoc]
  ·
    have hg : (mWU.baseChange L).g ≫ e₀.hom = (mWV.baseChange L).g := he₀g.symm
    rw [← Category.assoc, hg]
    apply pullback.hom_ext
    · rw [Category.assoc, jV_fst, Category.assoc, Model.baseChange_g, Model.baseChange_g, Model.gL_fst_assoc,
        Model.gL_fst]
      exact IsOpenImmersion.lift_fac WV.ι (crossing U V ≫ mV.g) (range_crossing_comp_subset U V mV WV hWV)
    · rw [Category.assoc, jV_snd, Category.assoc, Model.baseChange_g, Model.baseChange_g, Model.gL_snd, Model.gL_snd]
      simp only [Category.assoc, crossing_ι_assoc]

end Phases
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Pushout

variable {W A B : Scheme.{0}} (iU : W ⟶ A) (iV : W ⟶ B) [IsOpenImmersion iU] [IsOpenImmersion iV]

scoped instance span_map_isOpenImmersion {i j : WalkingSpan} (u : i ⟶ j) : IsOpenImmersion ((span iU iV).map u) := by
  rcases u with _ | (_ | _)
  · change IsOpenImmersion ((span iU iV).map (𝟙 _)); rw [CategoryTheory.Functor.map_id]; infer_instance
  · change IsOpenImmersion iU; infer_instance
  · change IsOpenImmersion iV; infer_instance

scoped instance hasPushout_of_isOpenImmersion : HasPushout iU iV := inferInstance

scoped instance isOpenImmersion_inl : IsOpenImmersion (pushout.inl iU iV) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span iU iV) WalkingSpan.left))

scoped instance isOpenImmersion_inr : IsOpenImmersion (pushout.inr iU iV) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span iU iV) WalkingSpan.right))

theorem exists_of_inl_eq_inr (a : A) (b : B) (h : pushout.inl iU iV a = pushout.inr iU iV b) :
    ∃ w, iU w = a ∧ iV w = b := by
  obtain ⟨k, fi, fj, x, hx1, hx2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span iU iV)).mp h
  rcases k with _ | (_ | _)
  · rcases fi with _ | _; rcases fj with _ | _; exact ⟨x, hx1, hx2⟩
  · rcases fj with _ | _
  · rcases fi with _ | _

theorem inl_or_inr (x : ↥(pushout iU iV)) : (∃ a, pushout.inl iU iV a = x) ∨ ∃ b, pushout.inr iU iV b = x := by
  obtain ⟨k, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span iU iV) x
  rcases k with _ | (_ | _)
  · left
    refine ⟨iU y, ?_⟩
    rw [← hy, ← colimit.w (span iU iV) WalkingSpan.Hom.fst, Scheme.Hom.comp_apply]
    rfl
  · left; exact ⟨y, hy⟩
  · right; exact ⟨y, hy⟩

noncomputable def pushoutCover : (pushout iU iV).OpenCover :=
  Scheme.Cover.mkOfCovers (J := Bool) (fun b => bif b then A else B)
    (fun b => match b with
      | true => pushout.inl iU iV
      | false => pushout.inr iU iV)
    (fun x => by
      rcases inl_or_inr iU iV x with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact ⟨true, a, ha⟩
      · exact ⟨false, b, hb⟩)
    (by
      rintro (_ | _)
      · exact isOpenImmersion_inr iU iV
      · exact isOpenImmersion_inl iU iV)

end Pushout
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

theorem quasiSeparatedSpace_of_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [Surjective f]
    [QuasiSeparatedSpace X] : QuasiSeparatedSpace Y := by
  refine ⟨fun A B hAo hAc hBo hBc => ?_⟩
  have h := QuasiSeparatedSpace.inter_isCompact (f ⁻¹' A) (f ⁻¹' B) (hAo.preimage f.continuous)
    (QuasiCompact.isCompact_preimage _ hAo hAc) (hBo.preimage f.continuous) (QuasiCompact.isCompact_preimage _ hBo hBc)
  have : A ∩ B = f '' (f ⁻¹' A ∩ f ⁻¹' B) := by
    rw [← Set.preimage_inter, Set.image_preimage_eq _ f.surjective]
  rw [this]
  exact h.image f.continuous

theorem compactSpace_of_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) [Surjective f] [CompactSpace X] : CompactSpace Y := by
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr f.surjective]
  exact isCompact_range f.continuous

section Phase3

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {X : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of K)} (U V : X.Opens)

theorem phase3 [CompactSpace X] [QuasiSeparatedSpace X] (hUV : U ⊔ V = ⊤)
    (mU : Model F K U (U.ι ≫ fX)) (mV : Model F K V (V.ι ≫ fX))
    (W₀ : Scheme.{0}) (iU : W₀ ⟶ mU.X₀) (iV : W₀ ⟶ mV.X₀) [IsOpenImmersion iU] [IsOpenImmersion iV]
    (gW : (U.ι ⁻¹ᵁ V).toScheme ⟶ W₀) (hf : iU ≫ mU.f₀ = iV ≫ mV.f₀)
    (hrU : mU.g ⁻¹ᵁ iU.opensRange ≤ U.ι ⁻¹ᵁ V) (hrV : mV.g ⁻¹ᵁ iV.opensRange ≤ V.ι ⁻¹ᵁ U)
    (hgU : gW ≫ iU = (U.ι ⁻¹ᵁ V).ι ≫ mU.g) (hgV : gW ≫ iV = crossing U V ≫ mV.g) :
    Nonempty (Model F K X fX) := by
  haveI := mU.qc; haveI := mU.qs; haveI := mU.lft; haveI := mV.qc; haveI := mV.qs; haveI := mV.lft

  let X₀ : Scheme.{0} := pushout iU iV
  let inl : mU.X₀ ⟶ X₀ := pushout.inl iU iV
  let inr : mV.X₀ ⟶ X₀ := pushout.inr iU iV
  let f₀ : X₀ ⟶ Spec (CommRingCat.of F) := pushout.desc mU.f₀ mV.f₀ hf
  have inl_f₀ : inl ≫ f₀ = mU.f₀ := pushout.inl_desc _ _ _
  have inr_f₀ : inr ≫ f₀ = mV.f₀ := pushout.inr_desc _ _ _
  have key : (U.ι ⁻¹ᵁ V).ι ≫ mU.g ≫ inl = crossing U V ≫ mV.g ≫ inr := by
    rw [← Category.assoc, ← hgU, Category.assoc, pushout.condition, ← Category.assoc, hgV, Category.assoc]

  let 𝒱 : X.OpenCover := X.openCoverOfIsOpenCover (fun b : Bool => bif b then U else V) (by
    change (⨆ b : Bool, (bif b then U else V)) = ⊤
    rw [← sup_eq_iSup]; exact hUV)
  let piece : ∀ b : Bool, (𝒱.X b ⟶ X₀) := fun b => match b with
    | true => mU.g ≫ inl
    | false => mV.g ≫ inr
  have hcompat : ∀ b c : Bool, pullback.fst (𝒱.f b) (𝒱.f c) ≫ piece b = pullback.snd (𝒱.f b) (𝒱.f c) ≫ piece c := by
    rintro (_ | _) (_ | _)
    · change pullback.fst V.ι V.ι ≫ mV.g ≫ inr = pullback.snd V.ι V.ι ≫ mV.g ≫ inr
      rw [fst_eq_snd_of_mono_eq]
    · change pullback.fst V.ι U.ι ≫ mV.g ≫ inr = pullback.snd V.ι U.ι ≫ mU.g ≫ inl
      have sq := (isPullback_crossing U V).flip
      rw [← cancel_epi sq.isoPullback.hom, sq.isoPullback_hom_fst_assoc, sq.isoPullback_hom_snd_assoc]
      exact key.symm
    · change pullback.fst U.ι V.ι ≫ mU.g ≫ inl = pullback.snd U.ι V.ι ≫ mV.g ≫ inr
      have sq := isPullback_crossing U V
      rw [← cancel_epi sq.isoPullback.hom, sq.isoPullback_hom_fst_assoc, sq.isoPullback_hom_snd_assoc]
      exact key
    · change pullback.fst U.ι U.ι ≫ mU.g ≫ inl = pullback.snd U.ι U.ι ≫ mU.g ≫ inl
      rw [fst_eq_snd_of_mono_eq]
  let g : X ⟶ X₀ := 𝒱.glueMorphisms piece hcompat
  have gU : U.ι ≫ g = mU.g ≫ inl := 𝒱.ι_glueMorphisms piece hcompat true
  have gV : V.ι ≫ g = mV.g ≫ inr := 𝒱.ι_glueMorphisms piece hcompat false
  have gU_apply : ∀ x : U, g (U.ι x) = inl (mU.g x) := fun x => by
    rw [← Scheme.Hom.comp_apply, gU, Scheme.Hom.comp_apply]
  have gV_apply : ∀ x : V, g (V.ι x) = inr (mV.g x) := fun x => by
    rw [← Scheme.Hom.comp_apply, gV, Scheme.Hom.comp_apply]

  have hpreU : g ⁻¹ᵁ inl.opensRange = U := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with hxU | hxV
      · exact hxU
      · have e1 : g x = inr (mV.g ⟨x, hxV⟩) := gV_apply ⟨x, hxV⟩
        obtain ⟨w, -, hw2⟩ := exists_of_inl_eq_inr iU iV a (mV.g ⟨x, hxV⟩) (ha.trans e1)
        exact hrV (show (⟨x, hxV⟩ : V) ∈ mV.g ⁻¹ᵁ iV.opensRange from ⟨w, hw2⟩)
    · intro hxU
      exact ⟨mU.g ⟨x, hxU⟩, (gU_apply ⟨x, hxU⟩).symm⟩
  have hpreV : g ⁻¹ᵁ inr.opensRange = V := by
    ext x
    constructor
    · rintro ⟨b, hb⟩
      have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with hxU | hxV
      · have e1 : g x = inl (mU.g ⟨x, hxU⟩) := gU_apply ⟨x, hxU⟩
        obtain ⟨w, hw1, -⟩ := exists_of_inl_eq_inr iU iV (mU.g ⟨x, hxU⟩) b (e1.symm.trans hb.symm)
        exact hrU (show (⟨x, hxU⟩ : U) ∈ mU.g ⁻¹ᵁ iU.opensRange from ⟨w, hw1⟩)
      · exact hxV
    · intro hxV
      exact ⟨mV.g ⟨x, hxV⟩, (gV_apply ⟨x, hxV⟩).symm⟩

  have sqU : IsPullback mU.g U.ι inl g :=
    IsOpenImmersion.isPullback _ _ _ _ gU (by rw [hpreU, Scheme.Opens.opensRange_ι])
  have sqV : IsPullback mV.g V.ι inr g :=
    IsOpenImmersion.isPullback _ _ _ _ gV (by rw [hpreV, Scheme.Opens.opensRange_ι])

  have H : IsPullback g fX f₀ (ι F K) := by
    refine Scheme.isPullback_of_openCover g fX f₀ (ι F K) (pushoutCover iU iV) ?_
    rintro (_ | _)
    · change IsPullback (pullback.snd g inr) (pullback.fst g inr ≫ fX) (inr ≫ f₀) (ι F K)
      rw [inr_f₀]
      refine mV.pb.of_iso sqV.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
      · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
      · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc]
    · change IsPullback (pullback.snd g inl) (pullback.fst g inl ≫ fX) (inl ≫ f₀) (ι F K)
      rw [inl_f₀]
      refine mU.pb.of_iso sqU.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
      · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
      · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc]

  haveI : Surjective g := MorphismProperty.of_isPullback H.flip inferInstance
  haveI : QuasiCompact g := MorphismProperty.of_isPullback H.flip inferInstance
  haveI hlft : LocallyOfFiniteType f₀ := by
    refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (pushoutCover iU iV) ?_
    rintro (_ | _)
    · change LocallyOfFiniteType (inr ≫ f₀); rw [inr_f₀]; infer_instance
    · change LocallyOfFiniteType (inl ≫ f₀); rw [inl_f₀]; infer_instance
  exact ⟨{ X₀ := X₀, f₀ := f₀, qc := compactSpace_of_surjective g, qs := quasiSeparatedSpace_of_surjective g,
           lft := hlft, g := g, pb := H }⟩

end Phase3
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Core

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
  {X : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of K)} (U V : X.Opens)

theorem glue_core [CompactSpace X] [QuasiSeparatedSpace X] (hUV : U ⊔ V = ⊤)
    (hUc : IsCompact (U : Set X)) (hVc : IsCompact (V : Set X))
    (mU : Model F K U (U.ι ≫ fX)) (mV : Model F K V (V.ι ≫ fX)) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L), Nonempty (Model L K X fX) := by
  obtain ⟨L₁, hL₁, mU₁, mV₁, WU, WV, hWUc, hWVc, hWU, hWV⟩ := phase1 U V hUc hVc mU mV
  haveI := hL₁
  haveI : Algebra.IsAlgebraic L₁ K := Algebra.IsAlgebraic.tower_top (K := F) L₁
  obtain ⟨L₂, hL₂, W₀, iU, iV, hiU, hiV, gW, hf, hrU, hrV, hgU, hgV⟩ :=
    phase2 U V mU₁ mV₁ WU WV hWUc hWVc hWU hWV
  haveI := hL₂
  haveI := hiU
  haveI := hiV
  obtain ⟨m⟩ := phase3 U V hUV _ _ W₀ iU iV gW hf hrU hrV hgU hgV
  exact ⟨L₂.restrictScalars F, finiteDimensional_restrictScalars L₁ L₂, ⟨m⟩⟩

end Core
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

structure Datum (k K : Type) [Field k] [Field K] [Algebra k K] (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of K)) where
  E : IntermediateField k K
  fd : FiniteDimensional k E
  X₀ : Scheme.{0}
  f₀ : X₀ ⟶ Spec (CommRingCat.of E)
  qc : CompactSpace X₀
  qs : QuasiSeparatedSpace X₀
  lft : LocallyOfFiniteType f₀
  g : X ⟶ X₀
  pb : IsPullback g fX f₀ (ι E K)

namespace Datum

variable {k K : Type} [Field k] [Field K] [Algebra k K] {X : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of K)}

def toModel (d : Datum k K X fX) : Model d.E K X fX :=
  { X₀ := d.X₀, f₀ := d.f₀, qc := d.qc, qs := d.qs, lft := d.lft, g := d.g, pb := d.pb }

def ofModel (E : IntermediateField k K) (hE : FiniteDimensional k E) (m : Model E K X fX) : Datum k K X fX :=
  { E := E, fd := hE, X₀ := m.X₀, f₀ := m.f₀, qc := m.qc, qs := m.qs, lft := m.lft, g := m.g, pb := m.pb }

theorem ι_comp_inclusion {E E' : IntermediateField k K} (h : E ≤ E') :
    ι E' K ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) = ι E K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

noncomputable def relevel (d : Datum k K X fX) (E' : IntermediateField k K) (h : d.E ≤ E')
    (hE' : FiniteDimensional k E') : Datum k K X fX := by
  let j : Spec (CommRingCat.of E') ⟶ Spec (CommRingCat.of d.E) :=
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)
  haveI := d.lft
  haveI := d.qc
  haveI := d.qs
  have w : d.g ≫ d.f₀ = (fX ≫ ι E' K) ≫ j := by
    rw [Category.assoc, ι_comp_inclusion h]
    exact d.pb.w
  refine
    { E := E'
      fd := hE'
      X₀ := pullback d.f₀ j
      f₀ := pullback.snd d.f₀ j
      qc := ?_
      qs := ?_
      lft := inferInstance
      g := pullback.lift d.g (fX ≫ ι E' K) w
      pb := ?_ }
  · haveI : IsAffineHom j := inferInstance
    infer_instance
  · exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst d.f₀ j)
  · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback d.f₀ j)
    rw [pullback.lift_fst, ι_comp_inclusion h]
    exact d.pb

end Datum
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Affine

variable {k K : Type} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

theorem affine_descends (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [LocallyOfFiniteType fX] :
    Nonempty (Datum k K X fX) := by
  classical

  let R : CommRingCat.{0} := Γ(X, ⊤)
  let φ : CommRingCat.of K ⟶ R := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ fX.appTop
  have hfX : fX = X.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hlft : LocallyOfFiniteType (Spec.map φ) := by
    have : Spec.map φ = X.isoSpec.inv ≫ fX := by rw [hfX, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlft
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hft
  obtain ⟨L, hL, A₀, _, _, hA₀, ⟨e⟩⟩ :=
    Algebra.exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic k K R

  let X₀ : Scheme.{0} := Spec (CommRingCat.of A₀)
  let f₀ : X₀ ⟶ Spec (CommRingCat.of L) := Spec.map (CommRingCat.ofHom (algebraMap L A₀))
  haveI : LocallyOfFiniteType f₀ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (RingHom.finiteType_algebraMap.mpr hA₀)

  have sq : IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := L) (A := K) (B := A₀)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := L) (A := K) (B := A₀))))
      f₀ (ι L K) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso L K A₀).symm ?_ ?_ |>.flip
    · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      change algebraMap K (K ⊗[L] A₀) (algebraMap L K x) = (Algebra.TensorProduct.includeRight (R := L) (A := K) (B := A₀))
        (algebraMap L A₀ x)
      rw [AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply L K (K ⊗[L] A₀) x).symm
    · exact pullbackSpecIso_inv_fst L K A₀
    · exact pullbackSpecIso_inv_snd L K A₀

  let u : X ⟶ Spec (CommRingCat.of (K ⊗[L] A₀)) :=
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)
  haveI : IsIso (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)) := by
    change IsIso (Scheme.Spec.map (e.toRingEquiv.toCommRingCatIso.hom.op))
    infer_instance
  haveI : IsIso u := IsIso.comp_isIso
  have hu : u ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := L) (A := K) (B := A₀))) = fX := by
    rw [hfX, Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    change e (algebraMap K (K ⊗[L] A₀) x) = φ.hom x
    rw [AlgEquiv.commutes]
    rfl
  let g : X ⟶ X₀ := u ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := L) (A := K) (B := A₀)).toRingHom)
  have pb : IsPullback g fX f₀ (ι L K) := by
    refine IsPullback.of_iso sq (asIso u).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [g]
    · simp [← hu]
    · simp
    · simp
  exact ⟨{ E := L, fd := hL, X₀ := X₀, f₀ := f₀, qc := inferInstance, qs := inferInstance, lft := inferInstance,
           g := g, pb := pb }⟩

end Affine
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Induction

variable (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

def GlueHyp : Prop :=
  ∀ (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of K)) [CompactSpace X] [QuasiSeparatedSpace X]
    [LocallyOfFiniteType fX] (U V : X.Opens), U ⊔ V = ⊤ → IsCompact (U : Set X) → IsCompact (V : Set X) →
    Nonempty (Datum k K U.toScheme (U.ι ≫ fX)) → Nonempty (Datum k K V.toScheme (V.ι ≫ fX)) →
    Nonempty (Datum k K X fX)

variable {k K}

theorem glueHyp : GlueHyp k K := by
  intro X fX _ _ _ U V hUV hUc hVc hU hV
  obtain ⟨dU⟩ := hU
  obtain ⟨dV⟩ := hV
  haveI := dU.fd
  haveI := dV.fd
  obtain ⟨E, hUE, hVE, hE⟩ : ∃ E : IntermediateField k K, dU.E ≤ E ∧ dV.E ≤ E ∧ FiniteDimensional k E :=
    ⟨dU.E ⊔ dV.E, le_sup_left, le_sup_right, IntermediateField.finiteDimensional_sup dU.E dV.E⟩
  haveI := hE
  haveI : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := k) E
  have mU : Model E K U (U.ι ≫ fX) := (dU.relevel E hUE hE).toModel
  have mV : Model E K V (V.ι ≫ fX) := (dV.relevel E hVE hE).toModel
  obtain ⟨L, hL, ⟨m⟩⟩ := glue_core U V hUV hUc hVc mU mV
  exact ⟨Datum.ofModel (L.restrictScalars k) (finiteDimensional_restrictScalars E L) m⟩

theorem descends_of_finite_affine_cover (hG : GlueHyp k K) :
    ∀ (n : ℕ) (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of K)) [CompactSpace X] [QuasiSeparatedSpace X]
      [LocallyOfFiniteType fX] (U : Fin n → X.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ →
      Nonempty (Datum k K X fX) := by
  intro n
  induction n with
  | zero =>
    intro X fX _ _ _ U hU hcov
    have hbot : (⊤ : X.Opens) = ⊥ := by rw [← hcov]; simp
    haveI : IsEmpty X := ⟨fun x => by
      have : x ∈ (⊤ : X.Opens) := trivial
      rw [hbot] at this
      exact this⟩
    haveI : IsAffine X := isAffine_of_isEmpty
    exact affine_descends X fX
  | succ n ih =>
    intro X fX _ _ _ U hU hcov

    let U' : X.Opens := U (Fin.last n)
    let V' : X.Opens := ⨆ i : Fin n, U (Fin.castSucc i)
    have hUV : U' ⊔ V' = ⊤ := by
      apply top_le_iff.mp
      rw [← hcov]
      refine iSup_le fun i => ?_
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact le_sup_of_le_right (le_iSup (fun j : Fin n => U (Fin.castSucc j)) j)
      · exact le_sup_left
    have hU'c : IsCompact (U' : Set X) := (hU (Fin.last n)).isCompact
    have hV'c : IsCompact (V' : Set X) := by
      simp only [V', TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
        TopologicalSpace.Opens.coe_mk]
      exact isCompact_iUnion fun i => (hU _).isCompact

    have hU' : Nonempty (Datum k K U'.toScheme (U'.ι ≫ fX)) := by
      haveI : IsAffine U'.toScheme := hU (Fin.last n)
      exact affine_descends _ _

    have hV' : Nonempty (Datum k K V'.toScheme (V'.ι ≫ fX)) := by
      haveI : CompactSpace V'.toScheme := isCompact_iff_compactSpace.mp hV'c
      haveI : QuasiSeparatedSpace V'.toScheme := V'.ι.isOpenEmbedding.quasiSeparatedSpace
      refine ih V'.toScheme (V'.ι ≫ fX) (fun i => V'.ι ⁻¹ᵁ U (Fin.castSucc i)) (fun i => ?_) ?_
      · refine (hU _).preimage_of_isOpenImmersion V'.ι ?_
        rw [Scheme.Opens.opensRange_ι]
        exact le_iSup (fun j : Fin n => U (Fin.castSucc j)) i
      · rw [← Scheme.Hom.preimage_iSup]
        exact Scheme.Opens.ι_preimage_self V'
    exact hG X fX U' V' hUV hU'c hV'c hU' hV'

theorem descends (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX] : Nonempty (Datum k K X fX) := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  let eqv := Fintype.equivFin 𝒰.I₀
  exact descends_of_finite_affine_cover glueHyp (Fintype.card 𝒰.I₀) X fX
    (fun i => (𝒰.f (eqv.symm i)).opensRange) (fun i => isAffineOpen_opensRange _) (by
      apply top_le_iff.mp
      rw [← 𝒰.iSup_opensRange]
      exact iSup_le fun j => le_iSup_of_le (eqv j) (by
        change (𝒰.f j).opensRange ≤ (𝒰.f (eqv.symm (eqv j))).opensRange
        rw [Equiv.symm_apply_apply]))

end Induction
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

end SchemeSpread
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

theorem solution
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX] :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Spec (CommRingCat.of L)) (_ : CompactSpace X₀) (_ : QuasiSeparatedSpace X₀)
      (_ : LocallyOfFiniteType f₀) (g : X ⟶ X₀),
      IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap L K))) := by
  obtain ⟨d⟩ := SchemeSpread.descends (k := k) (K := K) X fX
  exact ⟨d.E, d.fd, d.X₀, d.f₀, d.qc, d.qs, d.lft, d.g, d.pb⟩

end S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic
end P2MW
export P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic (solution)
