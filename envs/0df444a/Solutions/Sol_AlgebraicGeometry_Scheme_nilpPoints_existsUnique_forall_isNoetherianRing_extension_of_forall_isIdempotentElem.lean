-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nilpPoints.existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0d2b2f6f-77d8-515d-b1d6-de9953c229db

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_forall_isNoetherianRing_eq_of_forall_eq_of_forall_isIdempotentElem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

open TopologicalSpace Topology

namespace ExtendDefNoeth

theorem isOpen_connectedComponent_of_noetherianSpace {α : Type} [TopologicalSpace α] [NoetherianSpace α]
    (x : α) : IsOpen (connectedComponent x) := by
  classical
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcl : IsClosed (⋃ Z ∈ {Z ∈ irreducibleComponents α | ¬ Z ⊆ connectedComponent x}, Z) :=
    (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  have heq : (connectedComponent x)ᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents α | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZC⟩, hyZ⟩ hyC
      apply hZC
      rw [connectedComponent_eq hyC]
      exact hZ.1.2.isPreconnected.subset_connectedComponent hyZ
  rw [← isClosed_compl_iff, heq]
  exact hcl

theorem isIdempotentElem_eq_zero_or_one_of_preconnectedSpace {S : Type} [CommRing S]
    [PreconnectedSpace (PrimeSpectrum S)] (f : S) (hf : IsIdempotentElem f) : f = 0 ∨ f = 1 := by
  have key : ∀ g : S, IsIdempotentElem g → (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) = ∅ → g = 0 := by
    intro g hg h
    have hbot : PrimeSpectrum.basicOpen g = ⊥ := TopologicalSpace.Opens.ext (by simpa using h)
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff g).mp hbot
    cases n with
    | zero =>
      rw [pow_zero] at hn
      rw [← mul_one g, hn, mul_zero]
    | succ n => rw [← hg.pow_succ_eq n, hn]
  have hclopen : IsClopen (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨f, hf, rfl⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact Or.inl (key f hf h)
  · right
    have h1 : (PrimeSpectrum.basicOpen (1 - f) : Set (PrimeSpectrum S)) = ∅ := by
      rw [← PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem f hf]
      exact Set.compl_univ_iff.mp (by rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; exact h)
    have := key (1 - f) hf.one_sub h1
    exact (sub_eq_zero.mp this).symm

section comp

variable (B : Type) [CommRing B]

def Comp : Type := {C : Set (PrimeSpectrum B) // ∃ p : PrimeSpectrum B, C = connectedComponent p}

variable {B}

theorem Comp.eq_of_mem {C C' : Comp B} {y : PrimeSpectrum B} (h : y ∈ C.1) (h' : y ∈ C'.1) : C = C' := by
  obtain ⟨p, hp⟩ := C.2
  obtain ⟨p', hp'⟩ := C'.2
  apply Subtype.ext
  rw [hp] at h ⊢; rw [hp'] at h' ⊢
  rw [connectedComponent_eq h, connectedComponent_eq h']

theorem Comp.isPreconnected (C : Comp B) : _root_.IsPreconnected C.1 := by
  obtain ⟨p, hp⟩ := C.2
  rw [hp]; exact isPreconnected_connectedComponent

variable [IsNoetherianRing B]

theorem Comp.isClopen (C : Comp B) : IsClopen C.1 := by
  obtain ⟨p, hp⟩ := C.2
  rw [hp]
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace p⟩

noncomputable def Comp.idem (C : Comp B) : B := (PrimeSpectrum.isClopen_iff.mp C.isClopen).choose

theorem Comp.idem_spec (C : Comp B) :
    IsIdempotentElem C.idem ∧ C.1 = ↑(PrimeSpectrum.basicOpen C.idem) :=
  (PrimeSpectrum.isClopen_iff.mp C.isClopen).choose_spec

abbrev Comp.Piece (C : Comp B) : Type := Localization.Away C.idem

theorem Comp.range_comap (C : Comp B) :
    Set.range (PrimeSpectrum.comap (algebraMap B C.Piece)) = C.1 := by
  rw [PrimeSpectrum.localization_away_comap_range C.Piece C.idem, ← C.idem_spec.2]

theorem Comp.piece_connected (C : Comp B) : ∀ f : C.Piece, IsIdempotentElem f → f = 0 ∨ f = 1 := by
  have hemb := PrimeSpectrum.localization_away_isOpenEmbedding C.Piece C.idem
  haveI : PreconnectedSpace (PrimeSpectrum C.Piece) := ⟨by
    rw [← hemb.isInducing.isPreconnected_image, Set.image_univ, C.range_comap]
    exact C.isPreconnected⟩
  exact isIdempotentElem_eq_zero_or_one_of_preconnectedSpace

def Comp.of (p : PrimeSpectrum B) : Comp B := ⟨connectedComponent p, p, rfl⟩

omit [IsNoetherianRing B] in
theorem Comp.mem_of (p : PrimeSpectrum B) : p ∈ (Comp.of p).1 := mem_connectedComponent

end comp

section cover

variable (B : Type) [CommRing B] [IsNoetherianRing B]

noncomputable abbrev cover : (Spec (CommRingCat.of B)).OpenCover where
  I₀ := Comp B
  X C := Spec (CommRingCat.of C.Piece)
  f C := Spec.map (CommRingCat.ofHom (algebraMap B C.Piece))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p => ⟨Comp.of p, ?_⟩, fun C => inferInstance⟩
    have := (Comp.of p).range_comap
    exact (eq_iff_iff.mp congr(p ∈ $this)).mpr (Comp.mem_of p)

variable {B}

theorem cover_f_apply_mem (C : Comp B) (a : ↥((cover B).X C)) : (cover B).f C a ∈ C.1 := by
  have := C.range_comap
  exact (eq_iff_iff.mp congr(((cover B).f C a) ∈ $this)).mp ⟨a, rfl⟩

theorem isEmpty_pullback_of_ne {C C' : Comp B} (h : C ≠ C') :
    IsEmpty ↥(Limits.pullback ((cover B).f C) ((cover B).f C')) := by
  refine ⟨fun z => h ?_⟩
  have e := congrArg (fun φ => φ z) (Limits.pullback.condition (f := (cover B).f C) (g := (cover B).f C'))
  simp only [Scheme.Hom.comp_apply] at e
  exact Comp.eq_of_mem (cover_f_apply_mem C _) (e ▸ cover_f_apply_mem C' _)

theorem compatible {Y : Scheme.{0}} (g : ∀ C : Comp B, (cover B).X C ⟶ Y) (C C' : Comp B) :
    Limits.pullback.fst ((cover B).f C) ((cover B).f C') ≫ g C = Limits.pullback.snd ((cover B).f C) ((cover B).f C') ≫ g C' := by
  classical
  by_cases h : C = C'
  · subst h
    rw [Limits.fst_eq_snd_of_mono_eq]
  · haveI := isEmpty_pullback_of_ne h
    exact (isInitialOfIsEmpty).hom_ext _ _

end cover

section extend

variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)
  {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))
  (u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
    (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → F.obj B → (Scheme.nilpPoints fN).obj B)

theorem nilp_piece {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (C : Comp B) : IsNilpotent (algebraMap 𝒪 C.Piece π) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 B C.Piece]
  exact hB.map _

noncomputable def piece {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : F.obj B) (C : Comp B) : (cover B).X C ⟶ N :=
  (u C.Piece (nilp_piece π hB C) C.piece_connected (F.map (IsScalarTower.toAlgHom 𝒪 B C.Piece) x)).1

noncomputable def glue {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : F.obj B) : Spec (CommRingCat.of B) ⟶ N :=
  (cover B).glueMorphisms (piece π F fN u hB x) (compatible _)

theorem cover_f_glue {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : F.obj B) (C : Comp B) : (cover B).f C ≫ glue π F fN u hB x = piece π F fN u hB x C := by
  rw [glue]
  exact Scheme.Cover.ι_glueMorphisms (cover B) (piece π F fN u hB x) (compatible (piece π F fN u hB x)) C

theorem cover_f_comp_specOver {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (C : Comp B) :
    (cover B).f C ≫ Scheme.specOver (𝒪 := 𝒪) B = Scheme.specOver C.Piece :=
  Scheme.specMap_algHom_comp_specOver (IsScalarTower.toAlgHom 𝒪 B C.Piece)

noncomputable def UN (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : F.obj B) : (Scheme.nilpPoints fN).obj B :=
  ⟨glue π F fN u hB x, by
    refine (cover B).hom_ext _ _ fun C => ?_
    rw [← Category.assoc, cover_f_glue, cover_f_comp_specOver]
    exact (u C.Piece (nilp_piece π hB C) C.piece_connected (F.map (IsScalarTower.toAlgHom 𝒪 B C.Piece) x)).2⟩

variable (hu : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hc' : ∀ e : B', IsIdempotentElem e → e = 0 ∨ e = 1)
    (φ : B →ₐ[𝒪] B') (x : F.obj B),
    u B' hB' hc' (F.map φ x) = (Scheme.nilpPoints fN).map φ (u B hB hc x))

include hu in

theorem UN_eq {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (x : F.obj B) : UN π F fN u B hB x = u B hB hc x := by
  apply Subtype.ext
  refine (cover B).hom_ext _ _ fun C => ?_
  show (cover B).f C ≫ glue π F fN u hB x = (cover B).f C ≫ (u B hB hc x).1
  rw [cover_f_glue]
  have h := congrArg Subtype.val (hu B C.Piece hB (nilp_piece π hB C) hc C.piece_connected (IsScalarTower.toAlgHom 𝒪 B C.Piece) x)
  rw [Scheme.nilpPoints_map_val] at h
  exact h

theorem isUnit_of_range_comap_subset {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (b : R)
    (h : Set.range (PrimeSpectrum.comap g) ⊆ ↑(PrimeSpectrum.basicOpen b)) : IsUnit (g b) := by
  by_contra hb
  obtain ⟨m, hm, hbm⟩ := Ideal.exists_le_maximal (Ideal.span {g b}) ((Ideal.span_singleton_ne_top) hb)
  have hq := h ⟨⟨m, hm.isPrime⟩, rfl⟩
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hq
  exact hq (hbm (Ideal.mem_span_singleton_self _))

variable {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
  (φ : B →ₐ[𝒪] B')

noncomputable def back (C' : Comp B') : Comp B := Comp.of (PrimeSpectrum.comap φ.toRingHom C'.2.choose)

theorem range_subset_back (C' : Comp B') :
    Set.range (PrimeSpectrum.comap ((algebraMap B' C'.Piece).comp φ.toRingHom)) ⊆ (back φ C').1 := by
  have hp' : C'.1 = connectedComponent C'.2.choose := C'.2.choose_spec
  have hr : Set.range (PrimeSpectrum.comap ((algebraMap B' C'.Piece).comp φ.toRingHom)) =
      PrimeSpectrum.comap φ.toRingHom '' C'.1 := by
    rw [← C'.range_comap, ← Set.range_comp]
    rfl
  rw [hr]
  refine (C'.isPreconnected.image _ (PrimeSpectrum.continuous_comap φ.toRingHom).continuousOn).subset_connectedComponent ?_
  exact ⟨C'.2.choose, ((Set.ext_iff.mp hp') _).mpr mem_connectedComponent, rfl⟩

theorem isUnit_back (C' : Comp B') : IsUnit (((algebraMap B' C'.Piece).comp φ.toRingHom) (back φ C').idem) :=
  isUnit_of_range_comap_subset _ _ ((back φ C').idem_spec.2 ▸ range_subset_back φ C')

private noncomputable def _root_.ExtendDefNoeth.lift (C' : Comp B') : (back φ C').Piece →ₐ[𝒪] C'.Piece where
  toRingHom := IsLocalization.Away.lift (S := (back φ C').Piece) (back φ C').idem (isUnit_back φ C')
  commutes' r := by
    have h := congrArg (fun g => g (algebraMap 𝒪 B r)) (IsLocalization.Away.lift_comp (S := (back φ C').Piece) (back φ C').idem (isUnit_back φ C'))
    simp only [RingHom.comp_apply] at h
    rw [IsScalarTower.algebraMap_apply 𝒪 B (back φ C').Piece, IsScalarTower.algebraMap_apply 𝒪 B' C'.Piece]
    refine h.trans ?_
    change algebraMap B' C'.Piece (φ (algebraMap 𝒪 B r)) = _
    rw [AlgHom.commutes]

p2m_export "ExtendDefNoeth" "lift"
theorem lift_comp_toAlgHom (C' : Comp B') :
    (lift φ C').comp (IsScalarTower.toAlgHom 𝒪 B (back φ C').Piece) = (IsScalarTower.toAlgHom 𝒪 B' C'.Piece).comp φ := by
  apply AlgHom.ext
  intro b
  have h := congrArg (fun g => g b) (IsLocalization.Away.lift_comp (S := (back φ C').Piece) (back φ C').idem (isUnit_back φ C'))
  exact h

theorem cover_f_comp_specMap (C' : Comp B') :
    (cover B').f C' ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom (lift φ C').toRingHom) ≫ (cover B).f (back φ C') := by
  show Spec.map (CommRingCat.ofHom (algebraMap B' C'.Piece)) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
    Spec.map (CommRingCat.ofHom (lift φ C').toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap B (back φ C').Piece))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (IsLocalization.Away.lift_comp (S := (back φ C').Piece) (back φ C').idem (isUnit_back φ C')).symm

include hu in
theorem UN_nat (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (x : F.obj B) :
    UN π F fN u B' hB' (F.map φ x) = (Scheme.nilpPoints fN).map φ (UN π F fN u B hB x) := by
  apply Subtype.ext
  rw [Scheme.nilpPoints_map_val]
  refine (cover B').hom_ext _ _ fun C' => ?_
  show (cover B').f C' ≫ glue π F fN u hB' (F.map φ x) = (cover B').f C' ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ glue π F fN u hB x)
  have e2 : (cover B').f C' ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ glue π F fN u hB x) =
      Spec.map (CommRingCat.ofHom (lift φ C').toRingHom) ≫ piece π F fN u hB x (back φ C') := by
    rw [← cover_f_glue π F fN u hB x (back φ C'), ← Category.assoc, ← Category.assoc, cover_f_comp_specMap]
  rw [cover_f_glue, e2]

  have h := congrArg Subtype.val (hu (back φ C').Piece C'.Piece (nilp_piece π hB (back φ C')) (nilp_piece π hB' C')
    (back φ C').piece_connected C'.piece_connected (lift φ C') (F.map (IsScalarTower.toAlgHom 𝒪 B (back φ C').Piece) x))
  rw [Scheme.nilpPoints_map_val, ← F.map_comp, lift_comp_toAlgHom, F.map_comp] at h
  exact h

end extend

end ExtendDefNoeth

open ExtendDefNoeth in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → F.obj B → (Scheme.nilpPoints fN).obj B)
    (hu : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hc' : ∀ e : B', IsIdempotentElem e → e = 0 ∨ e = 1)
      (φ : B →ₐ[𝒪] B') (x : F.obj B),
      u B' hB' hc' (F.map φ x) = (Scheme.nilpPoints fN).map φ (u B hB hc x)) :
    ∃! U : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints fN).obj B,

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : F.obj B),
          U B' hB' (F.map φ x) = (Scheme.nilpPoints fN).map φ (U B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (x : F.obj B), U B hB x = u B hB hc x) := by
  classical
  refine ⟨UN π F fN u, ⟨?_, ?_⟩, ?_⟩
  · intro B _ _ _ B' _ _ _ hB hB' φ x
    exact UN_nat π F fN u hu φ hB hB' x
  · intro B _ _ _ hB hc x
    exact UN_eq π F fN u hu hB hc x
  · rintro U' ⟨hU'nat, hU'u⟩
    funext B instB instN instA hB x
    exact AlgebraicGeometry.Scheme.nilpPoints.forall_isNoetherianRing_eq_of_forall_eq_of_forall_isIdempotentElem π F fN
      U' (UN π F fN u) hU'nat (fun B _ _ _ B' _ _ _ hB hB' φ x => UN_nat π F fN u hu φ hB hB' x)
      (fun B _ _ _ hB hc x => by rw [hU'u B hB hc x, UN_eq π F fN u hu hB hc x]) B hB x

end S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem (solution)
