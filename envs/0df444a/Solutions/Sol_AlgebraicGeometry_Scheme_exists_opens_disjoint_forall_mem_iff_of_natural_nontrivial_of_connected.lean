-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/50c527ad-0cca-5882-813d-147a18a3a0ae

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

namespace LabelSplit

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

theorem isIdempotentElem_eq_zero_or_one_of_field {F : Type} [Field F] (e : F) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.1 h)

section Charts

variable {C : Type} [CommRing C] {X : Scheme.{0}}

def A (fX : X ⟶ Spec (CommRingCat.of C)) (V : X.affineOpens) : Type := Γ(X, V)

variable (fX : X ⟶ Spec (CommRingCat.of C)) (V : X.affineOpens)

noncomputable scoped instance : CommRing (A fX V) := inferInstanceAs (CommRing Γ(X, V))

noncomputable def ι : Spec (CommRingCat.of (A fX V)) ⟶ X := V.2.fromSpec

scoped instance : IsOpenImmersion (ι fX V) := V.2.isOpenImmersion_fromSpec

theorem range_ι : Set.range ⇑(ι fX V) = (V : Set X) := V.2.range_fromSpec

noncomputable def chartHom : C →+* A fX V := (Spec.preimage (ι fX V ≫ fX)).hom

noncomputable scoped instance algC : Algebra C (A fX V) := (chartHom fX V).toAlgebra

theorem ι_comp : ι fX V ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap C (A fX V))) := by
  rw [RingHom.algebraMap_toAlgebra]
  show ι fX V ≫ fX = Spec.map (CommRingCat.ofHom (Spec.preimage (ι fX V ≫ fX)).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

noncomputable def τ : (Scheme.nilpPoints fX).obj (A fX V) := ⟨ι fX V, ι_comp fX V⟩

scoped instance noeth [IsNoetherianRing C] [LocallyOfFiniteType fX] : IsNoetherianRing (A fX V) := by
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of C), ⊤) :=
    isNoetherianRing_of_ringEquiv C (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv
  letI : Algebra Γ(Spec (CommRingCat.of C), ⊤) (A fX V) := (fX.appLE ⊤ V.1 le_top).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Spec (CommRingCat.of C), ⊤) (A fX V) :=
    fX.finiteType_appLE (isAffineOpen_top _) V.2 le_top
  exact Algebra.FiniteType.isNoetherianRing Γ(Spec (CommRingCat.of C), ⊤) (A fX V)

theorem exists_algHom_map_τ_eq {T : Type} [CommRing T] [Algebra C T] (y : (Scheme.nilpPoints fX).obj T)
    (hy : Set.range ⇑y.1 ⊆ (V : Set X)) :
    ∃ g : A fX V →ₐ[C] T, (Scheme.nilpPoints fX).map g (τ fX V) = y := by
  have hrange : Set.range ⇑y.1 ⊆ Set.range ⇑(ι fX V) := by rw [range_ι]; exact hy
  let l : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (A fX V)) := IsOpenImmersion.lift (ι fX V) y.1 hrange
  have hl : l ≫ ι fX V = y.1 := IsOpenImmersion.lift_fac _ _ _
  let g₀ : A fX V →+* T := (Spec.preimage l).hom
  have hg₀ : Spec.map (CommRingCat.ofHom g₀) = l := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage l).hom) = l
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hgC : g₀.comp (algebraMap C (A fX V)) = algebraMap C T := by
    have h1 : Spec.map (CommRingCat.ofHom (g₀.comp (algebraMap C (A fX V)))) =
        Spec.map (CommRingCat.ofHom (algebraMap C T)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hg₀, ← ι_comp, ← Category.assoc, hl]
      exact y.2
    have h2 := Spec.map_injective h1
    rw [← CommRingCat.hom_ofHom (g₀.comp (algebraMap C (A fX V))), h2, CommRingCat.hom_ofHom]
  let g : A fX V →ₐ[C] T :=
    { toRingHom := g₀, commutes' := fun c => by
        show g₀ (algebraMap C (A fX V) c) = algebraMap C T c
        rw [← RingHom.comp_apply, hgC] }
  refine ⟨g, ?_⟩
  apply Subtype.ext
  rw [Scheme.nilpPoints_map_val]
  show Spec.map (CommRingCat.ofHom g₀) ≫ ι fX V = y.1
  rw [hg₀, hl]

end Charts

section Residue

variable {C : Type} [CommRing C] {X : Scheme.{0}}

def Kpt (fX : X ⟶ Spec (CommRingCat.of C)) (z : X) : Type := X.residueField z

variable (fX : X ⟶ Spec (CommRingCat.of C)) (z : X)

noncomputable scoped instance : Field (Kpt fX z) := inferInstanceAs (Field (X.residueField z))

noncomputable def ιpt : Spec (CommRingCat.of (Kpt fX z)) ⟶ X := X.fromSpecResidueField z

noncomputable scoped instance algCpt : Algebra C (Kpt fX z) := (Spec.preimage (ιpt fX z ≫ fX)).hom.toAlgebra

theorem ιpt_comp : ιpt fX z ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap C (Kpt fX z))) := by
  rw [RingHom.algebraMap_toAlgebra]
  show ιpt fX z ≫ fX = Spec.map (CommRingCat.ofHom (Spec.preimage (ιpt fX z ≫ fX)).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

noncomputable def τpt : (Scheme.nilpPoints fX).obj (Kpt fX z) := ⟨ιpt fX z, ιpt_comp fX z⟩

theorem range_τpt : Set.range ⇑(τpt fX z).1 ⊆ {z} := by
  rintro _ ⟨s, rfl⟩
  exact Scheme.fromSpecResidueField_apply z s

end Residue

end LabelSplit
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected.LabelSplit"

open LabelSplit in
theorem solution
    {C : Type} [CommRing C] [IsNoetherianRing C] (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType fX]
    (L : Type) [Fintype L] [DecidableEq L]
    (lab : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S],
      (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) → (Scheme.nilpPoints fX).obj S → L)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Nontrivial S']
      (hS : (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)) (hS' : (∀ e : S', IsIdempotentElem e → e = 0 ∨ e = 1))
      (g : S →ₐ[C] S') (x : (Scheme.nilpPoints fX).obj S),
      lab S' hS' ((Scheme.nilpPoints fX).map g x) = lab S hS x) :
    ∃ U : L → X.Opens,
      (∀ l l' : L, l ≠ l' → Disjoint (U l) (U l')) ∧ (⨆ l, U l) = ⊤ ∧
      ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Nontrivial S] (hS : (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1))
        (x : (Scheme.nilpPoints fX).obj S) (l : L),
        lab S hS x = l ↔ ∀ p : ↥(Spec (CommRingCat.of S)), x.1.base p ∈ U l := by
  classical

  let Piece : Type := {W : X.affineOpens // ∀ e : A fX W, IsIdempotentElem e → e = 0 ∨ e = 1}
  let lW : Piece → L := fun W => lab (A fX W.1) W.2 (τ fX W.1)

  have cover : ∀ z : X, ∃ W : Piece, z ∈ (W.1 : Set X) := by
    intro z
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    let V' : X.affineOpens := ⟨V, hV⟩

    obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum (A fX V'), ι fX V' p = z := by
      have : z ∈ Set.range ⇑(ι fX V') := by rw [range_ι]; exact hzV
      exact this
    obtain ⟨e, he, hCe⟩ := PrimeSpectrum.isClopen_iff.mp
      ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace p⟩

    let W : X.affineOpens := ⟨X.basicOpen (show Γ(X, V) from e), hV.basicOpen _⟩
    have hWset : (W.1 : Set X) = ⇑(ι fX V') '' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum (A fX V'))) := by
      show ((X.basicOpen (show Γ(X, V) from e) : X.Opens) : Set X) =
        ⇑hV.fromSpec '' ((PrimeSpectrum.basicOpen (show Γ(X, V) from e) : Opens (PrimeSpectrum Γ(X, V))) : Set (PrimeSpectrum Γ(X, V)))
      rw [← hV.fromSpec_image_basicOpen]
      rfl
    have hpre : _root_.IsPreconnected (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum (A fX V'))) := by
      have := (isPreconnected_connectedComponent (x := p))
      rw [hCe] at this
      exact this
    have hconn : ∀ f : A fX W, IsIdempotentElem f → f = 0 ∨ f = 1 := by
      have huniv : _root_.IsPreconnected (Set.univ : Set ↥(Spec (CommRingCat.of (A fX W)))) := by
        rw [← (ι fX W).isOpenEmbedding.isInducing.isPreconnected_image, Set.image_univ, range_ι, hWset]
        exact hpre.image _ (ι fX V').base.hom.continuous.continuousOn
      haveI : PreconnectedSpace (PrimeSpectrum (A fX W)) := ⟨huniv⟩
      exact isIdempotentElem_eq_zero_or_one_of_preconnectedSpace
    refine ⟨⟨W, hconn⟩, ?_⟩
    show z ∈ (W.1 : Set X)
    rw [hWset, ← hp]
    refine ⟨p, ?_, rfl⟩
    have : p ∈ connectedComponent p := mem_connectedComponent
    rw [hCe] at this
    exact this

  have key : ∀ (T : Type) [CommRing T] [Algebra C T] [IsNoetherianRing T] [Nontrivial T]
      (hT : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1) (y : (Scheme.nilpPoints fX).obj T) (W : Piece),
      Set.range ⇑y.1 ⊆ (W.1 : Set X) → lab T hT y = lW W := by
    intro T _ _ _ _ hT y W hy
    obtain ⟨g, hg⟩ := exists_algHom_map_τ_eq fX W.1 y hy
    rw [← hg]
    exact hnat _ _ W.2 hT g (τ fX W.1)

  have atPrime : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S]
      (hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (x : (Scheme.nilpPoints fX).obj S) (p : PrimeSpectrum S) (W : Piece),
      x.1 p ∈ (W.1 : Set X) → lab S hS x = lW W := by
    intro S _ _ _ hS x p W hp
    let κ : Type := p.asIdeal.ResidueField
    let φ : S →ₐ[C] κ := IsScalarTower.toAlgHom C S κ
    have h1 := hnat S κ hS (isIdempotentElem_eq_zero_or_one_of_field) φ x
    rw [← h1]
    apply key κ _ _ W
    rintro _ ⟨s, rfl⟩
    rw [Scheme.nilpPoints_map_val, Scheme.Hom.comp_apply]
    have hs : (Spec.map (CommRingCat.ofHom φ.toRingHom)) s = p := by
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap S κ) s.asIdeal = p.asIdeal
      rw [Ideal.eq_bot_of_prime s.asIdeal, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
    rw [hs]
    exact hp

  have agree : ∀ (W W' : Piece) (z : X), z ∈ (W.1 : Set X) → z ∈ (W'.1 : Set X) → lW W = lW W' := by
    intro W W' z hz hz'
    haveI : IsNoetherianRing (Kpt fX z) := inferInstance
    have h := key (Kpt fX z) (isIdempotentElem_eq_zero_or_one_of_field) (τpt fX z) W
      ((range_τpt fX z).trans (Set.singleton_subset_iff.2 hz))
    have h' := key (Kpt fX z) (isIdempotentElem_eq_zero_or_one_of_field) (τpt fX z) W'
      ((range_τpt fX z).trans (Set.singleton_subset_iff.2 hz'))
    rw [← h, ← h']

  refine ⟨fun l => ⨆ (W : Piece) (_ : lW W = l), (W.1 : X.Opens), ?_, ?_, ?_⟩
  ·
    intro l l' hll'
    rw [← Opens.coe_disjoint, Set.disjoint_left]
    intro z hz hz'
    obtain ⟨W, hW⟩ := Opens.mem_iSup.1 hz
    obtain ⟨hWl, hzW⟩ := Opens.mem_iSup.1 hW
    obtain ⟨W', hW'⟩ := Opens.mem_iSup.1 hz'
    obtain ⟨hW'l, hzW'⟩ := Opens.mem_iSup.1 hW'
    exact hll' (hWl.symm.trans ((agree W W' z hzW hzW').trans hW'l))
  ·
    apply top_le_iff.1
    intro z _
    obtain ⟨W, hzW⟩ := cover z
    exact Opens.mem_iSup.2 ⟨lW W, Opens.mem_iSup.2 ⟨W, Opens.mem_iSup.2 ⟨rfl, hzW⟩⟩⟩
  ·
    intro S _ _ _ _ hS x l
    constructor
    · intro h p
      obtain ⟨W, hzW⟩ := cover (x.1.base p)
      have hl : lW W = l := (atPrime S hS x p W hzW).symm.trans h
      exact Opens.mem_iSup.2 ⟨W, Opens.mem_iSup.2 ⟨hl, hzW⟩⟩
    · intro h
      obtain ⟨p⟩ : Nonempty (PrimeSpectrum S) := inferInstance
      obtain ⟨W, hW⟩ := Opens.mem_iSup.1 (h p)
      obtain ⟨hWl, hzW⟩ := Opens.mem_iSup.1 hW
      exact (atPrime S hS x p W hzW).trans hWl

end S_AlgebraicGeometry_Scheme_exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected (solution)
