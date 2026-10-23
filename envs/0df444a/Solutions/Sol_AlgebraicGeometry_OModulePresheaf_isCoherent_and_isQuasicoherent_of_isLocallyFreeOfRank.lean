-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isCoherent_and_isQuasicoherent_of_isLocallyFreeOfRank
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-22T17:33:48.698808+00:00
-- url     : https://prove2.me/submissions/46c78a7b-938a-4f2c-8005-aeb0d2d74cb4

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace PhilipponFiniteRankSections

/-- A linear map carrying one finite basis to another is scalar extension. -/
lemma baseChange_of_bases
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    [Module A P] [Module A Q] [Module B Q] [IsScalarTower A B Q]
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι A P) (c : Module.Basis ι B Q)
    (f : P →ₗ[A] Q) (hf : ∀ i, f (b i) = c i) : IsBaseChange B f := by
  classical
  have h := IsBaseChange.comp_equiv b.equivFun (Fintype.linearCombination A c)
    (IsBaseChange.of_fintype_basis A c)
  convert h using 1
  apply b.ext
  intro i
  simp [Fintype.linearCombination_apply, hf, Finsupp.single_apply]

variable {X : Scheme.{u}} (M : X.Modules)

abbrev resModule {V W : X.Opens} (h : W ≤ V) : Module Γ(X, V) Γ(M, W) :=
  Module.compHom _ (X.presheaf.map (homOfLE h).op).hom

def resLinear {V W : X.Opens} (h : W ≤ V) :
    letI := resModule M h
    Γ(M, V) →ₗ[Γ(X, V)] Γ(M, W) :=
  letI := resModule M h
  { toFun := M.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun a m => Scheme.Modules.map_smul M (homOfLE h) a m }

abbrev LocProp (W : X.Opens) (f : Γ(X, W)) : Prop :=
  (∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, W)),
    M.presheaf.map (homOfLE (X.basicOpen_le f)).op y =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x) ∧
  (∀ y : Γ(M, W), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
    ∃ n : ℕ, (f ^ n : Γ(X, W)) • y = 0)

/-- On a basis neighborhood, restriction to a principal open localizes each coordinate. -/
lemma local_localization {d : ℕ} {V : X.Opens} (e : Fin d → Γ(M, V))
    (he : ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W),
        ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i))
    {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ V)
    (f : Γ(X, W)) : LocProp M W f := by
  let h := X.basicOpen_le f
  let := resModule M h
  let : IsScalarTower Γ(X, W) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have := hW.isLocalization_basicOpen f
  obtain ⟨b, hb⟩ := he W hWV
  obtain ⟨c, hc⟩ := he (X.basicOpen f) (h.trans hWV)
  have hbc : IsBaseChange Γ(X, X.basicOpen f) (resLinear M h) := by
    apply baseChange_of_bases b c
    intro i
    change M.presheaf.map (homOfLE h).op (b i) = c i
    rw [hb, hc, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have : IsLocalizedModule.Away f (resLinear M h) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f)
      Γ(X, X.basicOpen f) (resLinear M h)).mpr hbc
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := IsLocalizedModule.Away.surj (resLinear M h) f x
    exact ⟨n, y, hy.symm⟩
  · intro y hy
    have hy' : resLinear M h y = resLinear M h 0 := by simpa [resLinear] using hy
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq f hy'
    exact ⟨n, by simpa using hn⟩

abbrev BasisOn (d : ℕ) (V : X.Opens) : Prop :=
  ∃ e : Fin d → Γ(M, V), ∀ (W : X.Opens) (hW : W ≤ V),
    ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W),
      ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)

/-- Refine local bases to a finite principal-open cover of an affine open. -/
lemma finite_cover {d : ℕ} (hM : Scheme.Modules.IsLocallyFreeOfRank d M)
    (U : X.affineOpens) :
    ∃ s : Finset Γ(X, U.1),
      (U.1 ≤ ⨆ h ∈ s, X.basicOpen h) ∧ Ideal.span (s : Set Γ(X, U.1)) = ⊤ ∧
      ∀ h ∈ s, ∃ V : X.Opens, X.basicOpen h ≤ V ∧ BasisOn M d V := by
  classical
  have hbasis : ∀ x : U.1, ∃ (h : Γ(X, U.1)) (V : X.Opens),
      (x : X) ∈ X.basicOpen h ∧ X.basicOpen h ≤ V ∧ BasisOn M d V := by
    intro x
    obtain ⟨V, hxV, e, he⟩ := hM.exists_basis x
    obtain ⟨h, hhV, hxh⟩ := U.2.exists_basicOpen_le ⟨(x : X), hxV⟩ x.2
    exact ⟨h, V, hxh, hhV, e, he⟩
  choose hOf VOf hxh hhV he using hbasis
  have hcov : (U.1 : Set X) ⊆ ⋃ x : U.1, (X.basicOpen (hOf x) : Set X) :=
    fun p hp => Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxh ⟨p, hp⟩⟩
  obtain ⟨t, ht⟩ := U.2.isCompact.elim_finite_subcover
    (fun x : U.1 => (X.basicOpen (hOf x) : Set X))
    (fun x => (X.basicOpen (hOf x)).isOpen) hcov
  refine ⟨t.image hOf, ?_, ?_, ?_⟩
  · intro p hp
    have hp' := ht hp
    simp only [Set.mem_iUnion] at hp'
    obtain ⟨x, hxt, hpx⟩ := hp'
    exact Opens.mem_iSup.mpr ⟨hOf x,
      Opens.mem_iSup.mpr ⟨Finset.mem_image_of_mem hOf hxt, hpx⟩⟩
  · rw [Finset.coe_image, ← U.2.self_le_iSup_basicOpen_iff]
    intro p hp
    have hp' := ht hp
    simp only [Set.mem_iUnion] at hp'
    obtain ⟨x, hxt, hpx⟩ := hp'
    exact Opens.mem_iSup.mpr ⟨⟨hOf x,
      Set.mem_image_of_mem _ (Finset.mem_coe.mpr hxt)⟩, hpx⟩
  · intro h hh
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hh
    exact ⟨VOf x, hhV x, he x⟩

/-- Glue numerator extension and power-torsion detection over the principal cover. -/
lemma localization {d : ℕ} (hM : Scheme.Modules.IsLocallyFreeOfRank d M)
    (U : X.affineOpens) (f : Γ(X, U.1)) : LocProp M U.1 f := by
  classical
  obtain ⟨s, hs, -, hlocal⟩ := finite_cover M hM U
  apply Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover M U s hs
  · intro h hh g
    obtain ⟨V, hV, e, he⟩ := hlocal h hh
    exact local_localization M e he (U.2.basicOpen h) hV g
  · intro h hh h' hh' g
    obtain ⟨V, hV, e, he⟩ := hlocal h hh
    have haff : IsAffineOpen (X.basicOpen h ⊓ X.basicOpen h') := by
      have := (U.2.basicOpen h).basicOpen
        (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h')
      rwa [Scheme.basicOpen_res] at this
    exact local_localization M e he haff (inf_le_left.trans hV) g

/-- Finite generation descends from the finite cover of basis neighborhoods. -/
lemma finite_sections {d : ℕ} (hM : Scheme.Modules.IsLocallyFreeOfRank d M)
    (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(M, U.1) := by
  classical
  obtain ⟨s, -, hspan, hlocal⟩ := finite_cover M hM U
  let Rₚ (g : s) : Type u := Γ(X, X.basicOpen g.val)
  let Mₚ (g : s) : Type u := Γ(M, X.basicOpen g.val)
  let (g : s) : Module Γ(X, U.1) (Mₚ g) := resModule M (X.basicOpen_le g.val)
  let (g : s) : IsScalarTower Γ(X, U.1) (Rₚ g) (Mₚ g) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have (g : s) : IsLocalization.Away g.val (Rₚ g) := U.2.isLocalization_basicOpen g.val
  let f (g : s) : Γ(M, U.1) →ₗ[Γ(X, U.1)] Mₚ g :=
    resLinear M (X.basicOpen_le g.val)
  have (g : s) : IsLocalizedModule.Away g.val (f g) := by
    apply IsLocalizedModule.Away.mk_of_addCommGroup
    · rw [← (Algebra.lsmul Γ(X, U.1) (A := Rₚ g) Γ(X, U.1) (Mₚ g)).commutes]
      exact (IsLocalization.Away.algebraMap_isUnit g.val).map _
    · intro x
      obtain ⟨n, y, hy⟩ := (localization M hM U g.val).1 x
      exact ⟨n, y, hy.symm⟩
    · exact (localization M hM U g.val).2
  apply Module.Finite.of_localizationSpan_finite' s hspan (Rₚ := Rₚ) f
  intro g
  obtain ⟨V, hV, e, he⟩ := hlocal g.val g.property
  obtain ⟨b, -⟩ := he (X.basicOpen g.val) hV
  exact Module.Finite.of_basis b

end PhilipponFiniteRankSections

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (d : ℕ) (M : X.Modules) (hM : Scheme.Modules.IsLocallyFreeOfRank d M) :
    (OModulePresheaf.ofModules π M).IsCoherent ∧
      (OModulePresheaf.ofModules π M).IsQuasicoherent := by
  constructor
  · intro U
    exact PhilipponFiniteRankSections.finite_sections M hM U
  · intro U f
    exact PhilipponFiniteRankSections.localization M hM U f
