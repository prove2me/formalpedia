-- Prove2me | solution 1 for AlgebraicCurve.exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4e3d158e-a5ff-5b8a-86d6-d353adb9cd2f

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_specMap_subtype_of_liesOverPrime
import Theorems.Thm_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve P2MW.S_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime.AlgebraicCurve TopologicalSpace"

universe v w

universe u

noncomputable section

namespace B12LevelFactor

theorem res_app_congr {X Y : Scheme} {f f' : X ⟶ Y} (e : f = f') (V : Y.Opens) (U : X.Opens)
    (h : U ≤ f ⁻¹ᵁ V) (h' : U ≤ f' ⁻¹ᵁ V) (a : Γ(Y, V)) :
    X.presheaf.map (homOfLE h).op ((f.app V).hom a) = X.presheaf.map (homOfLE h').op ((f'.app V).hom a) := by
  subst e; rfl

theorem res_res {X : Scheme} {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (s : Γ(X, W)) :
    X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op s) = X.presheaf.map (homOfLE (h₁.trans h₂)).op s := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem app_res {X Y : Scheme} (f : X ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W) (s : Γ(Y, W)) :
    (f.app V).hom (Y.presheaf.map (homOfLE hVW).op s) =
      X.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ W from fun x hx => hVW hx)).op ((f.app W).hom s) := by
  have := f.naturality (homOfLE hVW).op
  have h := congrArg (fun φ => φ.hom s) this
  simp only [CommRingCat.comp_apply] at h
  rw [h]
  rfl

end B12LevelFactor

open B12LevelFactor

namespace RoadT

p2m_open "Algebra CategoryTheory.Algebra"

theorem exists_finset_mem_adjoin_image {R : Type*} [CommRing R] {A O T : Type*} [CommRing T] [Algebra R T]
    (α : A → T) (β : O → T) (t : T) (ht : t ∈ Algebra.adjoin R (Set.range α ∪ Set.range β)) :
    ∃ F : Finset O, t ∈ Algebra.adjoin R (Set.range α ∪ β '' (↑F : Set O)) := by
  classical
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨o, rfl⟩
    · exact ⟨∅, Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)⟩
    · exact ⟨{o}, Algebra.subset_adjoin (Or.inr ⟨o, by simp, rfl⟩)⟩
  | algebraMap r => exact ⟨∅, Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF⟩ := hx; obtain ⟨G, hG⟩ := hy
    refine ⟨F ∪ G, Subalgebra.add_mem _ (Algebra.adjoin_mono ?_ hF) (Algebra.adjoin_mono ?_ hG)⟩
    · exact Set.union_subset_union_right _ (Set.image_mono (by simp))
    · exact Set.union_subset_union_right _ (Set.image_mono (by simp))
  | mul x y _ _ hx hy =>
    obtain ⟨F, hF⟩ := hx; obtain ⟨G, hG⟩ := hy
    refine ⟨F ∪ G, Subalgebra.mul_mem _ (Algebra.adjoin_mono ?_ hF) (Algebra.adjoin_mono ?_ hG)⟩
    · exact Set.union_subset_union_right _ (Set.image_mono (by simp))
    · exact Set.union_subset_union_right _ (Set.image_mono (by simp))

theorem exists_finset_forall_fraction_mem_adjoin {R : Type*} [CommRing R] {A O T : Type*} [CommRing T] [Algebra R T]
    (α : A → T) (β : O → T) (hgen : ∀ t : T, t ∈ Algebra.adjoin R (Set.range α ∪ Set.range β))
    (𝔮 : Ideal T) [𝔮.IsPrime] (S : Type*) [CommRing S] [Algebra T S] [IsLocalization.AtPrime S 𝔮]
    (Z : Finset S) :
    ∃ F : Finset O, ∀ z ∈ Z, ∃ y s : T,
      y ∈ Algebra.adjoin R (Set.range α ∪ β '' (↑F : Set O)) ∧ s ∈ Algebra.adjoin R (Set.range α ∪ β '' (↑F : Set O)) ∧
      s ∉ 𝔮 ∧ z * algebraMap T S s = algebraMap T S y := by
  classical
  induction Z using Finset.induction_on with
  | empty => exact ⟨∅, fun z hz => absurd hz (Finset.notMem_empty z)⟩
  | insert z Z hz ih =>
    obtain ⟨F, hF⟩ := ih
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj 𝔮.primeCompl z
    obtain ⟨Fr, hFr⟩ := exists_finset_mem_adjoin_image α β r (hgen r)
    obtain ⟨Fs, hFs⟩ := exists_finset_mem_adjoin_image α β (s : T) (hgen s)
    have mono : ∀ G H : Finset O, G ⊆ H →
        Algebra.adjoin R (Set.range α ∪ β '' (↑G : Set O)) ≤ Algebra.adjoin R (Set.range α ∪ β '' (↑H : Set O)) :=
      fun G H h => Algebra.adjoin_mono (Set.union_subset_union_right _ (Set.image_mono (Finset.coe_subset.2 h)))
    refine ⟨F ∪ Fr ∪ Fs, fun w hw => ?_⟩
    rcases Finset.mem_insert.1 hw with rfl | hw'
    · refine ⟨r, s, mono _ _ (by intro o ho; simp [ho]) hFr, mono _ _ (by intro o ho; simp [ho]) hFs, s.2, hrs⟩
    · obtain ⟨y, s', hy, hs', hs'q, h⟩ := hF w hw'
      exact ⟨y, s', mono _ _ (by intro o ho; simp [ho]) hy, mono _ _ (by intro o ho; simp [ho]) hs', hs'q, h⟩

end RoadT

namespace RoadT

theorem adjoin_le_range_of_factor {R : Type*} [CommRing R] {A O D T TD : Type*}
    [CommRing T] [Algebra R T] [CommRing TD] [Algebra R TD]
    (α : A → T) (β : O → T) (φ : TD →ₐ[R] T) (αD : A → TD) (βD : D → TD) (jD : D → O)
    (hα : ∀ a, φ (αD a) = α a) (hβ : ∀ d, φ (βD d) = β (jD d))
    (F : Set O) (hF : F ⊆ Set.range jD) :
    Algebra.adjoin R (Set.range α ∪ β '' F) ≤ φ.range := by
  refine Algebra.adjoin_le ?_
  rintro t (⟨a, rfl⟩ | ⟨o, ho, rfl⟩)
  · exact ⟨αD a, hα a⟩
  · obtain ⟨d, rfl⟩ := hF ho
    exact ⟨βD d, hβ d⟩

theorem exists_preimage_of_fraction {SD S : Type*} [CommRing SD] [CommRing S] [IsLocalRing SD] [IsLocalRing S]
    (ψ : SD →+* S) [IsLocalHom ψ] (y₀ s₀ : SD) (f : S) (hs : IsUnit (ψ s₀)) (hf : f * ψ s₀ = ψ y₀) :
    ∃ f₀ : SD, ψ f₀ = f := by
  have hs₀ : IsUnit s₀ := (isUnit_map_iff ψ s₀).1 hs
  refine ⟨y₀ * hs₀.unit⁻¹, ?_⟩
  rw [map_mul, ← hf, mul_assoc]
  have : ψ s₀ * ψ (↑hs₀.unit⁻¹ : SD) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [this, mul_one]

end RoadT

namespace RoadT

open scoped TensorProduct

theorem mem_adjoin_of_tensor_surjective {R A O T : Type*} [CommRing R] [CommRing A] [CommRing O] [CommRing T]
    [Algebra R A] [Algebra R O] (ψ : A ⊗[R] O →+* T) (hψ : Function.Surjective ψ)
    (α : A → T) (β : O → T) (hα : ∀ a, ψ (a ⊗ₜ 1) = α a) (hβ : ∀ c, ψ (1 ⊗ₜ c) = β c) (t : T) :
    t ∈ Algebra.adjoin ℤ (Set.range α ∪ Set.range β) := by
  obtain ⟨z, rfl⟩ := hψ t
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | tmul a c =>
    have : a ⊗ₜ[R] c = (a ⊗ₜ[R] (1 : O)) * ((1 : A) ⊗ₜ[R] c) := by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this, map_mul, hα, hβ]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨c, rfl⟩))
  | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy

end RoadT

section PieceABC_t0
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

namespace RoadT
namespace Chart

theorem mem_adjoin_int_tmul {R : Type u} [CommRing R] (A S : Type u) [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    (x : A ⊗[R] S) :
    x ∈ Algebra.adjoin ℤ (Set.range (fun a : A => a ⊗ₜ[R] (1 : S)) ∪ Set.range (fun s : S => (1 : A) ⊗ₜ[R] s)) := by
  induction x using TensorProduct.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | tmul a s =>
    have : a ⊗ₜ[R] s = (a ⊗ₜ[R] (1 : S)) * ((1 : A) ⊗ₜ[R] s) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩))
  | add x y hx hy => exact Subalgebra.add_mem _ hx hy

theorem forall_mem_adjoin_of_ringEquiv {T T' : Type u} [CommRing T] [CommRing T'] (e : T ≃+* T')
    {ι₁ ι₂ : Type u} (g₁ : ι₁ → T) (g₂ : ι₂ → T)
    (h : ∀ t : T, t ∈ Algebra.adjoin ℤ (Set.range g₁ ∪ Set.range g₂)) (t' : T') :
    t' ∈ Algebra.adjoin ℤ (Set.range (fun i => e (g₁ i)) ∪ Set.range (fun i => e (g₂ i))) := by
  obtain ⟨t, rfl⟩ := e.surjective t'
  have ht := h t
  have hmem : e.toRingHom.toIntAlgHom t ∈ (Algebra.adjoin ℤ (Set.range g₁ ∪ Set.range g₂)).map e.toRingHom.toIntAlgHom :=
    Subalgebra.mem_map.2 ⟨t, ht, rfl⟩
  rw [AlgHom.map_adjoin] at hmem
  refine Algebra.adjoin_mono ?_ hmem
  rintro _ ⟨y, (⟨a, rfl⟩ | ⟨o, rfl⟩), rfl⟩
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨o, rfl⟩

theorem specChart_adjoin {R : Type u} [CommRing R] (A S : Type u) [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    (t : Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R S))), ⊤)) :
    t ∈ Algebra.adjoin ℤ
      (Set.range (fun a : Γ(Spec (CommRingCat.of A), ⊤) =>
          (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop a) ∪
       Set.range (fun s : Γ(Spec (CommRingCat.of S), ⊤) =>
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop s)) := by
  set σ := pullbackSpecIso R A S with hσ
  set F := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R S))) with hF
  set G := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R S))) with hG

  let eΓ : Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R S))), ⊤) ≅
      Γ(Spec (CommRingCat.of (A ⊗[R] S)), ⊤) := Scheme.Γ.mapIso σ.symm.op
  have heΓinv : ∀ z, eΓ.inv z = σ.hom.appTop z := fun z => rfl
  let e : (A ⊗[R] S) ≃+* Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R S))), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] S))).symm ≪≫ eΓ.symm).commRingCatIsoToRingEquiv
  have he : ∀ z : A ⊗[R] S, e z = σ.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] S))).inv z) := fun z => rfl

  have hF' := (Iso.inv_comp_eq _).1 (hσ ▸ pullbackSpecIso_inv_fst R A S)
  have hG' := (Iso.inv_comp_eq _).1 (hσ ▸ pullbackSpecIso_inv_snd R A S)

  have happ : ∀ {Y : Scheme.{u}} (φ : Spec (CommRingCat.of (A ⊗[R] S)) ⟶ Y) (z : Γ(Y, ⊤)),
      (σ.hom ≫ φ).appTop z = σ.hom.appTop (φ.appTop z) := by
    intro Y φ z
    have : (σ.hom ≫ φ).appTop = φ.appTop ≫ σ.hom.appTop := by simp
    rw [this, CommRingCat.comp_apply]
  have hgen₁ : ∀ a : A, e (a ⊗ₜ[R] (1 : S)) = F.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := by
    intro a
    rw [he, hF, hF', happ]
    congr 1
    have nat := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := S)))
    have := congrArg (fun φ => CommRingCat.Hom.hom φ a) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    first | exact this | exact this.symm
  have hgen₂ : ∀ s : S, e ((1 : A) ⊗ₜ[R] s) = G.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s) := by
    intro s
    rw [he, hG, hG', happ]
    congr 1
    have nat := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (↑(Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)) : S →+* A ⊗[R] S))
    have := congrArg (fun φ => CommRingCat.Hom.hom φ s) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    first | exact this | exact this.symm
  have h := forall_mem_adjoin_of_ringEquiv e (fun a : A => a ⊗ₜ[R] (1 : S)) (fun s : S => (1 : A) ⊗ₜ[R] s)
    (mem_adjoin_int_tmul A S) t
  refine Algebra.adjoin_mono ?_ h
  rintro _ (⟨a, rfl⟩ | ⟨s, rfl⟩)
  · exact Or.inl ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).inv a, (hgen₁ a).symm⟩
  · exact Or.inr ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).inv s, (hgen₂ s).symm⟩

theorem comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (z : Γ(Z, ⊤)) :
    (f ≫ g).appTop z = f.appTop (g.appTop z) := by
  have : (f ≫ g).appTop = g.appTop ≫ f.appTop := by simp
  rw [this, CommRingCat.comp_apply]

theorem mem_adjoin_of_map {T T' : Type u} [CommRing T] [CommRing T'] (φ : T →+* T')
    {ι₁ ι₂ : Type u} (g₁ : ι₁ → T) (g₂ : ι₂ → T)
    (t : T) (h : t ∈ Algebra.adjoin ℤ (Set.range g₁ ∪ Set.range g₂)) :
    φ t ∈ Algebra.adjoin ℤ (Set.range (fun i => φ (g₁ i)) ∪ Set.range (fun i => φ (g₂ i))) := by
  have hmem : φ.toIntAlgHom t ∈ (Algebra.adjoin ℤ (Set.range g₁ ∪ Set.range g₂)).map φ.toIntAlgHom :=
    Subalgebra.mem_map.2 ⟨t, h, rfl⟩
  rw [AlgHom.map_adjoin] at hmem
  refine Algebra.adjoin_mono ?_ hmem
  rintro _ ⟨y, (⟨a, rfl⟩ | ⟨o, rfl⟩), rfl⟩
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨o, rfl⟩

theorem adjoin_transport_iso {V W Y Z : Scheme.{u}} (κ : V ≅ W)
    (fV : V ⟶ Y) (gV : V ⟶ Z) (fW : W ⟶ Y) (gW : W ⟶ Z) (hf : κ.hom ≫ fW = fV) (hg : κ.hom ≫ gW = gV)
    (hW : ∀ t : Γ(W, ⊤), t ∈ Algebra.adjoin ℤ (Set.range (fun a : Γ(Y, ⊤) => fW.appTop a) ∪ Set.range (fun s : Γ(Z, ⊤) => gW.appTop s)))
    (t : Γ(V, ⊤)) :
    t ∈ Algebra.adjoin ℤ (Set.range (fun a : Γ(Y, ⊤) => fV.appTop a) ∪ Set.range (fun s : Γ(Z, ⊤) => gV.appTop s)) := by
  have ht : t = κ.hom.appTop (κ.inv.appTop t) := by
    rw [← comp_appTop_apply, Iso.hom_inv_id]
    simp
  have h := mem_adjoin_of_map κ.hom.appTop.hom _ _ _ (hW (κ.inv.appTop t))
  rw [← ht] at h
  refine Algebra.adjoin_mono ?_ h
  rintro _ (⟨a, rfl⟩ | ⟨s, rfl⟩)
  · refine Or.inl ⟨a, ?_⟩
    show fV.appTop a = κ.hom.appTop (fW.appTop a)
    rw [← comp_appTop_apply, hf]
  · refine Or.inr ⟨s, ?_⟩
    show gV.appTop s = κ.hom.appTop (gW.appTop s)
    rw [← comp_appTop_apply, hg]

theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (z : Γ(Y, U)) : f.appLE U V e z = g.appLE U V (h ▸ e) z := by
  subst h; rfl

theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) (z : Γ(Y, ⊤)) :
    f.appLE ⊤ ⊤ h z = f.appTop z := by
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

set_option maxHeartbeats 6400000 in

theorem chart_adjoin_pullback {R S : Type u} [CommRing R] [CommRing S] (j : R →+* S)
    {X₀ : Scheme.{u}} (π₀ : X₀ ⟶ Spec (CommRingCat.of R)) (x : ↥(pullback π₀ (Spec.map (CommRingCat.ofHom j)))) :
    ∃ (U₀ : X₀.Opens) (U : (pullback π₀ (Spec.map (CommRingCat.ofHom j))).Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
      (hUle : U ≤ (pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U₀),
      ∀ t : Γ(pullback π₀ (Spec.map (CommRingCat.ofHom j)), U), t ∈ Algebra.adjoin ℤ
        (Set.range (fun a : Γ(X₀, U₀) => (pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE hUle).op
            ((pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).app U₀ a)) ∪
         Set.range (fun c : S => (pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE (le_top (a := U))).op
            ((pullback.snd π₀ (Spec.map (CommRingCat.ofHom j))).appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv c)))) := by
  classical
  letI : Algebra R S := j.toAlgebra
  let 𝒰 := X₀.affineOpenCover.openCover
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 π₀ (Spec.map (CommRingCat.ofHom j))
  let i := 𝒱.idx x
  obtain ⟨v, hv⟩ := 𝒱.covers x
  let Ri : CommRingCat := X₀.affineOpenCover.X i

  let V := 𝒱.X i
  let ι : V ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j)) := 𝒱.f i
  let fV : V ⟶ Spec Ri := pullback.fst (𝒰.f i ≫ π₀) (Spec.map (CommRingCat.ofHom j))
  let gV : V ⟶ Spec (CommRingCat.of S) := pullback.snd (𝒰.f i ≫ π₀) (Spec.map (CommRingCat.ofHom j))
  have hιf : ι ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j)) = fV ≫ 𝒰.f i := by
    show 𝒱.f i ≫ _ = _
    rw [Scheme.Pullback.openCoverOfLeft_f]; exact pullback.lift_fst _ _ _
  have hιg : ι ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = gV := by
    show 𝒱.f i ≫ _ = _
    rw [Scheme.Pullback.openCoverOfLeft_f]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

  let ψ : CommRingCat.of R ⟶ Ri := Spec.preimage (𝒰.f i ≫ π₀)
  letI : Algebra R Ri := ψ.hom.toAlgebra
  have hψ : 𝒰.f i ≫ π₀ = Spec.map (CommRingCat.ofHom (algebraMap R Ri)) := by
    rw [show CommRingCat.ofHom (algebraMap R ↑Ri) = ψ from rfl]
    exact (Spec.map_preimage _).symm
  have hj : Spec.map (CommRingCat.ofHom j) = Spec.map (CommRingCat.ofHom (algebraMap R S)) := rfl
  let κ : V ≅ pullback (Spec.map (CommRingCat.ofHom (algebraMap R Ri))) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    pullback.congrHom hψ hj
  have hκf : κ.hom ≫ pullback.fst _ _ = fV := by
    show (pullback.congrHom hψ hj).hom ≫ _ = _
    rw [pullback.congrHom_hom]; exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hκg : κ.hom ≫ pullback.snd _ _ = gV := by
    show (pullback.congrHom hψ hj).hom ≫ _ = _
    rw [pullback.congrHom_hom]; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hV : ∀ t : Γ(V, ⊤), t ∈ Algebra.adjoin ℤ (Set.range (fun a : Γ(Spec Ri, ⊤) => fV.appTop a) ∪
      Set.range (fun s : Γ(Spec (CommRingCat.of S), ⊤) => gV.appTop s)) :=
    adjoin_transport_iso κ fV gV _ _ hκf hκg (fun t => specChart_adjoin (R := R) Ri S t)

  have hUle : ι ''ᵁ ⊤ ≤ (pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ ((𝒰.f i) ''ᵁ ⊤) := by
    rintro y ⟨w, -, rfl⟩
    show (pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).base (ι.base w) ∈ Set.image (𝒰.f i).base (⊤ : (𝒰.X i).Opens)
    refine ⟨fV.base w, trivial, ?_⟩
    have := congrArg (fun k => k.base w) hιf
    have h__af := this.symm
    simp at h__af
    exact h__af
  have hU : IsAffineOpen (ι ''ᵁ ⊤) := by
    haveI : IsAffine (𝒰.X i) := by change IsAffine (Spec Ri); infer_instance
    haveI : IsAffine V := by
      change IsAffine (pullback (𝒰.f i ≫ π₀) (Spec.map (CommRingCat.ofHom j))); infer_instance
    rw [Scheme.Hom.image_top_eq_opensRange]; exact isAffineOpen_opensRange ι
  refine ⟨(𝒰.f i) ''ᵁ ⊤, ι ''ᵁ ⊤, hU, ⟨v, trivial, hv⟩, hUle, ?_⟩
  intro t

  let eι := ι.appIso ⊤
  have ht : eι.inv (eι.hom t) = t := Iso.hom_inv_id_apply eι t
  have h := mem_adjoin_of_map eι.inv.hom _ _ _ (hV (eι.hom t))
  rw [ht] at h

  have e₁ : (⊤ : (𝒰.X i).Opens) ≤ (𝒰.f i) ⁻¹ᵁ ((𝒰.f i) ''ᵁ ⊤) := fun w _ => ⟨w, trivial, rfl⟩
  have e₂ : (⊤ : V.Opens) ≤ fV ⁻¹ᵁ ⊤ := le_top
  have e₃ : (⊤ : V.Opens) ≤ gV ⁻¹ᵁ ⊤ := le_top
  have e₄ : (⊤ : V.Opens) ≤ ι ⁻¹ᵁ ((pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ ((𝒰.f i) ''ᵁ ⊤)) :=
    fun w _ => hUle ⟨w, trivial, rfl⟩
  have e₅ : (⊤ : V.Opens) ≤ ι ⁻¹ᵁ (ι ''ᵁ ⊤) := fun w _ => ⟨w, trivial, rfl⟩

  have C1 : ∀ a : Γ(X₀, (𝒰.f i) ''ᵁ ⊤),
      eι.hom ((pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE hUle).op
        ((pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).app ((𝒰.f i) ''ᵁ ⊤) a)) =
      fV.appTop ((𝒰.f i).appLE ((𝒰.f i) ''ᵁ ⊤) ⊤ e₁ a) := by
    intro a
    have s1 : eι.hom = ι.appLE (ι ''ᵁ ⊤) ⊤ e₅ := Scheme.Hom.appIso_hom' ι ⊤
    rw [s1, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hιf, ← appLE_top_top fV e₂]
    show _ = ((𝒰.f i).appLE ((𝒰.f i) ''ᵁ ⊤) ⊤ e₁ ≫ fV.appLE ⊤ ⊤ e₂) a
    erw [Scheme.Hom.appLE_comp_appLE fV (𝒰.f i) ((𝒰.f i) ''ᵁ ⊤) ⊤ ⊤ e₁ e₂]

  have C2 : ∀ c' : Γ(Spec (CommRingCat.of S), ⊤),
      eι.hom ((pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE (le_top (a := ι ''ᵁ ⊤))).op
        ((pullback.snd π₀ (Spec.map (CommRingCat.ofHom j))).appTop c')) = gV.appTop c' := by
    intro c'
    have s1 : eι.hom = ι.appLE (ι ''ᵁ ⊤) ⊤ e₅ := Scheme.Hom.appIso_hom' ι ⊤
    rw [s1, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      ← appLE_top_top (pullback.snd π₀ (Spec.map (CommRingCat.ofHom j))) le_top, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hιg, appLE_top_top]
  refine Algebra.adjoin_mono ?_ h
  rintro _ (⟨b, rfl⟩ | ⟨c', rfl⟩)
  · refine Or.inl ⟨((𝒰.f i).appIso ⊤).inv b, ?_⟩
    have hb : (𝒰.f i).appLE ((𝒰.f i) ''ᵁ ⊤) ⊤ e₁ (((𝒰.f i).appIso ⊤).inv b) = b := by
      rw [← Scheme.Hom.appIso_hom']; exact Iso.inv_hom_id_apply _ b
    show (pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE hUle).op
        ((pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).app ((𝒰.f i) ''ᵁ ⊤) (((𝒰.f i).appIso ⊤).inv b)) =
      eι.inv (fV.appTop b)
    have h1 : eι.hom ((pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE hUle).op
        ((pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).app ((𝒰.f i) ''ᵁ ⊤) (((𝒰.f i).appIso ⊤).inv b))) =
        fV.appTop b := by rw [C1, hb]
    rw [← h1]
    exact (Iso.hom_inv_id_apply eι _).symm
  · refine Or.inr ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom c', ?_⟩
    have hc : (Scheme.ΓSpecIso (CommRingCat.of S)).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).hom c') = c' :=
      Iso.hom_inv_id_apply _ c'
    show (pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE (le_top (a := ι ''ᵁ ⊤))).op
        ((pullback.snd π₀ (Spec.map (CommRingCat.ofHom j))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).hom c'))) =
      eι.inv (gV.appTop c')
    rw [hc, ← C2 c']
    exact (Iso.hom_inv_id_apply eι _).symm

end RoadT.Chart

end PieceABC_t0

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel IsCurveOver"
namespace GC1Sol
namespace LevelDVR
p2m_open "AlgebraicCurve"

theorem isDVR_stalk_and_maximalIdeal_eq_span
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (ϖ : D) (hϖ : Irreducible ϖ)
    {κ : Type u} [Field κ] (q : D →+* κ) (hq : Function.Surjective q) (hkerq : RingHom.ker q = Ideal.span {ϖ})
    (hqloc : Spec.map (CommRingCat.ofHom q) (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint D)
    {T Tk : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of D)) [Smooth t]
    (g : Tk ⟶ T) (tk : Tk ⟶ Spec (CommRingCat.of κ)) (H : IsPullback g tk t (Spec.map (CommRingCat.ofHom q)))
    [IsIntegral Tk]
    (hgen : ∀ y : T, y ⤳ g.base (genericPoint Tk) → t.base y = IsLocalRing.closedPoint D → y = g.base (genericPoint Tk)) :
    ∃ _ : IsDomain (T.presheaf.stalk (g.base (genericPoint Tk))),
      IsDiscreteValuationRing (T.presheaf.stalk (g.base (genericPoint Tk))) ∧
      IsLocalRing.maximalIdeal (T.presheaf.stalk (g.base (genericPoint Tk))) =
        Ideal.span {(T.presheaf.germ ⊤ (g.base (genericPoint Tk)) trivial) (t.appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv ϖ))} := by
  set η := g.base (genericPoint Tk) with hη

  have hηs : t.base η = IsLocalRing.closedPoint D := by
    change (g ≫ t).base (genericPoint Tk) = _
    rw [H.w]
    change (Spec.map (CommRingCat.ofHom q)).base (tk.base (genericPoint Tk)) = _
    have : tk.base (genericPoint Tk) = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
    rw [this]
    exact hqloc
  obtain ⟨hdom, hdvr⟩ := AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes D t η hηs hgen
  refine ⟨hdom, hdvr, ?_⟩

  obtain ⟨hsurj, hker⟩ := AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
    q hq t g tk H (genericPoint Tk)
  have hmax : (RingHom.ker (g.stalkMap (genericPoint Tk)).hom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  rw [← IsLocalRing.eq_maximalIdeal hmax, hker, hkerq, Ideal.map_span, Set.image_singleton]
  rfl

end AlgebraicCurve.GC1Sol.LevelDVR

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel IsCurveOver"
namespace GC1Sol
p2m_open "AlgebraicCurve"

namespace FunctionFieldPull

variable {X Y Z : Scheme.{u}}

def pull [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint X)

section

variable [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

theorem pull_germ (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    pull f h (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (h.mem_open U.isOpen hU) (f.app U s) := by
  simp only [pull, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem pull_algebraMap (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y) (x : X)
    (a : Y.presheaf.stalk (f.base x)) :
    pull f h (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  simp only [pull, RingHom.algebraMap_toAlgebra, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply (Y.presheaf)]
  have := Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) x
    ((genericPoint_spec X).specializes trivial) a
  convert this using 2

theorem pull_id : pull (𝟙 X) (specializes_refl _) = 𝟙 _ := by
  simp [pull]

theorem pull_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) ⤳ genericPoint Y)
    (hg : g.base (genericPoint Y) ⤳ genericPoint Z) :
    pull (f ≫ g) ((g.base.hom.map_specializes hf).trans hg) = pull g hg ≫ pull f hf := by
  simp only [pull, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc g (f.base (genericPoint X)) (genericPoint Y) hf]
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

end

variable [IsIntegral X] [IsIntegral Y]

theorem specializes_of_iso (e : X ≅ Y) : e.hom.base (genericPoint X) ⤳ genericPoint Y :=
  (genericPoint_eq_of_isOpenImmersion e.hom).symm ▸ specializes_refl _

theorem specializes_of_iso_inv (e : X ≅ Y) : e.inv.base (genericPoint Y) ⤳ genericPoint X :=
  specializes_of_iso e.symm

def equivOfIso (e : X ≅ Y) : Y.functionField ≃+* X.functionField :=
  (({ hom := pull e.hom (specializes_of_iso e)
      inv := pull e.inv (specializes_of_iso_inv e)
      hom_inv_id := by
        have h := (pull_comp e.inv e.hom (specializes_of_iso_inv e) (specializes_of_iso e)).symm
        rw [h]
        have : ∀ (k : (e.inv ≫ e.hom).base (genericPoint Y) ⤳ genericPoint Y),
            pull (e.inv ≫ e.hom) k = 𝟙 _ := by
          rw [e.inv_hom_id]; intro k; exact pull_id
        exact this _
      inv_hom_id := by
        have h := (pull_comp e.hom e.inv (specializes_of_iso e) (specializes_of_iso_inv e)).symm
        rw [h]
        have : ∀ (k : (e.hom ≫ e.inv).base (genericPoint X) ⤳ genericPoint X),
            pull (e.hom ≫ e.inv) k = 𝟙 _ := by
          rw [e.hom_inv_id]; intro k; exact pull_id
        exact this _ } : Y.functionField ≅ X.functionField)).commRingCatIsoToRingEquiv

theorem equivOfIso_apply (e : X ≅ Y) (a : Y.functionField) :
    equivOfIso e a = pull e.hom (specializes_of_iso e) a := rfl

theorem equivOfIso_symm_apply (e : X ≅ Y) (a : X.functionField) :
    (equivOfIso e).symm a = pull e.inv (specializes_of_iso_inv e) a := rfl

theorem map_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range.map
        (equivOfIso e).toRingHom =
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  haveI : IsIso (e.hom.stalkMap x) := inferInstance
  ext b
  simp only [Subring.mem_map, RingHom.mem_range, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨e.hom.stalkMap x a, (pull_algebraMap e.hom (specializes_of_iso e) x a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', e.hom.stalkMap x a' = a :=
      ⟨inv (e.hom.stalkMap x) a, by
        rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
    exact ⟨_, ⟨a', rfl⟩, pull_algebraMap e.hom (specializes_of_iso e) x a'⟩

theorem image_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e) ''
        ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) =
      ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) := by
  have h := congrArg (fun S : Subring X.functionField => (S : Set X.functionField))
    (map_equivOfIso_range_stalk e x)
  simpa [Subring.coe_map] using h

theorem image_equivOfIso_symm_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e).symm '' ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) =
      ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) := by
  rw [← image_equivOfIso_range_stalk e x, ← Set.image_comp]
  simp

theorem pull_baseToFunctionField {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ cY = cX)
    (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX a := by
  subst hf
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) =
    X.presheaf.germ ⊤ (genericPoint X) trivial _
  rw [pull_germ]
  rfl

theorem equivOfIso_baseToFunctionField {K : Type u} [Field K] (e : X ≅ Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    (hf : e.hom ≫ cY = cX) (a : K) :
    equivOfIso e (baseToFunctionField cY a) = baseToFunctionField cX a :=
  pull_baseToFunctionField e.hom _ cX cY hf a

end FunctionFieldPull

open FunctionFieldPull

section Frame

variable (O : ValuationSubring (AlgebraicClosure ℚ))
  (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O))
  [hXint : IsIntegral X]
  [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]
  [hXL : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom O.subtype)))]

abbrev Xk : Scheme.{0} := pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))

abbrev XL : Scheme.{0} := pullback π (Spec.map (CommRingCat.ofHom O.subtype))

abbrev ιk : Xk O X π ⟶ X := pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))
abbrev ιL : XL O X π ⟶ X := pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))

abbrev ξ : X := (ιk O X π).base (genericPoint ↥(Xk O X π))

def B : Subring X.functionField := (algebraMap (X.presheaf.stalk (ξ O X π)) X.functionField).range

def resXi : X.presheaf.stalk (ξ O X π) ⟶ (Xk O X π).functionField :=
  (ιk O X π).stalkMap (genericPoint ↥(Xk O X π))

theorem resXi_germ (U : X.Opens) (hU : ξ O X π ∈ U) (s : Γ(X, U)) :
    resXi O X π (X.presheaf.germ U (ξ O X π) hU s) =
      (Xk O X π).presheaf.germ ((ιk O X π) ⁻¹ᵁ U) (genericPoint ↥(Xk O X π)) hU ((ιk O X π).app U s) :=
  Scheme.Hom.germ_stalkMap_apply (ιk O X π) U (genericPoint ↥(Xk O X π)) hU s

def constO : ↥O →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv.hom)

theorem isOpenImmersion_fst (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) : IsOpenImmersion (ιL O X π) := by
  haveI := AlgebraicGeometry.isOpenImmersion_specMap_subtype_of_liesOverPrime O p hp hO
  infer_instance

theorem resXi_surjective [SmoothOfRelativeDimension 1 π] :
    Function.Surjective (resXi O X π) :=
  (AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
    (IsLocalRing.residue ↥O) Ideal.Quotient.mk_surjective π (ιk O X π)
    (pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))
    (IsPullback.of_hasPullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))
    (genericPoint ↥(Xk O X π))).1

theorem ker_resXi [SmoothOfRelativeDimension 1 π] :
    RingHom.ker (resXi O X π).hom = IsLocalRing.maximalIdeal (X.presheaf.stalk (ξ O X π)) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (resXi_surjective O X π))

end Frame

section SF1Assembly

open scoped TensorProduct

variable (O : ValuationSubring (AlgebraicClosure ℚ))
  (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O))

theorem chart_adjoin_eq_top
    (O₀ : Type) [CommRing O₀] (j : O₀ →+* ↥O)
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀))
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀] (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)
    (x : X) :
    ∃ (U₀ : X₀.Opens) (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
      (hUle : U ≤ (e₀ ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U₀),
      ∀ t : Γ(X, U), t ∈ Algebra.adjoin ℤ
        (Set.range (fun a : Γ(X₀, U₀) => X.presheaf.map (homOfLE hUle).op
            (((e₀ ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).app U₀).hom a)) ∪
         Set.range (fun c : ↥O => X.presheaf.map (homOfLE (le_top (a := U))).op
            (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv c)))) := by
  classical
  obtain ⟨U₀, U', hU', hxU', hU'le, hgen⟩ := RoadT.Chart.chart_adjoin_pullback j π₀ (e₀.base x)
  have hUle : e₀ ⁻¹ᵁ U' ≤ (e₀ ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U₀ := fun y hy => hU'le hy
  refine ⟨U₀, e₀ ⁻¹ᵁ U', hU'.preimage_of_isIso e₀, hxU', hUle, ?_⟩
  intro t

  let t' : Γ(pullback π₀ (Spec.map (CommRingCat.ofHom j)), U') := inv (e₀.app U') t
  have ht : (e₀.app U').hom t' = t := by
    show (inv (e₀.app U') ≫ e₀.app U').hom t = t
    rw [IsIso.inv_hom_id]; rfl
  have hmap : t ∈ (Algebra.adjoin ℤ _).map (e₀.app U').hom.toIntAlgHom := Subalgebra.mem_map.mpr ⟨t', hgen t', ht⟩
  rw [AlgHom.map_adjoin] at hmap
  refine Algebra.adjoin_mono ?_ hmap
  rintro _ ⟨s, hs | hs, rfl⟩
  · obtain ⟨a, rfl⟩ := hs
    left
    refine ⟨a, ?_⟩

    show X.presheaf.map (homOfLE hUle).op ((e₀ ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).app U₀ a) =
      (e₀.app U') ((pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE hU'le).op _)
    rw [Scheme.Hom.comp_app]
    change (Scheme.Hom.app (pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))) U₀ ≫ e₀.app _ ≫ X.presheaf.map (homOfLE hUle).op) a =
      ((pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE hU'le).op ≫ e₀.app U') _
    rw [e₀.naturality (homOfLE hU'le).op]
    rfl
  · obtain ⟨c, rfl⟩ := hs
    right
    refine ⟨c, ?_⟩
    show X.presheaf.map (homOfLE le_top).op (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv c)) =
      (e₀.app U') ((pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE le_top).op _)
    rw [← he₀, Scheme.Hom.comp_appTop]
    change ((pullback.snd π₀ (Spec.map (CommRingCat.ofHom j))).appTop ≫ e₀.appTop ≫ X.presheaf.map (homOfLE le_top).op) _ =
      ((pullback π₀ (Spec.map (CommRingCat.ofHom j))).presheaf.map (homOfLE le_top).op ≫ e₀.app U') _
    rw [Scheme.Hom.appTop, e₀.naturality (homOfLE (le_top (a := U'))).op]
    rfl

theorem level_factor
    (O₀ : Type) [CommRing O₀] (j : O₀ →+* ↥O)
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀))
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀] (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)
    (D : Type) [CommRing D] (jD : D →+* ↥O) (j₀ : O₀ →+* D) (hfac : jD.comp j₀ = j)
    (U₀ : X₀.Opens) (U : X.Opens) (hUle : U ≤ (e₀ ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U₀) :
    let g : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j₀)) :=
      e₀ ≫ pullback.map π₀ (Spec.map (CommRingCat.ofHom j)) π₀ (Spec.map (CommRingCat.ofHom j₀)) (𝟙 X₀)
        (Spec.map (CommRingCat.ofHom jD)) (𝟙 _) (by simp) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfac]; simp)
    ∃ (UD : (pullback π₀ (Spec.map (CommRingCat.ofHom j₀))).Opens) (hUD : U ≤ g ⁻¹ᵁ UD)
      (αD : Γ(X₀, U₀) → Γ(pullback π₀ (Spec.map (CommRingCat.ofHom j₀)), UD))
      (βD : D → Γ(pullback π₀ (Spec.map (CommRingCat.ofHom j₀)), UD)),
      (∀ a : Γ(X₀, U₀), X.presheaf.map (homOfLE hUD).op ((g.app UD).hom (αD a)) =
          X.presheaf.map (homOfLE hUle).op (((e₀ ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).app U₀).hom a)) ∧
      (∀ d : D, X.presheaf.map (homOfLE hUD).op ((g.app UD).hom (βD d)) =
          X.presheaf.map (homOfLE (le_top (a := U))).op (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv (jD d)))) ∧

      (∀ d : D, βD d = (pullback π₀ (Spec.map (CommRingCat.ofHom j₀))).presheaf.map (homOfLE (le_top (a := UD))).op
          ((pullback.snd π₀ (Spec.map (CommRingCat.ofHom j₀))).appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d))) := by
  intro g
  have hg_fst : g ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀)) = e₀ ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j)) := by
    simp only [g, Category.assoc, pullback.lift_fst, Category.comp_id]
  have hg_snd : g ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j₀)) = π ≫ Spec.map (CommRingCat.ofHom jD) := by
    simp only [g, Category.assoc, pullback.lift_snd, ← he₀]

  have hUD : U ≤ g ⁻¹ᵁ ((pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))) ⁻¹ᵁ U₀) := by
    show U ≤ (g ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))) ⁻¹ᵁ U₀
    rw [hg_fst]; exact hUle
  refine ⟨(pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))) ⁻¹ᵁ U₀, hUD,
    fun a => ((pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))).app U₀).hom a,
    fun d => (pullback π₀ (Spec.map (CommRingCat.ofHom j₀))).presheaf.map
      (homOfLE (le_top (a := (pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))) ⁻¹ᵁ U₀))).op
      ((pullback.snd π₀ (Spec.map (CommRingCat.ofHom j₀))).appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d)),
    ?_, ?_, fun d => rfl⟩
  ·
    intro a
    have e1 : (g.app ((pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))) ⁻¹ᵁ U₀)).hom
        (((pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))).app U₀).hom a) =
        ((g ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))).app U₀).hom a := by
      rw [Scheme.Hom.comp_app]; rfl
    rw [e1]
    exact res_app_congr hg_fst U₀ U hUD hUle a
  ·
    intro d
    rw [app_res g (le_top (a := (pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))) ⁻¹ᵁ U₀))]
    rw [res_res]
    have e2 : (g.app ⊤).hom ((pullback.snd π₀ (Spec.map (CommRingCat.ofHom j₀))).appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d)) =
        ((π ≫ Spec.map (CommRingCat.ofHom jD)).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d) := by
      rw [← hg_snd, Scheme.Hom.comp_appTop]; rfl
    rw [e2]
    have e3 : ((π ≫ Spec.map (CommRingCat.ofHom jD)).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d) =
        (π.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv (jD d)) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      congr 1
      have h := congrArg (fun φ => φ.hom d) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom jD))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact h.symm
    rw [e3]
    rfl

theorem exists_dvr_level (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j) (hjloc : ∀ x : O₀, IsUnit (j x) → IsUnit x)
    (C : Finset ↥O) :
    ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsDiscreteValuationRing D)
      (jD : D →+* ↥O) (_ : Function.Injective jD) (_ : ∀ x : D, IsUnit (jD x) → IsUnit x) (ϖ : D) (_ : Irreducible ϖ)
      (j₀ : O₀ →+* D) (_ : jD.comp j₀ = j),
      ∀ c ∈ C, c ∈ Set.range jD := by
  classical

  let K := FractionRing O₀
  have hjO : Function.Injective ((O.subtype).comp j) := Subtype.val_injective.comp hj
  let ι : K →+* AlgebraicClosure ℚ := IsFractionRing.lift hjO
  letI : Algebra K (AlgebraicClosure ℚ) := ι.toAlgebra
  have hιalg : ∀ c : O₀, algebraMap K (AlgebraicClosure ℚ) (algebraMap O₀ K c) = (j c : AlgebraicClosure ℚ) :=
    fun c => IsFractionRing.lift_algebraMap hjO c
  haveI : CharZero O₀ := (RingHom.charZero_iff hjO).mpr inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O₀ K)

  let S : Set (AlgebraicClosure ℚ) := (fun c : ↥O => (c : AlgebraicClosure ℚ)) '' (C : Set ↥O)
  haveI : Finite ↑S := (C.finite_toSet.image _).to_subtype
  let K₁ : IntermediateField K (AlgebraicClosure ℚ) := IntermediateField.adjoin K S
  have hint : ∀ x ∈ S, IsIntegral K x := by
    intro x _
    have hz : IsAlgebraic ℤ x :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x)
    obtain ⟨f, hf0, hfx⟩ := hz
    have halg : IsAlgebraic K x := by
      refine ⟨f.map (Int.castRingHom K), ?_, ?_⟩
      · exact (Polynomial.map_ne_zero_iff (Int.cast_injective (α := K))).mpr hf0
      · rw [Polynomial.aeval_def, Polynomial.eval₂_map,
          show (algebraMap K (AlgebraicClosure ℚ)).comp (Int.castRingHom K) = algebraMap ℤ (AlgebraicClosure ℚ) from
            RingHom.ext (fun n => by simp), ← Polynomial.aeval_def]
        exact hfx
    exact halg.isIntegral
  haveI : FiniteDimensional K K₁ := IntermediateField.finiteDimensional_adjoin hint
  haveI : Algebra.IsIntegral K K₁ := Algebra.IsIntegral.of_finite K K₁
  haveI : Algebra.IsSeparable K K₁ := Algebra.IsSeparable.of_integral K K₁

  let D : ValuationSubring K₁ := O.comap (algebraMap K₁ (AlgebraicClosure ℚ))
  have hmemD : ∀ x : K₁, x ∈ D ↔ (x : AlgebraicClosure ℚ) ∈ O := fun x => ValuationSubring.mem_comap
  letI : Algebra O₀ K₁ := ((algebraMap K K₁).comp (algebraMap O₀ K)).toAlgebra
  haveI : IsScalarTower O₀ K K₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halgK₁ : ∀ c : O₀, ((algebraMap O₀ K₁ c : K₁) : AlgebraicClosure ℚ) = (j c : AlgebraicClosure ℚ) := fun c => hιalg c
  have hCB : ∀ c : O₀, algebraMap O₀ K₁ c ∈ D := fun c => (hmemD _).mpr (by rw [halgK₁]; exact (j c).2)
  let j₀ : O₀ →+* ↥D := (algebraMap O₀ K₁).codRestrict D hCB
  let jD : ↥D →+* ↥O := ((algebraMap K₁ (AlgebraicClosure ℚ)).comp D.subtype).codRestrict O (fun x => (hmemD x.1).mp x.2)
  have hjD : ∀ x : ↥D, (jD x : AlgebraicClosure ℚ) = ((x : K₁) : AlgebraicClosure ℚ) := fun x => rfl
  have hfac : jD.comp j₀ = j := by
    ext c
    exact halgK₁ c
  have hjDinj : Function.Injective jD := by
    intro x y h
    have := congrArg Subtype.val h
    rw [hjD, hjD] at this
    exact Subtype.ext (Subtype.ext this)

  have hjDloc : ∀ x : ↥D, IsUnit (jD x) → IsUnit x := by
    intro x hx
    obtain ⟨w, hw⟩ := hx
    have hx0 : ((x : K₁) : AlgebraicClosure ℚ) ≠ 0 := by
      rw [← hjD, ← hw]; exact fun h => w.ne_zero (Subtype.ext h)
    have hx0' : (x : K₁) ≠ 0 := fun h => hx0 (by rw [h]; rfl)
    have hxw : ((x : K₁) : AlgebraicClosure ℚ) = ((w : ↥O) : AlgebraicClosure ℚ) := by rw [← hjD, ← hw]
    have hwinv : ((w : ↥O) : AlgebraicClosure ℚ)⁻¹ = (((w⁻¹ : (↥O)ˣ) : ↥O) : AlgebraicClosure ℚ) := by
      symm
      apply eq_inv_of_mul_eq_one_left
      have h : (((w⁻¹ : (↥O)ˣ) : ↥O) * (w : ↥O) : ↥O) = 1 := Units.inv_mul w
      exact_mod_cast congrArg Subtype.val h
    have hinvO : (((x : K₁))⁻¹ : K₁) ∈ D := by
      rw [hmemD]
      change ((x : K₁) : AlgebraicClosure ℚ)⁻¹ ∈ O
      rw [hxw, hwinv]
      exact ((w⁻¹ : (↥O)ˣ) : ↥O).2
    exact ⟨⟨x, ⟨(x : K₁)⁻¹, hinvO⟩, Subtype.ext (mul_inv_cancel₀ hx0'), Subtype.ext (inv_mul_cancel₀ hx0')⟩, rfl⟩
  have hCBmax : ∀ c : O₀, algebraMap O₀ K₁ c ∈ D.nonunits ↔ c ∈ IsLocalRing.maximalIdeal O₀ := by
    intro c
    have hc : algebraMap O₀ K₁ c ∈ D.nonunits ↔ ¬ IsUnit (j₀ c) := by
      rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ValuationSubring.valuation_lt_one_iff,
        ← ValuationSubring.mem_nonunits_iff]
      rfl
    rw [hc, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · exact fun h hu => h (hu.map j₀)
    · intro h hu
      exact h (hjloc c (by rw [← hfac]; exact hu.map jD))
  haveI hDVR : IsDiscreteValuationRing ↥D :=
    ValuationSubring.isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable (C := O₀) K (F := ↥K₁) D hCB hCBmax
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥D
  refine ⟨↥D, inferInstance, inferInstance, hDVR, jD, hjDinj, hjDloc, ϖ, hϖ, j₀, hfac, ?_⟩
  intro c hc
  have hcS : (c : AlgebraicClosure ℚ) ∈ (K₁ : Set (AlgebraicClosure ℚ)) :=
    IntermediateField.subset_adjoin K S ⟨c, by simpa using hc, rfl⟩
  refine ⟨⟨⟨(c : AlgebraicClosure ℚ), hcS⟩, (hmemD _).mpr c.2⟩, Subtype.ext rfl⟩

theorem exists_coeffs_stalk_mem_range
    (O₀ : Type) [CommRing O₀] (j : O₀ →+* ↥O)
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀))
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀] (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)
    (x : X) (S : Finset (X.presheaf.stalk x)) :
    ∃ C : Finset ↥O, ∀ (D : Type) [CommRing D] (jD : D →+* ↥O) (j₀ : O₀ →+* D) (hfac : jD.comp j₀ = j),
      (∀ c ∈ C, c ∈ Set.range jD) →
      ∀ f ∈ S, ∃ f₀ : (pullback π₀ (Spec.map (CommRingCat.ofHom j₀))).presheaf.stalk
          ((e₀ ≫ pullback.map π₀ (Spec.map (CommRingCat.ofHom j)) π₀ (Spec.map (CommRingCat.ofHom j₀)) (𝟙 X₀)
              (Spec.map (CommRingCat.ofHom jD)) (𝟙 _) (by simp) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfac]; simp)).base x),
        (e₀ ≫ pullback.map π₀ (Spec.map (CommRingCat.ofHom j)) π₀ (Spec.map (CommRingCat.ofHom j₀)) (𝟙 X₀)
            (Spec.map (CommRingCat.ofHom jD)) (𝟙 _) (by simp) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfac]; simp)).stalkMap x f₀ = f := by
  classical
  obtain ⟨U₀, U, hU, hxU, hUle, hgen⟩ := chart_adjoin_eq_top O X π O₀ j π₀ e₀ he₀ x

  let x' : U := ⟨x, hxU⟩
  letI := X.presheaf.algebra_section_stalk x'
  haveI hloc := hU.isLocalization_stalk x'
  obtain ⟨F, hF⟩ := RoadT.exists_finset_forall_fraction_mem_adjoin (R := ℤ)
    (fun a : Γ(X₀, U₀) => X.presheaf.map (homOfLE hUle).op
      (((e₀ ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).app U₀).hom a))
    (fun c : ↥O => X.presheaf.map (homOfLE (le_top (a := U))).op (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv c)))
    hgen (hU.primeIdealOf x').asIdeal (X.presheaf.stalk (x' : X)) S
  refine ⟨F, ?_⟩
  intro D _ jD j₀ hfac hC f hf
  obtain ⟨y, s, hy, hs, hsq, hfs⟩ := hF f hf
  obtain ⟨UD, hUD, αD, βD, hα, hβ, -⟩ := level_factor O X π O₀ j π₀ e₀ he₀ D jD j₀ hfac U₀ U hUle

  set g := e₀ ≫ pullback.map π₀ (Spec.map (CommRingCat.ofHom j)) π₀ (Spec.map (CommRingCat.ofHom j₀)) (𝟙 X₀)
      (Spec.map (CommRingCat.ofHom jD)) (𝟙 _) (by simp) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfac]; simp) with hg

  let φ : Γ(pullback π₀ (Spec.map (CommRingCat.ofHom j₀)), UD) →ₐ[ℤ] Γ(X, U) :=
    ((X.presheaf.map (homOfLE hUD).op).hom.comp (g.app UD).hom).toIntAlgHom
  have hle := RoadT.adjoin_le_range_of_factor (R := ℤ)
    (fun a : Γ(X₀, U₀) => X.presheaf.map (homOfLE hUle).op
      (((e₀ ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j))).app U₀).hom a))
    (fun c : ↥O => X.presheaf.map (homOfLE (le_top (a := U))).op (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv c)))
    φ αD βD jD (fun a => hα a) (fun d => hβ d) (↑F : Set ↥O) (fun c hc => hC c hc)
  obtain ⟨yD, hyD⟩ := hle hy
  obtain ⟨sD, hsD⟩ := hle hs
  replace hyD : φ yD = y := hyD
  replace hsD : φ sD = s := hsD

  have hgx : g.base x ∈ UD := hUD hxU
  have hgerm : ∀ t : Γ(pullback π₀ (Spec.map (CommRingCat.ofHom j₀)), UD),
      algebraMap Γ(X, U) (X.presheaf.stalk (x' : X)) (φ t) =
        (g.stalkMap x).hom ((pullback π₀ (Spec.map (CommRingCat.ofHom j₀))).presheaf.germ UD (g.base x) hgx t) := by
    intro t
    show (X.presheaf.germ U x x'.2).hom ((X.presheaf.map (homOfLE hUD).op).hom ((g.app UD).hom t)) = _
    rw [← CommRingCat.comp_apply, X.presheaf.germ_res (homOfLE hUD) x x'.2, Scheme.Hom.germ_stalkMap_apply]
  have hunit : IsUnit ((g.stalkMap x).hom ((pullback π₀ (Spec.map (CommRingCat.ofHom j₀))).presheaf.germ UD (g.base x) hgx sD)) := by
    rw [← hgerm, hsD]
    exact IsLocalization.map_units (M := (hU.primeIdealOf x').asIdeal.primeCompl) (X.presheaf.stalk (x' : X)) ⟨s, hsq⟩
  refine RoadT.exists_preimage_of_fraction (g.stalkMap x).hom
    ((pullback π₀ (Spec.map (CommRingCat.ofHom j₀))).presheaf.germ UD (g.base x) hgx yD)
    ((pullback π₀ (Spec.map (CommRingCat.ofHom j₀))).presheaf.germ UD (g.base x) hgx sD) f hunit ?_
  rw [← hgerm, ← hgerm, hyD, hsD]
  exact hfs

end SF1Assembly

section SF1

variable (O : ValuationSubring (AlgebraicClosure ℚ))
  (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O))

theorem level_specialFibre (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X] [hXk : IsIntegral (Xk O X π)]
    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j)
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀)) [IsProper π₀] [SmoothOfRelativeDimension 1 π₀] [GeometricallyIntegral π₀]
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀] (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)
    (D : Type) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (jD : D →+* ↥O) (hjD : Function.Injective jD) (hjDloc : ∀ x : D, IsUnit (jD x) → IsUnit x)
    (j₀ : O₀ →+* D) (hfac : jD.comp j₀ = j) :
    let XD := pullback π₀ (Spec.map (CommRingCat.ofHom j₀))
    let πD : XD ⟶ Spec (CommRingCat.of D) := pullback.snd π₀ (Spec.map (CommRingCat.ofHom j₀))
    let g : X ⟶ XD := e₀ ≫ pullback.map π₀ (Spec.map (CommRingCat.ofHom j)) π₀ (Spec.map (CommRingCat.ofHom j₀)) (𝟙 X₀)
        (Spec.map (CommRingCat.ofHom jD)) (𝟙 _) (by simp) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfac]; simp)
    let Tk := pullback πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)))
    ∃ _ : IsIntegral Tk,
      g.base (ξ O X π) = (pullback.fst πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)))).base (genericPoint Tk) ∧
      ∀ y : XD, y ⤳ g.base (ξ O X π) → πD.base y = IsLocalRing.closedPoint D → y = g.base (ξ O X π) := by
  intro XD πD g Tk

  haveI hTk : IsIntegral Tk :=
    GeometricallyIntegral.isIntegral_of_subsingleton
      (pullback.snd πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D))))
  haveI : IsLocalHom jD := ⟨hjDloc⟩

  let g' := pullback.map π₀ (Spec.map (CommRingCat.ofHom j)) π₀ (Spec.map (CommRingCat.ofHom j₀)) (𝟙 X₀)
      (Spec.map (CommRingCat.ofHom jD)) (𝟙 _) (by simp) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfac]; simp)
  have hg : g = e₀ ≫ g' := rfl
  have sq : IsPullback g' (pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)))
      (pullback.snd π₀ (Spec.map (CommRingCat.ofHom j₀))) (Spec.map (CommRingCat.ofHom jD)) := by
    have e1 : g' ≫ pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀)) = pullback.fst π₀ (Spec.map (CommRingCat.ofHom j)) := by
      simp only [g', pullback.lift_fst, Category.comp_id]
    have e2 : Spec.map (CommRingCat.ofHom jD) ≫ Spec.map (CommRingCat.ofHom j₀) = Spec.map (CommRingCat.ofHom j) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfac]
    refine IsPullback.of_right (h₁₂ := pullback.fst π₀ (Spec.map (CommRingCat.ofHom j₀))) (v₁₃ := π₀)
      (h₂₂ := Spec.map (CommRingCat.ofHom j₀)) ?_ ?_ (IsPullback.of_hasPullback _ _)
    · rw [e1, e2]; exact IsPullback.of_hasPullback _ _
    · simp only [g', pullback.lift_snd]

  have hclosedO : ∀ z : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥O)),
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).base z = IsLocalRing.closedPoint ↥O := by
    intro z; rw [Subsingleton.elim z (IsLocalRing.closedPoint _)]; exact IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥O)
  have hclosedD : ∀ z : Spec (CommRingCat.of (IsLocalRing.ResidueField D)),
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D))).base z = IsLocalRing.closedPoint D := by
    intro z; rw [Subsingleton.elim z (IsLocalRing.closedPoint _)]; exact IsLocalRing.comap_closedPoint (IsLocalRing.residue D)
  have hπξ : π.base (ξ O X π) = IsLocalRing.closedPoint ↥O := by
    change (ιk O X π ≫ π).base (genericPoint (Xk O X π)) = _
    rw [pullback.condition]
    exact hclosedO _

  have hFO : ∀ t : X, π.base t = IsLocalRing.closedPoint ↥O → ξ O X π ⤳ t := by
    intro t ht
    have : t ∈ Set.range (ιk O X π).base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨IsLocalRing.closedPoint _, by rw [ht]; exact hclosedO _⟩
    obtain ⟨t', rfl⟩ := this
    exact ((genericPoint_spec (Xk O X π)).specializes trivial).map (ιk O X π).base.hom.continuous

  have hFD : ∀ y : XD, πD.base y = IsLocalRing.closedPoint D →
      (pullback.fst πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)))).base (genericPoint Tk) ⤳ y := by
    intro y hy
    have : y ∈ Set.range (pullback.fst πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)))).base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨IsLocalRing.closedPoint _, by rw [hy]; exact hclosedD _⟩
    obtain ⟨y', rfl⟩ := this
    exact ((genericPoint_spec Tk).specializes trivial).map
      (pullback.fst πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)))).base.hom.continuous

  have hgξ : πD.base (g.base (ξ O X π)) = IsLocalRing.closedPoint D := by
    change (g ≫ πD).base (ξ O X π) = _
    have : g ≫ πD = π ≫ Spec.map (CommRingCat.ofHom jD) := by
      simp only [hg, g', πD, Category.assoc, pullback.lift_snd]; rw [← Category.assoc, he₀]
    rw [this]
    change (Spec.map (CommRingCat.ofHom jD)).base (π.base (ξ O X π)) = _
    rw [hπξ]
    exact IsLocalRing.comap_closedPoint jD

  have hγ : g.base (ξ O X π) ⤳ (pullback.fst πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)))).base (genericPoint Tk) := by
    have hγD : πD.base ((pullback.fst πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)))).base (genericPoint Tk)) =
        (Spec.map (CommRingCat.ofHom jD)).base (IsLocalRing.closedPoint ↥O) := by
      change (pullback.fst πD _ ≫ πD).base (genericPoint Tk) = _
      rw [pullback.condition]
      exact (hclosedD _).trans (IsLocalRing.comap_closedPoint jD).symm
    obtain ⟨t, ht, hts⟩ := Scheme.exists_preimage_of_isPullback sq _ _ hγD

    let t₀ : X := (inv e₀).base t
    have ht₀ : e₀.base t₀ = t := by
      change (inv e₀ ≫ e₀).base t = t; rw [IsIso.inv_hom_id]; rfl
    have hπt₀ : π.base t₀ = IsLocalRing.closedPoint ↥O := by
      rw [← he₀]; change (pullback.snd π₀ _).base (e₀.base t₀) = _; rw [ht₀]; exact hts
    have := (hFO t₀ hπt₀).map g.base.hom.continuous
    rw [hg] at this ⊢
    change (g').base (e₀.base (ξ O X π)) ⤳ _
    have h2 : (e₀ ≫ g').base t₀ = (pullback.fst πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)))).base (genericPoint Tk) := by
      change g'.base (e₀.base t₀) = _; rw [ht₀]; exact ht
    rw [← h2]
    exact this
  have heq : g.base (ξ O X π) = (pullback.fst πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)))).base (genericPoint Tk) :=
    (hγ.antisymm (hFD _ hgξ)).eq
  refine ⟨hTk, heq, ?_⟩
  intro y hy hyD
  exact (hy.antisymm (heq ▸ hFD y hyD)).eq

theorem stalk_covering_by_dvr_levels
    (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X] [hXk : IsIntegral (Xk O X π)]
    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j) (hju : ∀ n : ℕ, ¬ p ∣ n → IsUnit ((n : ℕ) : O₀))
    (hjloc : ∀ x : O₀, IsUnit (j x) → IsUnit x)
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀)) [IsProper π₀] [SmoothOfRelativeDimension 1 π₀] [GeometricallyIntegral π₀]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O₀))) π₀)
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀] (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)
    (S : Finset (X.presheaf.stalk (ξ O X π))) :
    ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsDiscreteValuationRing D)
      (jD : D →+* ↥O) (_ : Function.Injective jD) (_ : ∀ x : D, IsUnit (jD x) → IsUnit x) (ϖ : D) (_ : Irreducible ϖ)
      (XD : Scheme.{0}) (πD : XD ⟶ Spec (CommRingCat.of D))
      (g : X ⟶ XD) (_ : g ≫ πD = π ≫ Spec.map (CommRingCat.ofHom jD)),

      (∃ _ : IsDomain (XD.presheaf.stalk (g.base (ξ O X π))), IsDiscreteValuationRing (XD.presheaf.stalk (g.base (ξ O X π))) ∧
        IsLocalRing.maximalIdeal (XD.presheaf.stalk (g.base (ξ O X π))) =
          Ideal.span {(XD.presheaf.germ ⊤ (g.base (ξ O X π)) trivial) (πD.appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv ϖ))}) ∧

      (∀ f ∈ S, ∃ f₀ : XD.presheaf.stalk (g.base (ξ O X π)), g.stalkMap (ξ O X π) f₀ = f) ∧

      (∀ d : D, g.stalkMap (ξ O X π) ((XD.presheaf.germ ⊤ (g.base (ξ O X π)) trivial) (πD.appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d)))
        = (X.presheaf.germ ⊤ (ξ O X π) trivial) (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv (jD d)))) := by

  obtain ⟨C, hC⟩ := exists_coeffs_stalk_mem_range O X π O₀ j π₀ e₀ he₀ (ξ O X π) S
  obtain ⟨D, _, _, _, jD, hjD, hjDloc, ϖ, hϖ, j₀, hfac, hCD⟩ := exists_dvr_level O p hp hO O₀ j hj hjloc C
  obtain ⟨hTk, hξD, hgen⟩ := level_specialFibre O X π p hp hO O₀ j hj π₀ e₀ he₀ D jD hjD hjDloc j₀ hfac

  let XD := pullback π₀ (Spec.map (CommRingCat.ofHom j₀))
  let πD : XD ⟶ Spec (CommRingCat.of D) := pullback.snd π₀ (Spec.map (CommRingCat.ofHom j₀))
  let g : X ⟶ XD := e₀ ≫ pullback.map π₀ (Spec.map (CommRingCat.ofHom j)) π₀ (Spec.map (CommRingCat.ofHom j₀)) (𝟙 X₀)
      (Spec.map (CommRingCat.ofHom jD)) (𝟙 _) (by simp) (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfac]; simp)
  have hgπ : g ≫ πD = π ≫ Spec.map (CommRingCat.ofHom jD) := by
    simp only [g, πD, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, he₀]
  refine ⟨D, inferInstance, inferInstance, inferInstance, jD, hjD, hjDloc, ϖ, hϖ, XD, πD, g, hgπ, ?_, ?_, ?_⟩
  ·
    haveI := hTk
    haveI : Smooth π₀ := SmoothOfRelativeDimension.smooth 1 π₀
    have hmax : IsLocalRing.maximalIdeal D = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    have hkerq : RingHom.ker (IsLocalRing.residue D) = Ideal.span {ϖ} := by rw [IsLocalRing.ker_residue, hmax]
    have hqloc : Spec.map (CommRingCat.ofHom (IsLocalRing.residue D)) (IsLocalRing.closedPoint (IsLocalRing.ResidueField D)) =
        IsLocalRing.closedPoint D := IsLocalRing.comap_closedPoint (IsLocalRing.residue D)
    have key := AlgebraicCurve.GC1Sol.LevelDVR.isDVR_stalk_and_maximalIdeal_eq_span D ϖ hϖ (IsLocalRing.residue D)
      Ideal.Quotient.mk_surjective hkerq hqloc πD (pullback.fst πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D))))
      (pullback.snd πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D))))
      (IsPullback.of_hasPullback πD (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D))))
      (by rw [← hξD]; exact hgen)
    rw [← hξD] at key
    exact key
  ·
    exact hC D jD j₀ hfac hCD
  ·
    intro d
    rw [Scheme.Hom.germ_stalkMap_apply]
    have hnat : (Spec.map (CommRingCat.ofHom jD)).appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d) =
        (Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv (jD d) := by
      have h := congrArg (fun φ : CommRingCat.of D ⟶ _ => φ.hom d)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom jD))
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
      exact h.symm
    have h2 : g.app ⊤ (πD.appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d)) =
        π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv (jD d)) := by
      change (g ≫ πD).appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d) = _
      rw [hgπ]
      change π.appTop ((Spec.map (CommRingCat.ofHom jD)).appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv d)) = _
      rw [hnat]
    rw [h2]
    rfl

end SF1

section Core

variable (O : ValuationSubring (AlgebraicClosure ℚ))
  (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O))

theorem VR_core (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X] [hXk : IsIntegral (Xk O X π)]
    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j)
    (hju : ∀ n : ℕ, ¬ p ∣ n → IsUnit ((n : ℕ) : O₀))
    (hjloc : ∀ x : O₀, IsUnit (j x) → IsUnit x)
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀)) [IsProper π₀]
    [SmoothOfRelativeDimension 1 π₀] [GeometricallyIntegral π₀]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O₀))) π₀)
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π) :
    ∃ V : ValuationSubring X.functionField, V.toSubring = B O X π ∧

      (∀ a : ↥O, constO O X π a ∈ V) ∧
      (∀ a : ↥O, V.valuation (constO O X π a) < 1 ↔ a ∈ IsLocalRing.maximalIdeal ↥O) ∧

      (∀ f : X.functionField, f ≠ 0 → ∃ (a : ↥O) (u : ↥V), a ≠ 0 ∧ IsUnit u ∧
        (f = constO O X π a * (u : X.functionField) ∨ f * constO O X π a = (u : X.functionField))) ∧

      (∀ f : X.functionField, f ∈ V → (V.valuation f < 1 ↔
        ∃ (a : ↥O) (g : X.functionField), a ∈ IsLocalRing.maximalIdeal ↥O ∧ g ∈ V ∧ f = constO O X π a * g)) := by
  classical
  let ι : X.presheaf.stalk (ξ O X π) →+* X.functionField := algebraMap (X.presheaf.stalk (ξ O X π)) X.functionField
  have hιinj : Function.Injective ι := IsFractionRing.injective (X.presheaf.stalk (ξ O X π)) X.functionField
  have hB : ∀ x : X.functionField, x ∈ B O X π ↔ ∃ s, ι s = x := fun x => Iff.rfl

  let cX : ↥O →+* X.presheaf.stalk (ξ O X π) :=
    (X.presheaf.germ ⊤ (ξ O X π) trivial).hom.comp (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv.hom)
  have hcX : ∀ a : ↥O, ι (cX a) = constO O X π a := by
    intro a
    change (X.presheaf.germ ⊤ (ξ O X π) trivial ≫ X.presheaf.stalkSpecializes _) _ = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
    rfl

  have h5 := AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
      (IsLocalRing.residue ↥O) IsLocalRing.residue_surjective π (ιk O X π)
      (pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))
      (IsPullback.of_hasPullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))
      (genericPoint ↥(Xk O X π))
  have hmS : IsLocalRing.maximalIdeal (X.presheaf.stalk (ξ O X π)) = (IsLocalRing.maximalIdeal ↥O).map cX := by
    change IsLocalRing.maximalIdeal (X.presheaf.stalk (ξ O X π)) = (IsLocalRing.maximalIdeal ↥O).map
      ((X.presheaf.germ ⊤ (ξ O X π) trivial).hom.comp (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv.hom))
    rw [← IsLocalRing.ker_residue (R := ↥O), ← h5.2]
    exact (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ h5.1)).symm
  have hcXmax : ∀ a : ↥O, cX a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (ξ O X π)) ↔ a ∈ IsLocalRing.maximalIdeal ↥O := by
    intro a
    constructor
    · intro h
      by_contra ha
      have hu : IsUnit a := by rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at ha
      exact (IsLocalRing.mem_maximalIdeal _).mp h (hu.map cX)
    · intro h; rw [hmS]; exact Ideal.mem_map_of_mem _ h

  have hlevel : ∀ s t : X.presheaf.stalk (ξ O X π), ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsDiscreteValuationRing D)
      (jD : D →+* ↥O) (_ : Function.Injective jD) (_ : ∀ x : D, IsUnit (jD x) → IsUnit x) (ϖ : D) (_ : Irreducible ϖ)
      (SD : Type) (_ : CommRing SD) (_ : IsDomain SD) (_ : IsDiscreteValuationRing SD) (φ : SD →+* X.presheaf.stalk (ξ O X π))
      (ϖ' : SD) (_ : Irreducible ϖ') (_ : φ ϖ' = cX (jD ϖ)),
      (∃ s₀, φ s₀ = s) ∧ (∃ t₀, φ t₀ = t) := by
    intro s t
    obtain ⟨D, _, _, _, jD, hjD, hjDloc, ϖ, hϖ, XD, πD, g, hg, ⟨_, hdvr, hmax⟩, hcov, hconst⟩ :=
      stalk_covering_by_dvr_levels O X π p hp hO O₀ j hj hju hjloc π₀ ε₀ e₀ he₀ ({s, t} : Finset _)
    haveI := hdvr
    refine ⟨D, inferInstance, inferInstance, inferInstance, jD, hjD, hjDloc, ϖ, hϖ,
      XD.presheaf.stalk (g.base (ξ O X π)), inferInstance, inferInstance, hdvr, (g.stalkMap (ξ O X π)).hom,
      (XD.presheaf.germ ⊤ (g.base (ξ O X π)) trivial) (πD.appTop ((Scheme.ΓSpecIso (CommRingCat.of D)).inv ϖ)),
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax, hconst ϖ, ?_, ?_⟩
    · obtain ⟨s₀, hs₀⟩ := hcov s (by simp); exact ⟨s₀, hs₀⟩
    · obtain ⟨t₀, ht₀⟩ := hcov t (by simp); exact ⟨t₀, ht₀⟩

  have hpair : ∀ s t : X.presheaf.stalk (ξ O X π), s ≠ 0 → t ≠ 0 →
      ∃ (ϖO : ↥O) (_ : ϖO ≠ 0) (_ : ϖO ∈ IsLocalRing.maximalIdeal ↥O) (u v : X.presheaf.stalk (ξ O X π)) (_ : IsUnit u) (_ : IsUnit v)
        (m n : ℕ), s = u * cX ϖO ^ m ∧ t = v * cX ϖO ^ n := by
    intro s t hs ht
    obtain ⟨D, _, _, _, jD, hjD, hjDloc, ϖ, hϖ, SD, _, _, _, φ, ϖ', hϖ', hφϖ, ⟨s₀, rfl⟩, ⟨t₀, rfl⟩⟩ := hlevel s t
    have hs₀ : s₀ ≠ 0 := fun h => hs (by rw [h, map_zero])
    have ht₀ : t₀ ≠ 0 := fun h => ht (by rw [h, map_zero])
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs₀ hϖ'
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht₀ hϖ'
    refine ⟨jD ϖ, ?_, ?_, φ u, φ v, u.isUnit.map φ, v.isUnit.map φ, m, n, ?_, ?_⟩
    · exact fun h => hϖ.ne_zero (hjD (by rw [h, map_zero]))
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun h => hϖ.not_isUnit (hjDloc ϖ h)
    · rw [hu, map_mul, map_pow, hφϖ]
    · rw [hv, map_mul, map_pow, hφϖ]

  have hmem_or : ∀ x : X.functionField, x ∈ B O X π ∨ x⁻¹ ∈ B O X π := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (ξ O X π)) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hιb : ι b ≠ 0 := (map_ne_zero_iff ι hιinj).mpr hb0
    by_cases ha0 : a = 0
    · left; rw [hB]; exact ⟨0, by rw [map_zero, ha0, map_zero, zero_div]⟩
    have hιa : ι a ≠ 0 := (map_ne_zero_iff ι hιinj).mpr ha0
    obtain ⟨ϖO, hϖ0, -, u, v, hu, hv, m, n, rfl, rfl⟩ := hpair a b ha0 hb0
    obtain ⟨v', hv'⟩ := hv
    obtain ⟨u', hu'⟩ := hu
    rcases le_or_gt n m with hnm | hnm
    · left; rw [hB]
      refine ⟨u * (v'⁻¹ : (X.presheaf.stalk (ξ O X π))ˣ) * cX ϖO ^ (m - n), ?_⟩
      rw [eq_div_iff hιb, ← map_mul]
      congr 1
      rw [← hv']
      calc u * ((v'⁻¹ : (X.presheaf.stalk (ξ O X π))ˣ) : X.presheaf.stalk (ξ O X π)) * cX ϖO ^ (m - n) * ((v' : (X.presheaf.stalk (ξ O X π))ˣ) * cX ϖO ^ n)
          = u * (cX ϖO ^ (m - n) * cX ϖO ^ n) * (((v'⁻¹ : (X.presheaf.stalk (ξ O X π))ˣ) : X.presheaf.stalk (ξ O X π)) * v') := by ring
        _ = u * cX ϖO ^ m := by rw [Units.inv_mul, mul_one, ← pow_add, Nat.sub_add_cancel hnm]
    · right; rw [hB]
      refine ⟨v * (u'⁻¹ : (X.presheaf.stalk (ξ O X π))ˣ) * cX ϖO ^ (n - m), ?_⟩
      rw [inv_div, eq_div_iff hιa, ← map_mul]
      congr 1
      rw [← hu']
      calc v * ((u'⁻¹ : (X.presheaf.stalk (ξ O X π))ˣ) : X.presheaf.stalk (ξ O X π)) * cX ϖO ^ (n - m) * ((u' : (X.presheaf.stalk (ξ O X π))ˣ) * cX ϖO ^ m)
          = v * (cX ϖO ^ (n - m) * cX ϖO ^ m) * (((u'⁻¹ : (X.presheaf.stalk (ξ O X π))ˣ) : X.presheaf.stalk (ξ O X π)) * u') := by ring
        _ = v * cX ϖO ^ n := by rw [Units.inv_mul, mul_one, ← pow_add, Nat.sub_add_cancel hnm.le]
  let V : ValuationSubring X.functionField := ⟨B O X π, hmem_or⟩
  have hVmem : ∀ x : X.functionField, x ∈ V ↔ ∃ s, ι s = x := fun x => Iff.rfl

  let eSV : X.presheaf.stalk (ξ O X π) ≃+* ↥V :=
    RingEquiv.ofBijective (ι.codRestrict V (fun s => (hVmem _).mpr ⟨s, rfl⟩))
      ⟨fun a b h => hιinj (congrArg Subtype.val h), fun y => by obtain ⟨s, hs⟩ := (hVmem y.1).mp y.2; exact ⟨s, Subtype.ext hs⟩⟩
  have heSV : ∀ s, (eSV s : X.functionField) = ι s := fun s => rfl
  have hunitV : ∀ s, IsUnit (eSV s) ↔ IsUnit s :=
    fun s => ⟨fun h => by simpa using h.map eSV.symm, fun h => h.map eSV⟩
  have hvalV : ∀ s, V.valuation (ι s) < 1 ↔ ¬ IsUnit s := by
    intro s
    rw [← heSV, ← ValuationSubring.valuation_lt_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunitV]
  refine ⟨V, rfl, ?_, ?_, ?_, ?_⟩
  ·
    intro a; exact (hVmem _).mpr ⟨cX a, hcX a⟩
  ·
    intro a
    rw [← hcX, hvalV, ← hcXmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  ·
    intro f hf
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (ξ O X π)) f
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by rintro rfl; exact hf (by rw [map_zero, zero_div])
    have hιb : ι b ≠ 0 := (map_ne_zero_iff ι hιinj).mpr hb0
    obtain ⟨ϖO, hϖ0, -, u, v, hu, hv, m, n, rfl, rfl⟩ := hpair a b ha0 hb0
    obtain ⟨v', rfl⟩ := hv
    obtain ⟨u', rfl⟩ := hu
    have hcn : ∀ k : ℕ, ι (cX ϖO ^ k) = constO O X π (ϖO ^ k) := fun k => by rw [map_pow, map_pow, hcX]
    let w : ↥V := eSV ((u' : X.presheaf.stalk (ξ O X π)) * ((v'⁻¹ : (X.presheaf.stalk (ξ O X π))ˣ) : X.presheaf.stalk (ξ O X π)))
    have hw : IsUnit w := (hunitV _).mpr ((u'.isUnit).mul (v'⁻¹).isUnit)
    have hwval : (w : X.functionField) * ι (v' : X.presheaf.stalk (ξ O X π)) = ι (u' : X.presheaf.stalk (ξ O X π)) := by
      rw [heSV, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rcases le_or_gt n m with hnm | hnm
    · refine ⟨ϖO ^ (m - n), w, pow_ne_zero _ hϖ0, hw, Or.inl ?_⟩
      rw [div_eq_iff hιb, map_mul, map_mul, ← hcn, ← hwval]
      rw [show cX ϖO ^ m = cX ϖO ^ (m - n) * cX ϖO ^ n by rw [← pow_add, Nat.sub_add_cancel hnm], map_mul]
      ring
    · refine ⟨ϖO ^ (n - m), w, pow_ne_zero _ hϖ0, hw, Or.inr ?_⟩
      rw [div_mul_eq_mul_div, div_eq_iff hιb, map_mul, map_mul, ← hcn, ← hwval]
      rw [show cX ϖO ^ n = cX ϖO ^ (n - m) * cX ϖO ^ m by rw [← pow_add, Nat.sub_add_cancel hnm.le], map_mul]
      ring
  ·
    intro f hf
    obtain ⟨s, rfl⟩ := (hVmem f).mp hf
    constructor
    · intro hlt
      have hsu : ¬ IsUnit s := (hvalV s).mp hlt
      obtain ⟨D, _, _, _, jD, hjD, hjDloc, ϖ, hϖ, SD, _, _, _, φ, ϖ', hϖ', hφϖ, ⟨s₀, rfl⟩, -⟩ := hlevel s s
      have hs₀ : ¬ IsUnit s₀ := fun h => hsu (h.map φ)
      have hmem : s₀ ∈ Ideal.span {ϖ'} := by
        rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').mp hϖ']
        exact (IsLocalRing.mem_maximalIdeal _).mpr hs₀
      obtain ⟨g₀, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
      refine ⟨jD ϖ, ι (φ g₀), ?_, (hVmem _).mpr ⟨φ g₀, rfl⟩, ?_⟩
      · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun h => hϖ.not_isUnit (hjDloc ϖ h)
      · rw [map_mul, map_mul, hφϖ, hcX, mul_comm]
    · rintro ⟨a, g, ha, hg, hfg⟩
      rw [hfg, map_mul]
      have h1 : V.valuation (constO O X π a) < 1 := by
        rw [← hcX, hvalV, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hcXmax]
        exact ha
      calc V.valuation (constO O X π a) * V.valuation g ≤ V.valuation (constO O X π a) * 1 :=
            mul_le_mul_right ((V.valuation_le_one_iff g).mpr hg) _
        _ = V.valuation (constO O X π a) := mul_one _
        _ < 1 := h1

end Core

section Transport

variable (O : ValuationSubring (AlgebraicClosure ℚ))
  (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O))
  [hXint : IsIntegral X]
  [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]
  [hXL : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom O.subtype)))]

theorem specializes_of_isOpenImmersion {U Y : Scheme.{0}} [IsIntegral U] [IsIntegral Y] (f : U ⟶ Y)
    [IsOpenImmersion f] : f.base (genericPoint U) ⤳ genericPoint Y :=
  (genericPoint_eq_of_isOpenImmersion f).symm ▸ specializes_refl _

scoped instance isIso_pull_of_isOpenImmersion {U Y : Scheme.{0}} [IsIntegral U] [IsIntegral Y] (f : U ⟶ Y)
    [IsOpenImmersion f] : IsIso (pull f (specializes_of_isOpenImmersion f)) := by
  have h1 : IsIso (Y.presheaf.stalkSpecializes (specializes_of_isOpenImmersion f)) := by
    have key : ∀ (a b : Y) (hab : a = b) (h : a ⤳ b), IsIso (Y.presheaf.stalkSpecializes h) := by
      rintro a b rfl h
      rw [show Y.presheaf.stalkSpecializes h = 𝟙 _ from TopCat.Presheaf.stalkSpecializes_refl Y.presheaf a]
      infer_instance
    exact key _ _ (genericPoint_eq_of_isOpenImmersion f) _
  have h2 : IsIso (f.stalkMap (genericPoint U)) := inferInstance
  unfold pull
  exact IsIso.comp_isIso

def eqvL [IsOpenImmersion (ιL O X π)] : X.functionField ≃+* (XL O X π).functionField :=
  (asIso (pull (ιL O X π) (specializes_of_isOpenImmersion (ιL O X π)))).commRingCatIsoToRingEquiv

theorem eqvL_apply [IsOpenImmersion (ιL O X π)] (a : X.functionField) :
    eqvL O X π a = pull (ιL O X π) (specializes_of_isOpenImmersion (ιL O X π)) a := rfl

variable (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F]
  (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
  (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
  (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
  (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
  (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]

def toF [IsOpenImmersion (ιL O X π)] : X.functionField ≃+* F :=
  ((eqvL O X π).trans (equivOfIso (asIso e))).trans 𝔐.ffEquiv.symm

def toK : (Xk O X π).functionField ≃+* K :=
  (equivOfIso (asIso ek)).trans 𝔐k.ffEquiv.symm

theorem toF_germ [IsOpenImmersion (ιL O X π)] (U : X.Opens) [Nonempty U]
    [Nonempty ((e ≫ ιL O X π) ⁻¹ᵁ U)] (s : Γ(X, U)) :
    toF O X π F 𝔐 e (X.germToFunctionField U s) =
      𝔐.ffEquiv.symm (𝔐.C.germToFunctionField ((e ≫ ιL O X π) ⁻¹ᵁ U) ((e ≫ ιL O X π).app U s)) := by
  show 𝔐.ffEquiv.symm (equivOfIso (asIso e) (eqvL O X π (X.germToFunctionField U s))) = _
  congr 1
  rw [eqvL_apply, equivOfIso_apply]
  change pull (asIso e).hom _ (pull (ιL O X π) _ (X.presheaf.germ U (genericPoint X) _ s)) = _
  rw [pull_germ, pull_germ]
  rfl

theorem toK_resXi_germ (U : X.Opens) (hU : ξ O X π ∈ U) [Nonempty ((ek ≫ ιk O X π) ⁻¹ᵁ U)] (s : Γ(X, U)) :
    toK O X π K 𝔐k ek (resXi O X π (X.presheaf.germ U (ξ O X π) hU s)) =
      𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField ((ek ≫ ιk O X π) ⁻¹ᵁ U) ((ek ≫ ιk O X π).app U s)) := by
  rw [resXi_germ]
  show 𝔐k.ffEquiv.symm (equivOfIso (asIso ek) _) = _
  congr 1
  rw [equivOfIso_apply]
  change pull (asIso ek).hom _ ((Xk O X π).presheaf.germ _ (genericPoint _) _ _) = _
  rw [pull_germ]
  rfl

end Transport

section Assembly

variable (O : ValuationSubring (AlgebraicClosure ℚ))
  (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O))
  [hXint : IsIntegral X]
  [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]
  [hXL : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom O.subtype)))]
  (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F]
  (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
  (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
  (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
  (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
  (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]

omit hXk hXL in

theorem algebraMap_stalk_germ (U : X.Opens) (x : X) (hx : x ∈ U) [Nonempty U] (s : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = X.germToFunctionField U s := by
  change (X.presheaf.germ U x hx ≫ X.presheaf.stalkSpecializes _) s = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

omit hXk hXL in
theorem algebraMap_stalk_injective (x : X) :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
  IsFractionRing.injective (X.presheaf.stalk x) X.functionField

theorem nonempty_preimage_ιL [IsOpenImmersion (ιL O X π)] (U : X.Opens) [hU : Nonempty U] :
    Nonempty ((e ≫ ιL O X π) ⁻¹ᵁ U) := by
  haveI : IsIntegral 𝔐.C := 𝔐.isIntegral

  have hη : genericPoint X ∈ U := ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have h1 : (e ≫ ιL O X π).base (genericPoint 𝔐.C) = genericPoint X := by
    change (ιL O X π).base (e.base (genericPoint 𝔐.C)) = genericPoint X
    rw [genericPoint_eq_of_isOpenImmersion e, genericPoint_eq_of_isOpenImmersion (ιL O X π)]
  exact ⟨⟨genericPoint 𝔐.C, show (e ≫ ιL O X π).base (genericPoint 𝔐.C) ∈ U from h1 ▸ hη⟩⟩

theorem xi_mem_of_nonempty (U : X.Opens) [hU : Nonempty ((ek ≫ ιk O X π) ⁻¹ᵁ U)] : ξ O X π ∈ U := by
  haveI : IsIntegral 𝔐k.C := 𝔐k.isIntegral
  have hη : genericPoint 𝔐k.C ∈ (ek ≫ ιk O X π) ⁻¹ᵁ U :=
    ((genericPoint_spec 𝔐k.C).mem_open_set_iff ((ek ≫ ιk O X π) ⁻¹ᵁ U).isOpen).mpr (by simpa using hU)
  have h1 : (ek ≫ ιk O X π).base (genericPoint 𝔐k.C) = ξ O X π := by
    change (ιk O X π).base (ek.base (genericPoint 𝔐k.C)) = ξ O X π
    rw [genericPoint_eq_of_isOpenImmersion ek]
  exact h1 ▸ hη

theorem toF_constO [IsOpenImmersion (ιL O X π)]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase) (a : ↥O) :
    toF O X π F 𝔐 e (constO O X π a) = algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) := by
  haveI : IsIntegral 𝔐.C := 𝔐.isIntegral

  have hnat : (Spec.map (CommRingCat.ofHom O.subtype)).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv (a : AlgebraicClosure ℚ) := by
    have h := congrArg (fun φ : CommRingCat.of ↥O ⟶ _ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom O.subtype))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
    exact h.symm
  have h1 : pull (ιL O X π) (specializes_of_isOpenImmersion (ιL O X π)) (constO O X π a) =
      baseToFunctionField (pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype))) (a : AlgebraicClosure ℚ) := by
    change pull (ιL O X π) _ (X.presheaf.germ ⊤ (genericPoint X) trivial (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a))) = _
    rw [pull_germ]
    have h2 : (ιL O X π).app ⊤ (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a)) =
        (pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv (a : AlgebraicClosure ℚ)) := by
      change ((ιL O X π) ≫ π).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a) = _
      rw [pullback.condition]
      change (pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype))).appTop
        ((Spec.map (CommRingCat.ofHom O.subtype)).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a)) = _
      rw [hnat]
    rw [h2]
    rfl
  show 𝔐.ffEquiv.symm (equivOfIso (asIso e) (eqvL O X π (constO O X π a))) = _
  rw [eqvL_apply, h1, equivOfIso_baseToFunctionField (asIso e) 𝔐.toBase _ he, ← 𝔐.ffEquiv_algebraMap,
    RingEquiv.symm_apply_apply]

theorem toK_resXi_constO
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase) (a : ↥O) :
    toK O X π K 𝔐k ek (resXi O X π (X.presheaf.germ ⊤ (ξ O X π) trivial
      (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a)))) =
      algebraMap (IsLocalRing.ResidueField ↥O) K (IsLocalRing.residue ↥O a) := by
  haveI : IsIntegral 𝔐k.C := 𝔐k.isIntegral
  have hnat : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥O))).inv (IsLocalRing.residue ↥O a) := by
    have h := congrArg (fun φ : CommRingCat.of ↥O ⟶ _ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue ↥O)))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
    exact h.symm
  rw [resXi_germ]
  have h2 : (ιk O X π).app ⊤ (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a)) =
      (pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥O))).inv (IsLocalRing.residue ↥O a)) := by
    change ((ιk O X π) ≫ π).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a) = _
    rw [pullback.condition]
    change (pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).appTop
      ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a)) = _
    rw [hnat]
  rw [h2]
  change toK O X π K 𝔐k ek (baseToFunctionField (pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))
    (IsLocalRing.residue ↥O a)) = _
  show 𝔐k.ffEquiv.symm (equivOfIso (asIso ek) _) = _
  rw [equivOfIso_baseToFunctionField (asIso ek) 𝔐k.toBase _ hek, ← 𝔐k.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]

omit hXL in
theorem constO_eq_algebraMap_germ (a : ↥O) :
    constO O X π a = algebraMap (X.presheaf.stalk (ξ O X π)) X.functionField
      (X.presheaf.germ ⊤ (ξ O X π) trivial (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a))) := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  rw [algebraMap_stalk_germ]
  rfl

end Assembly

end AlgebraicCurve.GC1Sol
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime.AlgebraicCurve.GC1Sol"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime.AlgebraicCurve.GC1Sol"

theorem solution
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j)
    (hju : ∀ n : ℕ, ¬ p ∣ n → IsUnit ((n : ℕ) : O₀))

    (hjloc : ∀ x : O₀, IsUnit (j x) → IsUnit x)
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀)) [IsProper π₀]
    [SmoothOfRelativeDimension 1 π₀] [GeometricallyIntegral π₀]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O₀))) π₀)
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)

    (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase)

    (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase)
    :
    ∃ (𝒪F : ValuationSubring F) (res : ↥𝒪F →+* K),

      (∀ f : F, f ∈ 𝒪F ↔
      ∃ (U : X.Opens)
        (hξ : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
                (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s t : X.presheaf.obj (Opposite.op U)),
        IsUnit (X.presheaf.germ U _ hξ t) ∧
        f * 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s))) ∧

      (∀ (U : X.Opens)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (_ : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U))
        (hs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F),
        res ⟨_, hs⟩ =
          𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
            (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom s))) ∧

      Function.Surjective res ∧ RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F ∧

      (∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) F c ∈ 𝒪F ↔ c ∈ O) ∧

      (∀ f : F, f ≠ 0 → ∃ c : AlgebraicClosure ℚ, ∃ h : c • f ∈ 𝒪F, res ⟨c • f, h⟩ ≠ 0) ∧

      (∀ a : ↥O, ∃ h : algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) ∈ 𝒪F,
        res ⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), h⟩ =
          algebraMap (IsLocalRing.ResidueField ↥O) K (IsLocalRing.residue ↥O a)) := by

  haveI : IsIntegral 𝔐.C := 𝔐.isIntegral
  haveI : IsIntegral 𝔐k.C := 𝔐k.isIntegral
  haveI hXL : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom O.subtype))) := IsIntegral.of_isIso e
  haveI hOI : IsOpenImmersion (GC1Sol.ιL O X π) := GC1Sol.isOpenImmersion_fst O X π p hp hO
  obtain ⟨V, hVB, hVconst, hVdom, hVe1, hVmgen⟩ := GC1Sol.VR_core O X π p hp hO O₀ j hj hju hjloc π₀ ε₀ e₀ he₀

  let φ : X.functionField ≃+* F := GC1Sol.toF O X π F 𝔐 e
  let ψ : (GC1Sol.Xk O X π).functionField ≃+* K := GC1Sol.toK O X π K 𝔐k ek

  let 𝒪F : ValuationSubring F := V.comap φ.symm.toRingHom
  have hmem : ∀ f : F, f ∈ 𝒪F ↔ φ.symm f ∈ V := fun f => Iff.rfl
  have hBmem : ∀ g : X.functionField, g ∈ V ↔
      ∃ a : X.presheaf.stalk (GC1Sol.ξ O X π), algebraMap _ X.functionField a = g := by
    intro g
    rw [← ValuationSubring.mem_toSubring, hVB]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩

  have hsec : ∀ f : ↥𝒪F, ∃ a : X.presheaf.stalk (GC1Sol.ξ O X π), algebraMap _ X.functionField a = φ.symm (f : F) :=
    fun f => (hBmem _).1 ((hmem _).1 f.2)
  choose sec hsec' using hsec
  have sec_mul : ∀ f g : ↥𝒪F, sec (f * g) = sec f * sec g := by
    intro f g
    apply GC1Sol.algebraMap_stalk_injective X
    rw [map_mul, hsec', hsec', hsec']
    simp
  have sec_add : ∀ f g : ↥𝒪F, sec (f + g) = sec f + sec g := by
    intro f g
    apply GC1Sol.algebraMap_stalk_injective X
    rw [map_add, hsec', hsec', hsec']
    simp
  have sec_one : sec 1 = 1 := by
    apply GC1Sol.algebraMap_stalk_injective X
    rw [map_one, hsec']
    simp
  have sec_zero : sec 0 = 0 := by
    apply GC1Sol.algebraMap_stalk_injective X
    rw [map_zero, hsec']
    simp
  let secHom : ↥𝒪F →+* X.presheaf.stalk (GC1Sol.ξ O X π) :=
    { toFun := sec, map_one' := sec_one, map_mul' := sec_mul, map_zero' := sec_zero, map_add' := sec_add }
  let res : ↥𝒪F →+* K := ψ.toRingHom.comp ((GC1Sol.resXi O X π).hom.comp secHom)
  have hres_def : ∀ f : ↥𝒪F, res f = ψ (GC1Sol.resXi O X π (sec f)) := fun f => rfl

  have sec_inj : Function.Injective sec := by
    intro f g hfg
    have h1 := hsec' f
    rw [hfg, hsec'] at h1
    exact Subtype.ext (φ.symm.injective h1.symm)
  have sec_surj : Function.Surjective sec := by
    intro a
    have ha : φ (algebraMap _ X.functionField a) ∈ 𝒪F := by
      rw [hmem, RingEquiv.symm_apply_apply]; exact (hBmem _).2 ⟨a, rfl⟩
    refine ⟨⟨_, ha⟩, ?_⟩
    apply GC1Sol.algebraMap_stalk_injective X
    rw [hsec']
    simp
  let secEquiv : ↥𝒪F ≃+* X.presheaf.stalk (GC1Sol.ξ O X π) := RingEquiv.ofBijective secHom ⟨sec_inj, sec_surj⟩
  have secEquiv_apply : ∀ f, secEquiv f = sec f := fun f => rfl

  have hφconst : ∀ a : ↥O, φ.symm (algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ)) = GC1Sol.constO O X π a := by
    intro a
    rw [← GC1Sol.toF_constO O X π F 𝔐 e he a]
    exact φ.symm_apply_apply _
  have hprolong : ∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) F c ∈ 𝒪F ↔ c ∈ O := by
    intro c
    constructor
    · intro hc
      by_contra hcO
      have hc0 : c ≠ 0 := by rintro rfl; exact hcO O.zero_mem

      have hinv : c⁻¹ ∈ O := (O.mem_or_inv_mem c).resolve_left hcO
      have hinvm : (⟨c⁻¹, hinv⟩ : ↥O) ∈ IsLocalRing.maximalIdeal ↥O := by
        rw [ValuationSubring.valuation_lt_one_iff]
        have hgt : ¬ O.valuation c ≤ 1 := fun h => hcO ((O.valuation_le_one_iff c).1 h)
        show O.valuation c⁻¹ < 1
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ (lt_of_not_ge hgt)
      have hlt := (hVdom ⟨c⁻¹, hinv⟩).2 hinvm

      have hcV : φ.symm (algebraMap (AlgebraicClosure ℚ) F c) ∈ V := (hmem _).1 hc
      have hprod : φ.symm (algebraMap (AlgebraicClosure ℚ) F c) * GC1Sol.constO O X π ⟨c⁻¹, hinv⟩ = 1 := by
        rw [← hφconst, ← map_mul, ← map_mul, mul_inv_cancel₀ hc0, map_one, map_one]
      have h1 : V.valuation (φ.symm (algebraMap (AlgebraicClosure ℚ) F c)) ≤ 1 := (V.valuation_le_one_iff _).2 hcV
      have := V.valuation.map_mul (φ.symm (algebraMap (AlgebraicClosure ℚ) F c)) (GC1Sol.constO O X π ⟨c⁻¹, hinv⟩)
      rw [hprod, Valuation.map_one] at this
      have h2 : V.valuation (φ.symm (algebraMap (AlgebraicClosure ℚ) F c)) *
          V.valuation (GC1Sol.constO O X π ⟨c⁻¹, hinv⟩) < 1 :=
        calc _ ≤ 1 * V.valuation (GC1Sol.constO O X π ⟨c⁻¹, hinv⟩) := mul_le_mul_left h1 _
          _ = _ := one_mul _
          _ < 1 := hlt
      rw [← this] at h2
      exact lt_irrefl _ h2
    · intro hc
      rw [hmem, hφconst ⟨c, hc⟩]
      exact hVconst ⟨c, hc⟩
  have hsurj : Function.Surjective res := by
    intro y
    obtain ⟨a, ha⟩ := GC1Sol.resXi_surjective O X π (ψ.symm y)
    obtain ⟨f, hf⟩ := sec_surj a
    exact ⟨f, by rw [hres_def, hf, ha, RingEquiv.apply_symm_apply]⟩
  have hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F := by
    ext f
    rw [RingHom.mem_ker, hres_def, map_eq_zero_iff _ ψ.injective, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [show (GC1Sol.resXi O X π (sec f) = 0) ↔ sec f ∈ RingHom.ker (GC1Sol.resXi O X π).hom from Iff.rfl,
      GC1Sol.ker_resXi O X π, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← secEquiv_apply]
    exact (isUnit_map_iff secEquiv f).not
  have hunit_res : ∀ x : ↥𝒪F, IsUnit x → res x ≠ 0 := by
    intro x hx h0
    have : x ∈ RingHom.ker res := h0
    rw [hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
    exact this hx

  have hgermF : ∀ (U : X.Opens) [Nonempty U] [Nonempty ((e ≫ GC1Sol.ιL O X π) ⁻¹ᵁ U)] (s : Γ(X, U)),
      𝔐.ffEquiv.symm (𝔐.C.germToFunctionField ((e ≫ GC1Sol.ιL O X π) ⁻¹ᵁ U) ((e ≫ GC1Sol.ιL O X π).app U s)) =
        φ (X.germToFunctionField U s) :=
    fun U _ _ s => (GC1Sol.toF_germ O X π F 𝔐 e U s).symm
  have hconst_ne : ∀ a : ↥O, a ≠ 0 → GC1Sol.constO O X π a ≠ 0 := by
    intro a ha h0
    have := GC1Sol.toF_constO O X π F 𝔐 e he a
    rw [h0, map_zero] at this
    have h2 : (a : AlgebraicClosure ℚ) = 0 := (map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) F).injective).1 this.symm
    exact ha (ZeroMemClass.coe_eq_zero.1 h2)
  refine ⟨𝒪F, res, ?_, ?_, hsurj, hker, hprolong, ?_, ?_⟩
  ·
    intro f
    constructor
    · intro hf
      obtain ⟨U, hξU, s0, hs0⟩ := X.presheaf.germ_exist (sec ⟨f, hf⟩)
      haveI : Nonempty U := ⟨⟨_, hξU⟩⟩
      haveI hne := GC1Sol.nonempty_preimage_ιL O X π F 𝔐 e U
      refine ⟨U, hξU, hne, s0, 1, by rw [map_one]; exact isUnit_one, ?_⟩
      rw [hgermF, hgermF, map_one, map_one, mul_one, ← GC1Sol.algebraMap_stalk_germ X U (GC1Sol.ξ O X π) hξU s0, hs0, hsec']
      exact (φ.apply_symm_apply f).symm
    · rintro ⟨U, hξU, hne, s0, t0, hunit, heq⟩
      haveI : Nonempty U := ⟨⟨_, hξU⟩⟩
      haveI := hne
      rw [hgermF, hgermF] at heq
      obtain ⟨w, hw⟩ := hunit
      have hgt : X.germToFunctionField U t0 = algebraMap _ X.functionField (w : X.presheaf.stalk (GC1Sol.ξ O X π)) := by
        rw [hw, GC1Sol.algebraMap_stalk_germ X U (GC1Sol.ξ O X π) hξU t0]
      have hgt0 : X.germToFunctionField U t0 ≠ 0 := by
        rw [hgt, map_ne_zero_iff _ (GC1Sol.algebraMap_stalk_injective X _)]
        exact w.ne_zero
      rw [hmem, hBmem]
      refine ⟨X.presheaf.germ U (GC1Sol.ξ O X π) hξU s0 * ↑w⁻¹, ?_⟩
      apply mul_right_cancel₀ hgt0
      rw [map_mul, GC1Sol.algebraMap_stalk_germ X U (GC1Sol.ξ O X π) hξU s0, mul_assoc, hgt, ← map_mul,
        Units.inv_mul, map_one, mul_one]
      apply φ.injective
      rw [map_mul, φ.apply_symm_apply, ← hgt]
      exact heq.symm
  ·
    intro U hne1 hne2 s0 hs
    haveI := hne1; haveI := hne2
    have hξU : GC1Sol.ξ O X π ∈ U := GC1Sol.xi_mem_of_nonempty O X π K 𝔐k ek U
    haveI : Nonempty U := ⟨⟨_, hξU⟩⟩
    have hsec_eq : sec ⟨_, hs⟩ = X.presheaf.germ U (GC1Sol.ξ O X π) hξU s0 := by
      apply GC1Sol.algebraMap_stalk_injective X
      rw [hsec', GC1Sol.algebraMap_stalk_germ X U (GC1Sol.ξ O X π) hξU s0]
      change φ.symm (𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _ ((e ≫ GC1Sol.ιL O X π).app U s0))) =
        X.germToFunctionField U s0
      rw [hgermF, φ.symm_apply_apply]
    rw [hres_def, hsec_eq]
    exact GC1Sol.toK_resXi_germ O X π K 𝔐k ek U hξU s0
  ·
    intro f hf
    have hg : φ.symm f ≠ 0 := by rwa [map_ne_zero_iff _ φ.symm.injective]
    obtain ⟨a, u, ha, hu, hcase⟩ := hVe1 (φ.symm f) hg
    obtain ⟨u', hu'⟩ := hu

    have key : ∀ c : AlgebraicClosure ℚ, φ.symm (c • f) = (u : X.functionField) →
        ∃ h : c • f ∈ 𝒪F, res ⟨c • f, h⟩ ≠ 0 := by
      intro c hc
      have hcf : c • f ∈ 𝒪F := by rw [hmem, hc]; exact u.2

      have hinv : φ ((u'⁻¹ : (↥V)ˣ) : ↥V) ∈ 𝒪F := by
        rw [hmem, φ.symm_apply_apply]; exact SetLike.coe_mem _
      have hmul : (u : X.functionField) * (((u'⁻¹ : (↥V)ˣ) : ↥V) : X.functionField) = 1 := by
        rw [← hu']
        exact_mod_cast congrArg (fun z : ↥V => (z : X.functionField)) u'.mul_inv
      refine ⟨hcf, hunit_res _ (isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, ?_⟩)⟩
      apply Subtype.ext
      apply φ.symm.injective
      show φ.symm ((c • f) * φ ((u'⁻¹ : (↥V)ˣ) : ↥V)) = φ.symm 1
      rw [map_mul, hc, φ.symm_apply_apply, map_one]
      exact hmul
    rcases hcase with hA | hB
    ·
      refine ⟨((a : AlgebraicClosure ℚ))⁻¹, ?_⟩
      apply key
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hφconst, hA, ← mul_assoc, inv_mul_cancel₀ (hconst_ne a ha), one_mul]
    ·
      refine ⟨(a : AlgebraicClosure ℚ), ?_⟩
      apply key
      rw [Algebra.smul_def, map_mul, hφconst, mul_comm, hB]
  ·
    intro a
    refine ⟨(hprolong _).2 a.2, ?_⟩
    rw [hres_def]
    have : sec ⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), (hprolong _).2 a.2⟩ =
        X.presheaf.germ ⊤ (GC1Sol.ξ O X π) trivial (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a)) := by
      apply GC1Sol.algebraMap_stalk_injective X
      rw [hsec', ← GC1Sol.constO_eq_algebraMap_germ]
      exact hφconst a
    rw [this]
    exact GC1Sol.toK_resXi_constO O X π K 𝔐k ek hek a

end S_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime
end P2MW
export P2MW.S_AlgebraicCurve_exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime (solution)
