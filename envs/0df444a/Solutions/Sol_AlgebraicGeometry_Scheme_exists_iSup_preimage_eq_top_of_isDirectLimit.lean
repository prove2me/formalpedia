-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_iSup_preimage_eq_top_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a3ac4b11-eb06-53d5-a6b5-2071e560ecd2

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
import Theorems.Thm_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace LimitIsoFil

private def _root_.AlgebraicGeometry.Scheme.Hom.appInf {X Y : Scheme.{u}} (π : Y ⟶ X) (V W : X.Opens) :
    Γ(X, V ⊓ W) ⟶ Γ(Y, π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W) :=
  π.app (V ⊓ W)

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit.AlgebraicGeometry.Scheme.Hom.appInf" "AlgebraicGeometry.Scheme.Hom.appInf"
p2m_open "AlgebraicGeometry.Scheme.Modules"

private theorem _root_.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf {X Y : Scheme.{u}} (π : Y ⟶ X) {W' V W : X.Opens}
    (h : W' ≤ V ⊓ W) : π ⁻¹ᵁ W' ≤ π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W := π.preimage_mono h

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf" "AlgebraicGeometry.Scheme.Hom.preimage_mono_inf"
lemma appInf_res {X Y : Scheme.{u}} (π : Y ⟶ X) (V W W' : X.Opens) (h : W' ≤ V ⊓ W) (t : Γ(X, V ⊓ W)) :
    Y.presheaf.map (homOfLE (π.preimage_mono_inf h)).op (π.appInf V W t) =
      π.app W' (X.presheaf.map (homOfLE h).op t) := by
  have e := congrArg (fun k => (ConcreteCategory.hom k) t) (π.naturality (homOfLE h).op)
  simp only [CategoryTheory.comp_apply] at e
  exact e.symm

lemma res_res {X : Scheme.{u}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op s) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

lemma cocycle_res {X Y : Scheme.{u}} (π : Y ⟶ X) {V W W' : X.Opens} (h : W' ≤ V ⊓ W) (t₁ t₂ : Γ(X, V ⊓ W))
    (uV : Γ(Y, π ⁻¹ᵁ V)) (uW : Γ(Y, π ⁻¹ᵁ W))
    (hc : π.appInf V W t₁ * Y.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V)).op uV =
      Y.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ W)).op uW * π.appInf V W t₂) :
    π.app W' (X.presheaf.map (homOfLE h).op t₁) *
        Y.presheaf.map (homOfLE (π.preimage_mono (h.trans inf_le_left))).op uV =
      Y.presheaf.map (homOfLE (π.preimage_mono (h.trans inf_le_right))).op uW *
        π.app W' (X.presheaf.map (homOfLE h).op t₂) := by
  have e := congrArg (Y.presheaf.map (homOfLE (π.preimage_mono_inf h)).op) hc
  rw [map_mul, map_mul, appInf_res, appInf_res, res_res, res_res] at e
  exact e

lemma map_swap {K : Type u} [CommRing K] {A A' B B' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra K A] [Algebra K A'] [Algebra K B] [Algebra K B'] (ψ : A →ₐ[K] A') (ρ : B →ₐ[K] B') (x : A ⊗[K] B) :
    Algebra.TensorProduct.map ψ (AlgHom.id K B') (Algebra.TensorProduct.map (AlgHom.id K A) ρ x) =
      Algebra.TensorProduct.map (AlgHom.id K A') ρ (Algebra.TensorProduct.map ψ (AlgHom.id K B) x) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  simp only [AlgHom.comp_id, AlgHom.id_comp]

lemma map_one_tmul {K : Type u} [CommRing K] {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra K A] [Algebra K A'] [Algebra K B] (ψ : A →ₐ[K] A') (b : B) :
    Algebra.TensorProduct.map ψ (AlgHom.id K B) ((1 : A) ⊗ₜ[K] b) = (1 : A') ⊗ₜ[K] b := by
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

lemma exists_ge₂ {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)] {α β : Type*} [Finite α] [Finite β]
    (f : α → J) (g : β → J) : ∃ m : J, (∀ a, f a ≤ m) ∧ ∀ b, g b ≤ m := by
  classical
  haveI := Fintype.ofFinite α; haveI := Fintype.ofFinite β
  obtain ⟨m, hm⟩ := Finset.exists_le (Finset.univ.image f ∪ Finset.univ.image g)
  exact ⟨m, fun a => hm _ (Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_univ a))),
    fun b => hm _ (Finset.mem_union_right _ (Finset.mem_image_of_mem g (Finset.mem_univ b)))⟩

lemma nonempty_iso_pullback_of_fac {X Y Z : Scheme.{u}} (h : X ⟶ Y) (π : Y ⟶ Z) (p : X ⟶ Z) (hp : h ≫ π = p)
    (L₁ L₂ : Z.Modules)
    (e : Nonempty ((Scheme.Modules.pullback π).obj L₁ ≅ (Scheme.Modules.pullback π).obj L₂)) :
    Nonempty ((Scheme.Modules.pullback p).obj L₁ ≅ (Scheme.Modules.pullback p).obj L₂) := by
  obtain ⟨e⟩ := e
  exact ⟨((Scheme.Modules.pullbackComp h π).app L₁ ≪≫ (Scheme.Modules.pullbackCongr hp).app L₁).symm ≪≫
    (Scheme.Modules.pullback h).mapIso e ≪≫
    ((Scheme.Modules.pullbackComp h π).app L₂ ≪≫ (Scheme.Modules.pullbackCongr hp).app L₂)⟩

end LimitIsoFil

open LimitIsoFil in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {κ : Type u} (W : κ → X.Opens)
    (hcov : (⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W k) = ⊤) :
    ∃ (j : ι) (hij : i ≤ j), (⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) = ⊤ := by
  classical
  haveI : CompactSpace ↥(Spec (CommRingCat.of (G i))) := (inferInstance : CompactSpace (PrimeSpectrum (G i)))
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace fX

  let J : Type u := {j : ι // i ≤ j}
  haveI : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  haveI : IsDirected J (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  letI algK : ∀ j : J, Algebra (G i) (G j.1) := fun j => (φ i j.1 j.2).toAlgebra
  letI algR : Algebra (G i) R := (g i).toAlgebra
  letI algGR : ∀ j : J, Algebra (G j.1) R := fun j => (g j.1).toAlgebra
  haveI hST : ∀ j : J, IsScalarTower (G i) (G j.1) R := fun j =>
    IsScalarTower.of_algebraMap_eq (fun r => (IsDirectLimit.compatibility (f := fun i j h => ⇑(φ i j h))
      (g := fun i => ⇑(g i)) i j.1 j.2 r).symm)
  let f' : ∀ j k : J, j ≤ k → G j.1 →ₐ[G i] G k.1 := fun j k h =>
    { toRingHom := φ j.1 k.1 h
      commutes' := fun r => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) j.2 h r }
  haveI hDS : DirectedSystem (fun j : J => G j.1) (fun j k h => ⇑(f' j k h)) :=
    ⟨fun j x => DirectedSystem.map_self (f := fun i j h => ⇑(φ i j h)) x,
     fun k j l hlj hjk x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) hlj hjk x⟩
  have hR' : IsDirectLimit (fun j k h => ⇑(f' j k h)) (fun j : J => ⇑(algebraMap (G j.1) R)) := by
    refine ⟨fun x => ?_, fun j k x y hxy => ?_, fun j k h x => ?_⟩
    · obtain ⟨i', y, hy⟩ := hR.surj x
      obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i i'
      exact ⟨⟨k, hik⟩, φ i' k hi'k y, by rw [← hy]; exact hR.compatibility i' k hi'k y⟩
    · obtain ⟨l, hjl, hkl, e⟩ := hR.inj j.1 k.1 x y hxy
      exact ⟨⟨l, j.2.trans hjl⟩, hjl, hkl, e⟩
    · exact hR.compatibility j.1 k.1 h x

  letI instK : ∀ V : X.Opens, Algebra (G i) Γ(X, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom fX V
  letI instKR : ∀ W : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).Opens,
      Algebra (G i) Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))), W) := fun W =>
    Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))) ≫ fX) W
  obtain ⟨εR, hεaff, hε1, -, hε2⟩ :=
    AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen (G i) fX R

  have hDL : ∀ V : X.Opens, ∃ _ : DirectedSystem (fun j : J => G j.1 ⊗[G i] Γ(X, V))
      (fun j k h => ⇑(Algebra.TensorProduct.map (f' j k h) (AlgHom.id (G i) Γ(X, V)))),
      IsDirectLimit (fun j k h => ⇑(Algebra.TensorProduct.map (f' j k h) (AlgHom.id (G i) Γ(X, V))))
        (fun j : J => ⇑(Algebra.TensorProduct.map (IsScalarTower.toAlgHom (G i) (G j.1) R)
          (AlgHom.id (G i) Γ(X, V)))) := fun V =>
    Algebra.TensorProduct.isDirectLimit_map_of_isDirectLimit (G i) (fun j : J => G j.1) f' R hR' Γ(X, V)
  choose hDSv hDLv using hDL

  let γR : ∀ (V : X.Opens) (hV : IsAffineOpen V),
      Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ V) ≃ₐ[G i]
      R ⊗[G i] Γ(X, V) := fun V hV => (εR V hV).trans (Algebra.TensorProduct.comm (G i) Γ(X, V) R)
  have γR1 : ∀ (V : X.Opens) (hV : IsAffineOpen V) (s : Γ(X, V)),
      γR V hV ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).app V s) =
        (1 : R) ⊗ₜ[G i] s := by
    intro V hV s
    change Algebra.TensorProduct.comm (G i) _ R (εR V hV _) = _
    erw [hε1 V hV s]
    exact Algebra.TensorProduct.comm_tmul _ _ _
  have γR2 : ∀ (V V' : X.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
      (s : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (AlgHom.id (G i) R) (Scheme.TwoAffineOpenCover.restrictAlgHom fX hle) (γR V hV s) =
        γR V' hV' ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).presheaf.map
          (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).preimage_mono
            hle)).op s) := by
    intro V V' hV hV' hle s
    change Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.comm (G i) _ R (εR V hV s)) =
      Algebra.TensorProduct.comm (G i) _ R (εR V' hV' _)
    rw [← hε2 V V' hV hV' hle s]
    exact (Algebra.TensorProduct.comm_comp_map_apply _ _ _).symm

  obtain ⟨S, hSfin, htop⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1
    (by simpa using isCompact_univ)
  haveI : Finite ↥S := hSfin.to_subtype
  have hcov' : ⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ W k = ⊤ := hcov
  haveI : IsAffineHom (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) := MorphismProperty.pullback_fst _ _ inferInstance

  have claim : ∀ Y : ↥S, ∃ jY : J, ∀ js : J, jY ≤ js →
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ ((Y : X.affineOpens) : X.Opens) ≤ ⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ W k := by
    intro Y
    have hY : IsAffineOpen ((Y : X.affineOpens) : X.Opens) := Y.1.2
    let H : Set Γ(X, ((Y : X.affineOpens) : X.Opens)) := {h | ∃ k, X.basicOpen h ≤ W k}
    have hcovB : ∀ x : X, x ∈ ((Y : X.affineOpens) : X.Opens) → (∃ k, x ∈ W k) → ∃ h ∈ H, x ∈ X.basicOpen h := by
      intro x hxY hk
      obtain ⟨k, hxk⟩ := hk
      obtain ⟨h, hle, hxh⟩ := hY.exists_basicOpen_le ⟨x, hxk⟩ hxY
      exact ⟨h, ⟨k, hle⟩, hxh⟩
    have hT : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ ((Y : X.affineOpens) : X.Opens) ≤ ⨆ h : H, (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).basicOpen ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).app _ h.1) := by
      intro x hx
      have hx2 : x ∈ (⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ W k) := by rw [hcov']; trivial
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx2
      obtain ⟨h', hH, hxh⟩ := hcovB _ hx ⟨k, hk⟩
      refine Opens.mem_iSup.2 ⟨⟨h', hH⟩, ?_⟩
      rw [← Scheme.preimage_basicOpen]
      exact hxh
    have hYT : IsAffineOpen ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ ((Y : X.affineOpens) : X.Opens)) := hY.preimage _
    have hspan : Ideal.span (((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).app ((Y : X.affineOpens) : X.Opens)).hom '' H) = ⊤ := by
      rw [← hYT.self_le_iSup_basicOpen_iff]
      refine hT.trans (iSup_le fun h' => ?_)
      exact le_iSup (fun f : ↥(((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).app ((Y : X.affineOpens) : X.Opens)).hom '' H) => (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).basicOpen f.1)
        ⟨_, h'.1, h'.2, rfl⟩
    have h1 : (1 : Γ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ ((Y : X.affineOpens) : X.Opens))) ∈
        Submodule.span Γ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ ((Y : X.affineOpens) : X.Opens)) (((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).app ((Y : X.affineOpens) : X.Opens)).hom '' H) := by
      change (1 : _) ∈ Ideal.span _
      rw [hspan]; trivial
    obtain ⟨N, cf, gf, hsum⟩ := Submodule.mem_span_set'.1 h1
    have hg := fun m => (gf m).2
    choose hh hhH hhg using hg

    have e1 : ∑ m, γR _ hY (cf m) * ((1 : R) ⊗ₜ[G i] hh m) = 1 := by
      have e := congrArg (γR _ hY) hsum
      rw [map_sum, map_one] at e
      rw [← e]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_eq_mul, map_mul, ← hhg m]
      erw [γR1 _ hY (hh m)]

    have s1 := fun m => (hDLv ((Y : X.affineOpens) : X.Opens)).surj (γR _ hY (cf m))
    choose jc zc hzc using s1
    obtain ⟨j₀, hj₀, -⟩ := exists_ge₂ jc jc
    obtain ⟨zc0, hzc0⟩ : ∃ zc0 : Fin N → G j₀.1 ⊗[G i] Γ(X, ((Y : X.affineOpens) : X.Opens)), ∀ m,
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom (G i) (G j₀.1) R) (AlgHom.id (G i) _) (zc0 m) =
          γR _ hY (cf m) :=
      ⟨fun m => Algebra.TensorProduct.map (f' (jc m) j₀ (hj₀ m)) (AlgHom.id (G i) _) (zc m), fun m => by
        rw [← hzc m]; exact (hDLv _).compatibility (jc m) j₀ (hj₀ m) (zc m)⟩

    have s2 := (hDLv ((Y : X.affineOpens) : X.Opens)).inj j₀ j₀ (∑ m, zc0 m * ((1 : G j₀.1) ⊗ₜ[G i] hh m)) 1 (by
      rw [map_sum, map_one, ← e1]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, map_one_tmul, hzc0])
    obtain ⟨j₁, hj₁, hj₁', hZ⟩ := s2
    refine ⟨j₁, fun js hjs => ?_⟩

    letI instKs : ∀ W' : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).Opens, Algebra (G i) Γ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))), W') := fun W' =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ≫ fX) W'
    obtain ⟨εs, -, hεs1, -, -⟩ :=
      AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen (G i) fX (G js.1)
    let γs : Γ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ ((Y : X.affineOpens) : X.Opens)) ≃ₐ[G i] G js.1 ⊗[G i] Γ(X, ((Y : X.affineOpens) : X.Opens)) :=
      (εs _ hY).trans (Algebra.TensorProduct.comm (G i) _ (G js.1))
    have γs1 : ∀ s : Γ(X, ((Y : X.affineOpens) : X.Opens)), γs ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).app _ s) = (1 : G js.1) ⊗ₜ[G i] s := by
      intro s
      change Algebra.TensorProduct.comm (G i) _ (G js.1) (εs _ hY _) = _
      erw [hεs1 _ hY s]
      exact Algebra.TensorProduct.comm_tmul _ _ _
    have hZs : Algebra.TensorProduct.map (f' j₀ js (hj₁.trans hjs)) (AlgHom.id (G i) _)
        (∑ m, zc0 m * ((1 : G j₀.1) ⊗ₜ[G i] hh m)) = 1 := by
      have e := congrArg (Algebra.TensorProduct.map (f' j₁ js hjs) (AlgHom.id (G i) Γ(X, ((Y : X.affineOpens) : X.Opens)))) hZ
      rw [(hDSv _).map_map, (hDSv _).map_map, map_one] at e
      exact e
    haveI : IsAffineHom (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) := MorphismProperty.pullback_fst _ _ inferInstance
    have hYs : IsAffineOpen ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ ((Y : X.affineOpens) : X.Opens)) := hY.preimage _
    have hspan' : Ideal.span (((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).app ((Y : X.affineOpens) : X.Opens)).hom '' H) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have e2 : (1 : Γ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ ((Y : X.affineOpens) : X.Opens))) =
          ∑ m, γs.symm (Algebra.TensorProduct.map (f' j₀ js (hj₁.trans hjs)) (AlgHom.id (G i) _) (zc0 m)) *
            (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).app _ (hh m) := by
        apply γs.injective
        rw [map_one, map_sum, ← hZs, map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, γs1, map_one_tmul]
      rw [e2]
      exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨hh m, hhH m, rfl⟩)
    refine ((hYs.self_le_iSup_basicOpen_iff).2 hspan').trans (iSup_le fun f => ?_)
    obtain ⟨f, h', ⟨k, hk⟩, rfl⟩ := f
    calc (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).basicOpen (((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).app _).hom h') = (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ X.basicOpen h' := (Scheme.preimage_basicOpen _ _).symm
      _ ≤ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ W k := (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).preimage_mono hk
      _ ≤ ⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ W k := le_iSup (fun k => (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ W k) k
  choose jY hjY using claim
  obtain ⟨js, hjs, -⟩ := exists_ge₂ jY jY
  refine ⟨js.1, js.2, ?_⟩
  refine top_le_iff.mp fun x _ => ?_
  have hx : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) x ∈ (⨆ Y ∈ S, (Y : X.Opens)) := by rw [← htop]; trivial
  obtain ⟨Y, hY⟩ := Opens.mem_iSup.1 hx
  obtain ⟨hYS, hxY⟩ := Opens.mem_iSup.1 hY
  exact hjY ⟨Y, hYS⟩ js (hjs _) hxY

end

end S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit (solution)
