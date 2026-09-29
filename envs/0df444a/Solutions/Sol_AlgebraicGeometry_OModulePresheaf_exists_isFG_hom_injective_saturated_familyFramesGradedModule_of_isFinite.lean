-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4ebec8a8-d890-5553-8870-d803e6ca33e0

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

local infixr:73 " ⨳ " => HSMul.hSMul

namespace P2mFamFG

open AlgebraicGeometry.ProjSpace AlgebraicGeometry.OModulePresheaf HomogeneousLocalization ProjSpaceCech

section Constants

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))

local notation "𝒜r" => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A

theorem algebraMap_eq_app_awayToSection (l : Fin (r + 1)) (a : A) :
    (Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ ProjSpace.π A r) (pullbackChart ι l)).algebraMap a
      = (ι.app (Proj.basicOpen 𝒜r (MvPolynomial.X l))).hom
          ((Proj.awayToSection 𝒜r (MvPolynomial.X l)).hom (algebraMap A (Away 𝒜r (MvPolynomial.X l)) a)) := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]

  have hIι : (Proj.basicOpen 𝒜r (MvPolynomial.X l)).ι ≫ ProjSpace.π A r
      = Proj.basicOpenToSpec 𝒜r (MvPolynomial.X l)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Away 𝒜r (MvPolynomial.X l)))) := by
    rw [← awayι_comp_π A r l, ← Proj.basicOpenIsoSpec_inv_ι 𝒜r _ (X_mem_one A r l) one_pos,
      ← Category.assoc (Proj.basicOpenToSpec 𝒜r _), ← Proj.basicOpenIsoSpec_hom 𝒜r _ (X_mem_one A r l) one_pos,
      Iso.hom_inv_id_assoc]
  have hres := (Scheme.ΓSpecIso (.of A)).inv ≫= congrArg Scheme.Hom.appTop hIι
    =≫ (Proj.basicOpen 𝒜r (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A)).topIso.hom
  simp only [Scheme.Hom.comp_appTop, Category.assoc] at hres
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc,
    show (Proj.basicOpenToSpec 𝒜r (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A)).appTop
      = (Proj.basicOpenToSpec 𝒜r _).app ⊤ from rfl,
    Proj.basicOpenToSpec_app_top, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom] at hres
  have hres' := congrArg (fun φ => CommRingCat.Hom.hom φ a) hres
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hres'

  have hιnat := congrArg (fun φ => CommRingCat.Hom.hom φ
      ((ProjSpace.π A r).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)))
    (ι.naturality (homOfLE (le_top : Proj.basicOpen 𝒜r (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A) ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hιnat
  rw [Scheme.Hom.appLE, Scheme.Hom.comp_app]
  change (P.presheaf.map (homOfLE _).op).hom ((ι.app ⊤).hom ((ProjSpace.π A r).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)))
    = _
  have H : ((Proj 𝒜r).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜r (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A) ≤ ⊤)).op).hom
      ((ProjSpace.π A r).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a))
      = (Proj.awayToSection 𝒜r (MvPolynomial.X l)).hom (algebraMap A (Away 𝒜r (MvPolynomial.X l)) a) := by
    refine Eq.trans ?_ hres'
    rw [← CommRingCat.comp_apply]
    exact congrArg (fun φ => CommRingCat.Hom.hom φ _)
      ((congrArg ((Proj 𝒜r).presheaf.map) (Subsingleton.elim _ _)).trans (Functor.map_comp (Proj 𝒜r).presheaf _ _))
  rw [← H, hιnat]
  exact congrArg (fun α => (P.presheaf.map α).hom _) (Subsingleton.elim _ _)

def awayMkHom (l : Fin (r + 1)) (n : ℕ) : (𝒜r (n ⨳ 1)) →+ Away 𝒜r (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A) where
  toFun x := Away.mk 𝒜r (X_mem_one A r l) n x.1 x.2
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, HomogeneousLocalization.val_zero, ZeroMemClass.coe_zero, Localization.mk_zero]
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk, Localization.add_mk_self]
    rfl

theorem app_eq_sum (l : Fin (r + 1))
    (t : Γ(Proj 𝒜r, Proj.basicOpen 𝒜r (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A))) :
    ∃ (S : Finset (Fin (r + 1) →₀ ℕ)) (a : (Fin (r + 1) →₀ ℕ) → A),
      (show Γ(P, pullbackChart ι l) from (ι.app (Proj.basicOpen 𝒜r (MvPolynomial.X l))).hom t)
        = ∑ cf ∈ S, (show Γ(P, pullbackChart ι l) from (ι.app (Proj.basicOpen 𝒜r (MvPolynomial.X l))).hom
              ((Proj.awayToSection 𝒜r (MvPolynomial.X l)).hom (algebraMap A (Away 𝒜r (MvPolynomial.X l)) (a cf))))
            * ∏ i, frameUnit ι l i ^ cf i := by
  obtain ⟨n, num, hnum, hmk⟩ := Away.mk_surjective 𝒜r (X_mem_one A r l)
    ((Proj.basicOpenIsoAway 𝒜r _ (X_mem_one A r l) one_pos).inv t)
  have hzt : (Proj.awayToSection 𝒜r (MvPolynomial.X l)).hom (Away.mk 𝒜r (X_mem_one A r l) n num hnum) = t := by
    rw [hmk, ← Proj.basicOpenIsoAway_hom 𝒜r _ (X_mem_one A r l) one_pos, ← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  have hnum' : num.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n num).mp (by simpa using hnum)
  have hdeg : ∀ cf ∈ num.support, (cf : Fin (r + 1) →₀ ℕ).degree = n := fun cf hcf => by
    rw [Finsupp.degree_eq_weight_one]; exact hnum' (MvPolynomial.mem_support_iff.mp hcf)
  have hmon : ∀ cf ∈ num.support, MvPolynomial.monomial cf (num.coeff cf) ∈ 𝒜r (n ⨳ 1) := fun cf hcf =>
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_monomial _
      (by rw [hdeg cf hcf, smul_eq_mul, mul_one]))
  have hsum : (⟨num, hnum⟩ : 𝒜r (n ⨳ 1))
      = ∑ cf ∈ num.support.attach, (⟨MvPolynomial.monomial cf.1 (num.coeff cf.1), hmon cf.1 cf.2⟩ : 𝒜r (n ⨳ 1)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change num = ∑ cf ∈ num.support.attach, MvPolynomial.monomial cf.1 (num.coeff cf.1)
    rw [Finset.sum_attach num.support (fun cf => MvPolynomial.monomial cf (num.coeff cf))]
    exact num.as_sum
  refine ⟨num.support, fun cf => num.coeff cf, ?_⟩
  let ψ : Away 𝒜r (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A) →+* Γ(P, pullbackChart ι l) :=
    (ι.app (Proj.basicOpen 𝒜r (MvPolynomial.X l))).hom.comp (Proj.awayToSection 𝒜r (MvPolynomial.X l)).hom
  have key : (show Γ(P, pullbackChart ι l) from (ι.app (Proj.basicOpen 𝒜r (MvPolynomial.X l))).hom t)
      = ψ (awayMkHom (A := A) l n ⟨num, hnum⟩) := by rw [← hzt]; rfl
  rw [key, hsum, map_sum, map_sum, ← Finset.sum_attach num.support]
  refine Finset.sum_congr rfl fun cf _ => ?_
  change ψ (Away.mk 𝒜r (X_mem_one A r l) n (MvPolynomial.monomial cf.1 (num.coeff cf.1)) (hmon cf.1 cf.2)) = _
  rw [awayMk_monomial A r l n cf.1 (hdeg cf.1 cf.2), map_mul, map_prod]
  simp only [map_pow]
  rfl

variable (A) in

theorem proj_basicOpen_awayToSection_ratio (N : ℕ) (j i : Fin (N + 1)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)).basicOpen
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X j)).hom
          (ProjSpace.ratio A N j i))
      = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
          ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) * MvPolynomial.X i) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A with h𝒜
  set z : Away 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) := ProjSpace.ratio A N j i with hz
  have hkey : ∀ (x : Proj 𝒜) (hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A)),
      IsUnit ((Proj 𝒜).presheaf.germ _ x hxj ((Proj.awayToSection 𝒜 (MvPolynomial.X j)).hom z))
        ↔ (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) A) ∉ x.asHomogeneousIdeal := by
    intro x hxj
    have hxj' : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A)
        ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hxj
    have hgerm := congrArg (fun ψ => CommRingCat.Hom.hom ψ z)
      (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X j) x hxj)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hgerm
    erw [hgerm]
    haveI : IsLocalHom (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom := isLocalHom_of_isIso _
    refine (isUnit_map_iff (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom _).trans ?_
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
    have hval : (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxj') z).val
        = Localization.mk (MvPolynomial.X i)
            ⟨(MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ 1, pow_mem hxj' 1⟩ := by
      simp only [hz, ProjSpace.ratio, HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
        HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
      rfl
    rw [show Submonoid.powers_le.mpr hxj = Submonoid.powers_le.mpr hxj' from rfl, hval,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact Iff.rfl
  ext x
  simp only [SetLike.mem_coe, Proj.basicOpen_mul, Proj.mem_basicOpen, Opens.mem_inf]
  refine ⟨fun hx => ?_, fun ⟨hxj, hxi⟩ => ?_⟩
  · have hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) :=
      Scheme.basicOpen_le _ _ hx
    exact ⟨hxj, (hkey x hxj).mp ((Scheme.mem_basicOpen _ _ x hxj).mp hx)⟩
  · exact (Scheme.mem_basicOpen _ _ x hxj).mpr ((hkey x hxj).mpr hxi)

theorem basicOpen_frameUnit (j i : Fin (r + 1)) : P.basicOpen (frameUnit ι j i) = pullbackOverlap ι j i := by
  have h := Scheme.preimage_basicOpen ι
    ((Proj.awayToSection 𝒜r (MvPolynomial.X j)).hom (ProjSpace.ratio A r j i))
  rw [proj_basicOpen_awayToSection_ratio] at h
  exact h.symm

end Constants

section Algebra

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}

abbrev Mf (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]
    {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
    {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} (hθ : YComm G θ) :
    GradedModule (MvPolynomial (Fin ny) A) r :=
  familyFramesGradedModule ι G θ hθ

variable {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
  {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} {hθ : YComm G θ}

theorem res_smul' (F : OModulePresheaf q) {U U' : P.Opens} (h : U ≤ U') (a : Γ(P, U')) (x : F.obj U') :
    F.res h (a ⨳ x) = restrictFun h a ⨳ F.res h x :=
  F.res_smul h a x

variable (ι) in

def uprod (j : Fin (r + 1)) (a : Fin (r + 1) → ℕ) : Γ(P, pullbackChart ι j) := ∏ l, frameUnit ι j l ^ a l

theorem uprod_add (j : Fin (r + 1)) (a b : Fin (r + 1) → ℕ) : uprod ι j (a + b) = uprod ι j a * uprod ι j b := by
  simp only [uprod, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem uprod_single (j l : Fin (r + 1)) (n : ℕ) : uprod ι j (Pi.single l n) = frameUnit ι j l ^ n := by
  rw [uprod, Finset.prod_eq_single l (fun m _ hm => by rw [Pi.single_eq_of_ne hm, pow_zero]) (fun h => absurd (Finset.mem_univ l) h),
    Pi.single_eq_same]

theorem uprod_cocycle (j l : Fin (r + 1)) (cc : Fin (r + 1) → ℕ) :
    restrictFun (pullbackOverlap_le_left ι j l) (uprod ι j cc)
      = restrictFun (pullbackOverlap_le_left ι j l) (frameUnit ι j l) ^ (∑ m, cc m) *
          restrictFun (pullbackOverlap_le_right ι j l) (uprod ι l cc) := by
  simp only [uprod, map_prod, map_pow]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => by rw [← mul_pow, frameUnit_cocycle]

theorem framesCompat_uprod_smul {F : OModulePresheaf q} {n : ℕ} {g : ∀ j : Fin (r + 1), F.obj (pullbackChart ι j)}
    (hg : FramesCompat ι F n g) (cc : Fin (r + 1) → ℕ) :
    FramesCompat ι F (n + ∑ m, cc m) (fun j => uprod ι j cc ⨳ g j) := by
  intro j l
  rw [res_smul', res_smul', hg j l, smul_smul, smul_smul, uprod_cocycle]
  congr 1
  ring

theorem framesCompat_sub {F : OModulePresheaf q} {n : ℕ} {g g' : ∀ j : Fin (r + 1), F.obj (pullbackChart ι j)}
    (hg : FramesCompat ι F n g) (hg' : FramesCompat ι F n g') : FramesCompat ι F n (fun j => g j - g' j) := fun j l => by
  rw [map_sub, map_sub, smul_sub, hg j l, hg' j l]

theorem framesCompat_app {n k : ℕ} {g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)} (hg : FramesCompat ι (G k) n g)
    (φ : AffHom (G k) (G (k + 1))) : FramesCompat ι (G (k + 1)) n (fun j => φ.app (framesChart ι j) (g j)) := fun j l => by
  show (G (k + 1)).res _ (φ.app (framesChart ι j) (g j)) = _ ⨳ (G (k + 1)).res _ (φ.app (framesChart ι l) (g l))
  rw [← φ.naturality_apply (U := framesOverlap ι j l) (U' := framesChart ι j),
    ← φ.naturality_apply (U := framesOverlap ι j l) (U' := framesChart ι l), hg j l, φ.app_smul]

variable {k : ℕ}

theorem single_add' (e : ℤ) (g g' : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) :
    FamilyFrames.single ι G e k (fun j => g j + g' j) = FamilyFrames.single ι G e k g + FamilyFrames.single ι G e k g' := by
  refine FamilyFrames.ext fun e' k' j => ?_
  rw [FamilyFrames.add_apply]
  by_cases he : e' = e
  · subst he
    by_cases hk : k' = k
    · subst hk; simp only [FamilyFrames.single_apply_self]
    · simp only [FamilyFrames.single_apply_of_ne_level _ _ hk, Pi.zero_apply, add_zero]
  · simp only [FamilyFrames.single_apply_of_ne_degree he, Pi.zero_apply, add_zero]

theorem single_C_smul (e : ℤ) (a : A) (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) :
    (MvPolynomial.C a : MvPolynomial (Fin ny) A) ⨳ (show (Mf ι hθ).M from FamilyFrames.single ι G e k g)
      = FamilyFrames.single ι G e k (fun j => a ⨳ g j) := by
  rw [C_smul]
  refine FamilyFrames.ext fun e' k' j => ?_
  show a ⨳ FamilyFrames.single ι G e k g e' k' j = _
  by_cases he : e' = e
  · subst he
    by_cases hk : k' = k
    · subst hk; simp only [FamilyFrames.single_apply_self]
    · simp only [FamilyFrames.single_apply_of_ne_level _ _ hk, Pi.zero_apply, smul_zero]
  · simp only [FamilyFrames.single_apply_of_ne_degree he, Pi.zero_apply, smul_zero]

theorem sum_apply' {X : Type} (S : Finset X) (Fx : X → FamilyFrames ι G) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    (∑ x ∈ S, Fx x) e k j = ∑ x ∈ S, Fx x e k j := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, FamilyFrames.add_apply, ih]

theorem single_zero' (e : ℤ) : FamilyFrames.single ι G e k (fun _ => 0) = 0 := by
  refine FamilyFrames.ext fun e' k' j => ?_
  rw [FamilyFrames.zero_apply]
  by_cases he : e' = e
  · subst he
    by_cases hk : k' = k
    · subst hk; simp only [FamilyFrames.single_apply_self]
    · simp only [FamilyFrames.single_apply_of_ne_level _ _ hk, Pi.zero_apply]
  · simp only [FamilyFrames.single_apply_of_ne_degree he, Pi.zero_apply]

theorem single_congr {e e' : ℤ} (he : e = e') {g g' : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)} (hg : g = g') :
    FamilyFrames.single ι G e k g = FamilyFrames.single ι G e' k g' := by subst he hg; rfl

private theorem _root_.P2mFamFG.monMul_single (cc : Fin (r + 1) → ℕ) (e : ℤ) (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) :
    GradedModule.monMul (Mf ι hθ) cc (FamilyFrames.single ι G e k g)
      = FamilyFrames.single ι G (e + ∑ l, (cc l : ℤ)) k (fun j => uprod ι j cc ⨳ g j) := by
  refine FamilyFrames.ext fun e' k' j => ?_
  rw [monMul_apply]
  by_cases he : e' - ∑ l, (cc l : ℤ) = e
  · have he' : e' = e + ∑ l, (cc l : ℤ) := by rw [← he]; ring
    rw [he, he']
    by_cases hk : k' = k
    · subst hk; rw [FamilyFrames.single_apply_self, FamilyFrames.single_apply_self]; rfl
    · rw [FamilyFrames.single_apply_of_ne_level _ _ hk, FamilyFrames.single_apply_of_ne_level _ _ hk, Pi.zero_apply,
        smul_zero]
  · have he' : e' ≠ e + ∑ l, (cc l : ℤ) := fun h => he (by rw [h]; ring)
    rw [FamilyFrames.single_apply_of_ne_degree he, FamilyFrames.single_apply_of_ne_degree he', Pi.zero_apply,
      Pi.zero_apply, smul_zero]

p2m_export "P2mFamFG" "monMul_single"

theorem xMul_pow_single (l : Fin (r + 1)) (n : ℕ) (e : ℤ) (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) :
    ((Mf ι hθ).xMul l ^ n) (FamilyFrames.single ι G e k g)
      = FamilyFrames.single ι G (e + n) k (fun j => frameUnit ι j l ^ n ⨳ g j) := by
  rw [← GradedModule.monMul_single, monMul_single]
  refine single_congr ?_ (funext fun j => by rw [uprod_single])
  congr 1
  rw [Finset.sum_eq_single l (fun m _ hm => by rw [Pi.single_eq_of_ne hm, Nat.cast_zero])
    (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same]

theorem yEnd_single (m : Fin ny) (e : ℤ) (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) :
    yEnd ι G θ m (FamilyFrames.single ι G e k g)
      = FamilyFrames.single ι G e (k + 1) (fun j => (θ m k).app (framesChart ι j) (g j)) := by
  refine FamilyFrames.ext fun e' k' j => ?_
  cases k' with
  | zero =>
    rw [yEnd_apply_zero, FamilyFrames.single_apply_of_ne_level _ _ (Nat.succ_ne_zero k).symm]; rfl
  | succ k' =>
    rw [yEnd_apply_succ]
    by_cases he : e' = e
    · subst he
      by_cases hk : k' = k
      · subst hk; rw [FamilyFrames.single_apply_self, FamilyFrames.single_apply_self]
      · rw [FamilyFrames.single_apply_of_ne_level _ _ hk, FamilyFrames.single_apply_of_ne_level _ _ (by omega),
          Pi.zero_apply, Pi.zero_apply, map_zero]
    · rw [FamilyFrames.single_apply_of_ne_degree he, FamilyFrames.single_apply_of_ne_degree he, Pi.zero_apply,
        Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, map_zero]

theorem single_mem_grade_iff (n : ℕ) (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) :
    FamilyFrames.single ι G (n : ℤ) k g ∈ (Mf ι hθ).grade (n : ℤ) ↔ FramesCompat ι (G k) n g := by
  change IsHomogeneousElem ι G (n : ℤ) (FamilyFrames.single ι G (n : ℤ) k g) ↔ _
  rw [isHomogeneousElem_single_iff]
  refine ⟨fun h => ?_, fun h => ⟨fun h' => absurd h' (by omega), fun _ => ?_⟩⟩
  · have h2 := h.2 (Int.natCast_nonneg n)
    rwa [Int.toNat_natCast] at h2
  · rwa [Int.toNat_natCast]

open scoped IsMulCommutative in
variable (ι hθ) in

private def _root_.P2mFamFG.xAlg : MvPolynomial (Fin (r + 1)) (MvPolynomial (Fin ny) A) →ₐ[MvPolynomial (Fin ny) A]
    Module.End (MvPolynomial (Fin ny) A) (Mf ι hθ).M :=
  haveI := Algebra.isMulCommutative_adjoin (MvPolynomial (Fin ny) A) (s := Set.range (Mf ι hθ).xMul)
    (by
      rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩
      exact (Mf ι hθ).xMul_comm l l')
  (Algebra.adjoin (MvPolynomial (Fin ny) A) (Set.range (Mf ι hθ).xMul)).val.comp
    (MvPolynomial.aeval fun l =>
      (⟨(Mf ι hθ).xMul l, Algebra.subset_adjoin ⟨l, rfl⟩⟩ : Algebra.adjoin (MvPolynomial (Fin ny) A) (Set.range (Mf ι hθ).xMul)))

p2m_export "P2mFamFG" "xAlg"
theorem xAlg_X (l : Fin (r + 1)) : xAlg ι hθ (MvPolynomial.X l) = (Mf ι hθ).xMul l := by
  simp only [xAlg, AlgHom.comp_apply, MvPolynomial.aeval_X, Subalgebra.coe_val]

theorem xAlg_C (ρ : MvPolynomial (Fin ny) A) (f : (Mf ι hθ).M) : xAlg ι hθ (MvPolynomial.C ρ) f = ρ ⨳ f := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]

theorem xMul_pow_eq_xAlg (l : Fin (r + 1)) (n : ℕ) : (Mf ι hθ).xMul l ^ n = xAlg ι hθ (MvPolynomial.X l ^ n) := by
  rw [map_pow, xAlg_X]

theorem xAlg_prod (cc : Fin (r + 1) → ℕ) :
    xAlg ι hθ (∏ l, MvPolynomial.X l ^ cc l) = GradedModule.monMul (Mf ι hθ) cc := by
  rw [← Finset.noncommProd_eq_prod, Finset.map_noncommProd]
  unfold GradedModule.monMul
  exact Finset.noncommProd_congr rfl (fun l _ => by rw [map_pow, xAlg_X]) _

theorem xAlg_monomial (cc : Fin (r + 1) →₀ ℕ) (ρ : MvPolynomial (Fin ny) A) (f : (Mf ι hθ).M) :
    xAlg ι hθ (MvPolynomial.monomial cc ρ) f = ρ ⨳ GradedModule.monMul (Mf ι hθ) cc f := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_mul, Module.End.mul_apply, xAlg_prod,
    xAlg_C]

theorem xAlg_comm_xMul_pow (p : MvPolynomial (Fin (r + 1)) (MvPolynomial (Fin ny) A)) (l : Fin (r + 1)) (n : ℕ)
    (f : (Mf ι hθ).M) : xAlg ι hθ p (((Mf ι hθ).xMul l ^ n) f) = ((Mf ι hθ).xMul l ^ n) (xAlg ι hθ p f) := by
  rw [xMul_pow_eq_xAlg, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

theorem sum_eq_degree (cc : Fin (r + 1) →₀ ℕ) : (∑ l, cc l) = cc.degree := by
  rw [Finsupp.degree]
  exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => Finsupp.notMem_support_iff.mp hj) |>.symm

theorem xAlg_mem_grade {p : MvPolynomial (Fin (r + 1)) (MvPolynomial (Fin ny) A)} {n' e : ℤ}
    (hp : p ∈ GradedModule.freeGrade (MvPolynomial (Fin ny) A) r n') {f : (Mf ι hθ).M} (hf : f ∈ (Mf ι hθ).grade e) :
    xAlg ι hθ p f ∈ (Mf ι hθ).grade (e + n') := by
  by_cases hn : 0 ≤ n'
  · rw [GradedModule.freeGrade_of_nonneg _ _ hn, MvPolynomial.mem_homogeneousSubmodule] at hp
    rw [p.as_sum, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun cf hcf => ?_
    rw [xAlg_monomial]
    refine Submodule.smul_mem _ _ ?_
    have hdeg : (∑ l, (cf l : ℤ)) = n' := by
      have h1 : cf.degree = n'.toNat := by rw [Finsupp.degree_eq_weight_one]; exact hp (MvPolynomial.mem_support_iff.mp hcf)
      rw [← Int.toNat_of_nonneg hn, ← h1, ← sum_eq_degree]; push_cast; rfl
    rw [← hdeg]
    exact GradedModule.monMul_mem_grade _ cf e f hf
  · have hp0 : p = 0 := by simpa [GradedModule.freeGrade, hn] using hp
    rw [hp0, map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _

theorem freeGrade_mul_mem {p p' : MvPolynomial (Fin (r + 1)) (MvPolynomial (Fin ny) A)} {n₁ n₂ : ℤ}
    (hp : p ∈ GradedModule.freeGrade (MvPolynomial (Fin ny) A) r n₁)
    (hp' : p' ∈ GradedModule.freeGrade (MvPolynomial (Fin ny) A) r n₂) :
    p * p' ∈ GradedModule.freeGrade (MvPolynomial (Fin ny) A) r (n₁ + n₂) := by
  by_cases h₁ : 0 ≤ n₁
  · by_cases h₂ : 0 ≤ n₂
    · rw [GradedModule.freeGrade_of_nonneg _ _ h₁, MvPolynomial.mem_homogeneousSubmodule] at hp
      rw [GradedModule.freeGrade_of_nonneg _ _ h₂, MvPolynomial.mem_homogeneousSubmodule] at hp'
      rw [GradedModule.freeGrade_of_nonneg _ _ (by omega), MvPolynomial.mem_homogeneousSubmodule, Int.toNat_add h₁ h₂]
      exact hp.mul hp'
    · have : p' = 0 := by simpa [GradedModule.freeGrade, h₂] using hp'
      rw [this, mul_zero]; exact Submodule.zero_mem _
  · have : p = 0 := by simpa [GradedModule.freeGrade, h₁] using hp
    rw [this, zero_mul]; exact Submodule.zero_mem _

end Algebra

section Presentation

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
  {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} {hθ : YComm G θ}

local notation "Rx" => MvPolynomial (Fin (r + 1)) (MvPolynomial (Fin ny) A)

variable (ι G) in

structure Gens where

  d₁ : ℕ

  m : ℕ

  sg : Fin m → ∀ j : Fin (r + 1), (G 0).obj (pullbackChart ι j)
  compat : ∀ a, FramesCompat ι (G 0) d₁ (sg a)
  gen : ∀ (l : Fin (r + 1)) (z : (G 0).obj (pullbackChart ι l)),
    z ∈ AddSubmonoid.closure (Set.range fun p :
        Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A),
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)
              (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A)) × Fin m =>
      (show Γ(P, pullbackChart ι l) from
          (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A) (MvPolynomial.X l))).hom p.1)
        ⨳ sg p.2 l)

variable (𝔤 : Gens ι G)

abbrev F : GradedModule (MvPolynomial (Fin ny) A) r :=
  GradedModule.pi (fun _ : Fin 𝔤.m => GradedModule.FD (MvPolynomial (Fin ny) A) r (-(𝔤.d₁ : ℤ)))

theorem mem_F_grade_iff (e : ℤ) (p : (F (ny := ny) 𝔤).M) :
    p ∈ (F (ny := ny) 𝔤).grade e ↔ ∀ a, p a ∈ GradedModule.freeGrade (MvPolynomial (Fin ny) A) r (e + -(𝔤.d₁ : ℤ)) := by
  change (∀ a ∈ (Set.univ : Set (Fin 𝔤.m)), p a ∈ GradedModule.freeGrade (MvPolynomial (Fin ny) A) r (e + -(𝔤.d₁ : ℤ))) ↔ _
  exact ⟨fun h a => h a (Set.mem_univ a), fun h a _ => h a⟩

theorem F_xMul_apply (l : Fin (r + 1)) (p : (F (ny := ny) 𝔤).M) (a : Fin 𝔤.m) :
    (F (ny := ny) 𝔤).xMul l p a = (MvPolynomial.X l : Rx) * (show Rx from p a) := rfl

variable (hθ) in

private def _root_.P2mFamFG.gen (a : Fin 𝔤.m) : (Mf ι hθ).M := FamilyFrames.single ι G (𝔤.d₁ : ℤ) 0 (𝔤.sg a)

p2m_export "P2mFamFG" "gen"
theorem gen_mem (a : Fin 𝔤.m) : gen hθ 𝔤 a ∈ (Mf ι hθ).grade (𝔤.d₁ : ℤ) :=
  (single_mem_grade_iff _ _).mpr (𝔤.compat a)

variable (hθ) in

def Φlin : (F (ny := ny) 𝔤).M →ₗ[MvPolynomial (Fin ny) A] (Mf ι hθ).M :=
  ∑ a : Fin 𝔤.m, (LinearMap.applyₗ (gen hθ 𝔤 a)).comp ((xAlg ι hθ).toLinearMap.comp (LinearMap.proj a))

theorem Φlin_apply (p : (F (ny := ny) 𝔤).M) : Φlin hθ 𝔤 p = ∑ a, xAlg ι hθ (p a) (gen hθ 𝔤 a) := by
  simp only [Φlin, LinearMap.sum_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.applyₗ_apply_apply]
  rfl

theorem Φlin_mem_grade {e : ℤ} {p : (F (ny := ny) 𝔤).M} (hp : p ∈ (F (ny := ny) 𝔤).grade e) : Φlin hθ 𝔤 p ∈ (Mf ι hθ).grade e := by
  rw [Φlin_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  have h := xAlg_mem_grade ((mem_F_grade_iff 𝔤 e p).mp hp a) (gen_mem 𝔤 a) (hθ := hθ)
  rwa [show (𝔤.d₁ : ℤ) + (e + -(𝔤.d₁ : ℤ)) = e by ring] at h

theorem Φlin_xMul (l : Fin (r + 1)) (p : (F (ny := ny) 𝔤).M) :
    Φlin hθ 𝔤 ((F (ny := ny) 𝔤).xMul l p) = (Mf ι hθ).xMul l (Φlin hθ 𝔤 p) := by
  rw [Φlin_apply, Φlin_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [F_xMul_apply, map_mul, xAlg_X, Module.End.mul_apply]

variable (hθ) in

def ΦHom : GradedModule.Hom (F (ny := ny) 𝔤) (Mf ι hθ) where
  toLinearMap := Φlin hθ 𝔤
  mem_grade _ _ hp := Φlin_mem_grade 𝔤 hp
  xMul_comm l := LinearMap.ext fun p => Φlin_xMul 𝔤 l p

theorem Φlin_xMul_pow (l : Fin (r + 1)) (n : ℕ) (p : (F (ny := ny) 𝔤).M) :
    Φlin hθ 𝔤 (((F (ny := ny) 𝔤).xMul l ^ n) p) = ((Mf ι hθ).xMul l ^ n) (Φlin hθ 𝔤 p) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, Φlin_xMul, ih]

theorem Φlin_xAlg (P' : Rx) (p : (F (ny := ny) 𝔤).M) :
    Φlin hθ 𝔤 (fun a => P' * (show Rx from p a)) = xAlg ι hθ P' (Φlin hθ 𝔤 p) := by
  rw [Φlin_apply, Φlin_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, Module.End.mul_apply]

variable (hθ) in

abbrev K : Submodule (MvPolynomial (Fin ny) A) (F (ny := ny) 𝔤).M := LinearMap.ker (Φlin hθ 𝔤)

theorem K_stable (l : Fin (r + 1)) : ∀ p ∈ K hθ 𝔤, (F (ny := ny) 𝔤).xMul l p ∈ K hθ 𝔤 := fun p hp => by
  rw [LinearMap.mem_ker, Φlin_xMul, LinearMap.mem_ker.mp hp, map_zero]

variable (hθ) in

def D : GradedModule (MvPolynomial (Fin ny) A) r := (F (ny := ny) 𝔤).quot (K hθ 𝔤) (K_stable 𝔤)

variable (hθ) in

def pres : GradedModule.Presentation (D hθ 𝔤) where
  J := Fin 𝔤.m
  d₀ _ := -(𝔤.d₁ : ℤ)
  hom :=
    { toLinearMap := (K hθ 𝔤).mkQ
      mem_grade := fun _ p hp => ⟨p, hp, rfl⟩
      xMul_comm := fun l => LinearMap.ext fun p => rfl }
  surj _ _ hz := by
    obtain ⟨p, hp, rfl⟩ := hz
    exact ⟨p, hp, rfl⟩

variable (hθ) in

def hHom : GradedModule.Hom (D hθ 𝔤) (Mf ι hθ) where
  toLinearMap := (K hθ 𝔤).liftQ (Φlin hθ 𝔤) le_rfl
  mem_grade _ _ hz := by
    obtain ⟨p, hp, rfl⟩ := hz
    exact Φlin_mem_grade 𝔤 hp
  xMul_comm l := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun p => ?_)
    show (K hθ 𝔤).liftQ (Φlin hθ 𝔤) le_rfl ((K hθ 𝔤).mapQ (K hθ 𝔤) ((F (ny := ny) 𝔤).xMul l) (K_stable 𝔤 l) ((K hθ 𝔤).mkQ p))
      = (Mf ι hθ).xMul l ((K hθ 𝔤).liftQ (Φlin hθ 𝔤) le_rfl ((K hθ 𝔤).mkQ p))
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.liftQ_apply, Submodule.liftQ_apply, Φlin_xMul]

theorem hHom_injective : Function.Injective (hHom hθ 𝔤).toLinearMap :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

theorem hHom_mkQ (p : (F (ny := ny) 𝔤).M) : (hHom hθ 𝔤).toLinearMap ((K hθ 𝔤).mkQ p) = Φlin hθ 𝔤 p := rfl

variable (hθ) in

def Sat (l : Fin (r + 1)) (e : ℤ) (f : (Mf ι hθ).M) : Prop :=
  ∃ (N : ℕ) (p : (F (ny := ny) 𝔤).M), p ∈ (F (ny := ny) 𝔤).grade (e + N) ∧ Φlin hθ 𝔤 p = ((Mf ι hθ).xMul l ^ N) f

variable {𝔤} {l : Fin (r + 1)}

theorem sat_iff_le {e : ℤ} {f : (Mf ι hθ).M} :
    Sat hθ 𝔤 l e f ↔ ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      ∃ p : (F (ny := ny) 𝔤).M, p ∈ (F (ny := ny) 𝔤).grade (e + N') ∧ Φlin hθ 𝔤 p = ((Mf ι hθ).xMul l ^ N') f := by
  refine ⟨fun ⟨N, p, hp, hΦ⟩ => ⟨N, fun N' hN' => ⟨((F (ny := ny) 𝔤).xMul l ^ (N' - N)) p, ?_, ?_⟩⟩,
    fun ⟨N, h⟩ => ⟨N, h N le_rfl⟩⟩
  · have h := GradedModule.xMul_pow_mem_grade (F (ny := ny) 𝔤) l (N' - N) _ p hp
    rwa [show e + (N : ℤ) + ((N' - N : ℕ) : ℤ) = e + N' by push_cast [hN']; ring] at h
  · rw [Φlin_xMul_pow, hΦ, ← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hN']

theorem sat_zero (e : ℤ) : Sat hθ 𝔤 l e 0 :=
  ⟨0, 0, Submodule.zero_mem _, by rw [map_zero, map_zero]⟩

theorem Sat.add {e : ℤ} {f f' : (Mf ι hθ).M} (hf : Sat hθ 𝔤 l e f) (hf' : Sat hθ 𝔤 l e f') : Sat hθ 𝔤 l e (f + f') := by
  obtain ⟨N, hN⟩ := sat_iff_le.mp hf
  obtain ⟨N', hN'⟩ := sat_iff_le.mp hf'
  obtain ⟨p, hp, hΦ⟩ := hN (N + N') (Nat.le_add_right N N')
  obtain ⟨p', hp', hΦ'⟩ := hN' (N + N') (Nat.le_add_left N' N)
  exact ⟨N + N', p + p', Submodule.add_mem _ hp hp', by rw [map_add, hΦ, hΦ', map_add]⟩

theorem Sat.smul {e : ℤ} {f : (Mf ι hθ).M} (hf : Sat hθ 𝔤 l e f) (ρ : MvPolynomial (Fin ny) A) : Sat hθ 𝔤 l e (ρ ⨳ f) := by
  obtain ⟨N, p, hp, hΦ⟩ := hf
  exact ⟨N, ρ ⨳ p, Submodule.smul_mem _ ρ hp, by rw [map_smul, hΦ, map_smul]⟩

theorem Sat.sum {e : ℤ} {ι' : Type} (S : Finset ι') {f : ι' → (Mf ι hθ).M} (hf : ∀ i ∈ S, Sat hθ 𝔤 l e (f i)) :
    Sat hθ 𝔤 l e (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact sat_zero e
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i S)).add (ih fun i' hi' => hf i' (Finset.mem_insert_of_mem hi'))

theorem Sat.xAlg {e n' : ℤ} {f : (Mf ι hθ).M} (hf : Sat hθ 𝔤 l e f) {P' : MvPolynomial (Fin (r + 1)) (MvPolynomial (Fin ny) A)}
    (hP' : P' ∈ GradedModule.freeGrade (MvPolynomial (Fin ny) A) r n') : Sat hθ 𝔤 l (e + n') (xAlg ι hθ P' f) := by
  obtain ⟨N, p, hp, hΦ⟩ := hf
  refine ⟨N, fun a => P' * (show Rx from p a), ?_, ?_⟩
  · rw [mem_F_grade_iff] at hp ⊢
    intro a
    have h := freeGrade_mul_mem hP' (hp a)
    rwa [show n' + (e + (N : ℤ) + -(𝔤.d₁ : ℤ)) = e + n' + N + -(𝔤.d₁ : ℤ) by ring] at h
  · rw [Φlin_xAlg, hΦ, xAlg_comm_xMul_pow]

theorem Sat.monMul {e : ℤ} {f : (Mf ι hθ).M} (hf : Sat hθ 𝔤 l e f) (cc : Fin (r + 1) → ℕ) :
    Sat hθ 𝔤 l (e + ∑ m, (cc m : ℤ)) (GradedModule.monMul (Mf ι hθ) cc f) := by
  rw [← xAlg_prod]
  exact hf.xAlg (GradedModule.prod_X_pow_mem_freeGrade cc)

theorem Sat.xMul_pow {e : ℤ} {f : (Mf ι hθ).M} (hf : Sat hθ 𝔤 l e f) (i : Fin (r + 1)) (n : ℕ) :
    Sat hθ 𝔤 l (e + n) (((Mf ι hθ).xMul i ^ n) f) := by
  have h := hf.monMul (Pi.single i n)
  rw [GradedModule.monMul_single, Finset.sum_eq_single i (fun m _ hm => by rw [Pi.single_eq_of_ne hm, Nat.cast_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same] at h
  exact h

theorem Sat.yEnd {e : ℤ} {f : (Mf ι hθ).M} (hf : Sat hθ 𝔤 l e f) (m : Fin ny) : Sat hθ 𝔤 l e (yEnd ι G θ m f) := by
  have h := hf.smul (MvPolynomial.X m)
  rwa [X_smul] at h

theorem Sat.of_xMul_pow {e : ℤ} {f : (Mf ι hθ).M} (n : ℕ) (hf : Sat hθ 𝔤 l (e + n) (((Mf ι hθ).xMul l ^ n) f)) : Sat hθ 𝔤 l e f := by
  obtain ⟨N, p, hp, hΦ⟩ := hf
  refine ⟨N + n, p, ?_, ?_⟩
  · rwa [show e + (n : ℤ) + N = e + ((N + n : ℕ) : ℤ) by push_cast; ring] at hp
  · rw [hΦ, ← Module.End.mul_apply, ← pow_add]

theorem sat_single_of_apply_eq_zero {k : ℕ} (hq : (G k).IsQuasicoherent) {n : ℕ}
    {g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)} (hg : FramesCompat ι (G k) n g) (h0 : g l = 0) :
    Sat hθ 𝔤 l (n : ℤ) (FamilyFrames.single ι G (n : ℤ) k g) := by

  have hj : ∀ j, ∃ e : ℕ, frameUnit ι j l ^ e ⨳ g j = 0 := fun j => by
    have e := basicOpen_frameUnit ι j l
    refine ((hq ⟨pullbackChart ι j, isAffineOpen_pullbackChart ι j⟩ (frameUnit ι j l)).2 (g j) ?_)
    have h1 : (G k).res (P.basicOpen_le _) (g j) = (G k).res e.le ((G k).res (pullbackOverlap_le_left ι j l) (g j)) := by
      rw [(G k).res_res]
    rw [h1, hg j l, h0, map_zero, smul_zero, map_zero]
  choose e0 he0 using hj
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j, e0 j ≤ N := ⟨Finset.univ.sup e0, fun j => Finset.le_sup (f := e0) (Finset.mem_univ j)⟩
  refine ⟨N, 0, Submodule.zero_mem _, ?_⟩
  have hz : (fun j => frameUnit ι j l ^ N ⨳ g j) = fun _ => 0 := funext fun j => by
    rw [← Nat.sub_add_cancel (hN j), pow_add, mul_smul, he0 j, smul_zero]
  rw [map_zero, xMul_pow_single, hz, single_zero']
  rfl

theorem sat_single_congr {k : ℕ} (hq : (G k).IsQuasicoherent) {n : ℕ}
    {g g' : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)} (hg : FramesCompat ι (G k) n g) (hg' : FramesCompat ι (G k) n g')
    (hl : g l = g' l) (h : Sat hθ 𝔤 l (n : ℤ) (FamilyFrames.single ι G (n : ℤ) k g')) :
    Sat hθ 𝔤 l (n : ℤ) (FamilyFrames.single ι G (n : ℤ) k g) := by
  have e1 : FamilyFrames.single ι G (n : ℤ) k g
      = FamilyFrames.single ι G (n : ℤ) k g' + FamilyFrames.single ι G (n : ℤ) k (fun j => g j - g' j) := by
    rw [← single_add']; exact single_congr rfl (funext fun j => by abel)
  rw [e1]
  exact h.add (sat_single_of_apply_eq_zero hq (framesCompat_sub hg hg') (by show g l - g' l = 0; rw [hl, sub_self]))

end Presentation

section Generation

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
  {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} {hθ : YComm G θ} {𝔤 : Gens ι G} {l : Fin (r + 1)}

local notation "Rx" => MvPolynomial (Fin (r + 1)) (MvPolynomial (Fin ny) A)

variable (hθ 𝔤 l) in

def GoodAt (k : ℕ) (z : (G k).obj (pullbackChart ι l)) : Prop :=
  ∃ (n : ℕ) (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)),
    FramesCompat ι (G k) n g ∧ Sat hθ 𝔤 l (n : ℤ) (FamilyFrames.single ι G (n : ℤ) k g) ∧ g l = z

variable {k : ℕ}

theorem goodAt_zero : GoodAt hθ 𝔤 l k 0 :=
  ⟨0, fun _ => 0, FramesCompat.zero _ _, by rw [single_zero']; exact sat_zero _, rfl⟩

theorem framesCompat_pow_smul {F : OModulePresheaf q} {n : ℕ} {g : ∀ j : Fin (r + 1), F.obj (pullbackChart ι j)}
    (hg : FramesCompat ι F n g) (e : ℕ) : FramesCompat ι F (n + e) (fun j => frameUnit ι j l ^ e ⨳ g j) := by
  have h := framesCompat_uprod_smul hg (Pi.single l e)
  rw [Finset.sum_eq_single l (fun m _ hm => by rw [Pi.single_eq_of_ne hm]) (fun h => absurd (Finset.mem_univ l) h),
    Pi.single_eq_same] at h
  simpa only [uprod_single] using h

theorem GoodAt.bump {z : (G k).obj (pullbackChart ι l)} {n : ℕ} {g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)}
    (hg : FramesCompat ι (G k) n g) (hs : Sat hθ 𝔤 l (n : ℤ) (FamilyFrames.single ι G (n : ℤ) k g)) (hz : g l = z) (e : ℕ) :
    FramesCompat ι (G k) (n + e) (fun j => frameUnit ι j l ^ e ⨳ g j) ∧
      Sat hθ 𝔤 l ((n + e : ℕ) : ℤ) (FamilyFrames.single ι G ((n + e : ℕ) : ℤ) k (fun j => frameUnit ι j l ^ e ⨳ g j)) ∧
      frameUnit ι l l ^ e ⨳ g l = z := by
  refine ⟨framesCompat_pow_smul hg e, ?_, by rw [frameUnit_self, one_pow, one_smul, hz]⟩
  have h := hs.xMul_pow l e
  rwa [xMul_pow_single, ← Nat.cast_add] at h

theorem GoodAt.add {z z' : (G k).obj (pullbackChart ι l)} (h : GoodAt hθ 𝔤 l k z) (h' : GoodAt hθ 𝔤 l k z') :
    GoodAt hθ 𝔤 l k (z + z') := by
  obtain ⟨n, g, hg, hs, hz⟩ := h
  obtain ⟨n', g', hg', hs', hz'⟩ := h'
  obtain ⟨hg1, hs1, hz1⟩ := GoodAt.bump hg hs hz n'
  obtain ⟨hg2, hs2, hz2⟩ := GoodAt.bump hg' hs' hz' n
  rw [add_comm n' n] at hg2 hs2
  refine ⟨n + n', fun j => frameUnit ι j l ^ n' ⨳ g j + frameUnit ι j l ^ n ⨳ g' j, hg1.add hg2, ?_, by
    show frameUnit ι l l ^ n' ⨳ g l + frameUnit ι l l ^ n ⨳ g' l = z + z'; rw [hz1, hz2]⟩
  rw [single_add']
  exact hs1.add hs2

theorem GoodAt.sum {ι' : Type} (S : Finset ι') {z : ι' → (G k).obj (pullbackChart ι l)} (h : ∀ i ∈ S, GoodAt hθ 𝔤 l k (z i)) :
    GoodAt hθ 𝔤 l k (∑ i ∈ S, z i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact goodAt_zero
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i S)).add (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))

theorem GoodAt.smul_const_uprod {z : (G k).obj (pullbackChart ι l)} (h : GoodAt hθ 𝔤 l k z) (a : A) (cc : Fin (r + 1) → ℕ) :
    GoodAt hθ 𝔤 l k
      (((Scheme.TwoAffineOpenCover.algebraOfHom q (pullbackChart ι l)).algebraMap a * uprod ι l cc) ⨳ z) := by
  obtain ⟨n, g, hg, hs, hz⟩ := h
  refine ⟨n + ∑ m, cc m, fun j => a ⨳ (uprod ι j cc ⨳ g j), (framesCompat_uprod_smul hg cc).smul a, ?_, ?_⟩
  · have h1 := (hs.monMul cc).smul (MvPolynomial.C a)
    rw [monMul_single, single_C_smul, ← Nat.cast_sum, ← Nat.cast_add] at h1
    exact h1
  · letI := Scheme.TwoAffineOpenCover.algebraOfHom q (pullbackChart ι l)
    haveI : IsScalarTower A Γ(P, pullbackChart ι l) ((G k).obj (pullbackChart ι l)) := (G k).isScalarTower _
    show a ⨳ (uprod ι l cc ⨳ g l) = _
    rw [hz, ← smul_assoc, Algebra.smul_def]

theorem GoodAt.smul_app (hιq : ι ≫ ProjSpace.π A r = q) {z : (G k).obj (pullbackChart ι l)}
    (h : GoodAt hθ 𝔤 l k z)
    (c : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)
          (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A))) :
    GoodAt hθ 𝔤 l k ((show Γ(P, pullbackChart ι l) from
      (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A) (MvPolynomial.X l))).hom c) ⨳ z) := by
  subst hιq
  obtain ⟨S, a, hc⟩ := app_eq_sum ι l c
  rw [hc, Finset.sum_smul]
  refine GoodAt.sum S fun cf _ => ?_
  rw [← algebraMap_eq_app_awayToSection ι l (a cf)]
  exact h.smul_const_uprod (a cf) cf

theorem GoodAt.app {w : (G k).obj (pullbackChart ι l)} (h : GoodAt hθ 𝔤 l k w) (m : Fin ny) :
    GoodAt hθ 𝔤 l (k + 1) ((θ m k).app (framesChart ι l) w) := by
  obtain ⟨n, g, hg, hs, hz⟩ := h
  refine ⟨n, fun j => (θ m k).app (framesChart ι j) (g j), framesCompat_app hg (θ m k), ?_, by
    show (θ m k).app (framesChart ι l) (g l) = _; rw [hz]⟩
  have h1 := hs.yEnd m
  rwa [yEnd_single] at h1

theorem goodAt_gen (a : Fin 𝔤.m) : GoodAt hθ 𝔤 l 0 (𝔤.sg a l) := by
  refine ⟨𝔤.d₁, 𝔤.sg a, 𝔤.compat a, ⟨0, Pi.single (M := fun _ : Fin 𝔤.m => Rx) a 1, ?_, ?_⟩, rfl⟩
  · rw [mem_F_grade_iff]
    intro a'
    rw [show (𝔤.d₁ : ℤ) + ((0 : ℕ) : ℤ) + -(𝔤.d₁ : ℤ) = 0 by push_cast; ring,
      GradedModule.freeGrade_of_nonneg _ _ le_rfl, Int.toNat_zero]
    by_cases ha : a' = a
    · subst ha
      rw [Pi.single_eq_same]
      exact (MvPolynomial.mem_homogeneousSubmodule 0 (1 : Rx)).mpr (MvPolynomial.isHomogeneous_one _ _)
    · rw [Pi.single_eq_of_ne ha]
      exact Submodule.zero_mem _
  · rw [pow_zero, Module.End.one_apply, Φlin_apply, Finset.sum_eq_single a (fun a' _ ha' => by
      rw [Pi.single_eq_of_ne ha', map_zero, LinearMap.zero_apply]) (fun h => absurd (Finset.mem_univ a) h),
      Pi.single_eq_same, map_one, Module.End.one_apply]
    rfl

theorem goodAt_all (hιq : ι ≫ ProjSpace.π A r = q)
    (hgen : ∀ (k : ℕ) (U : P.affineOpens), (⨆ m : Fin ny, LinearMap.range ((θ m k).app U)) = ⊤) :
    ∀ (k : ℕ) (z : (G k).obj (pullbackChart ι l)), GoodAt hθ 𝔤 l k z := by
  intro k
  induction k with
  | zero =>
    intro z
    have hz := 𝔤.gen l z
    induction hz using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨⟨c, a⟩, rfl⟩ := hx
      exact (goodAt_gen a).smul_app hιq c
    | zero => exact goodAt_zero
    | add x y _ _ hx hy => exact hx.add hy
  | succ k ih =>
    intro z
    have hz : z ∈ ⨆ m : Fin ny, LinearMap.range ((θ m k).app (framesChart ι l)) := by
      rw [hgen k (framesChart ι l)]; exact Submodule.mem_top
    induction hz using Submodule.iSup_induction' with
    | mem m x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact (ih w).app m
    | zero => exact goodAt_zero
    | add x y _ _ hx hy => exact hx.add hy

theorem sat_single (hιq : ι ≫ ProjSpace.π A r = q)
    (hgen : ∀ (k : ℕ) (U : P.affineOpens), (⨆ m : Fin ny, LinearMap.range ((θ m k).app U)) = ⊤)
    (hq : (G k).IsQuasicoherent) {n : ℕ} {g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)}
    (hg : FramesCompat ι (G k) n g) : Sat hθ 𝔤 l (n : ℤ) (FamilyFrames.single ι G (n : ℤ) k g) := by
  obtain ⟨n', g', hg', hs', hz'⟩ := goodAt_all hιq hgen k (g l)

  obtain ⟨hg1, hs1, hz1⟩ := GoodAt.bump hg' hs' hz' n
  rw [add_comm n' n] at hg1 hs1
  have hg2 := framesCompat_pow_smul (l := l) hg n'
  have hs2 : Sat hθ 𝔤 l ((n + n' : ℕ) : ℤ) (FamilyFrames.single ι G ((n + n' : ℕ) : ℤ) k fun j => frameUnit ι j l ^ n' ⨳ g j) :=
    sat_single_congr hq hg2 hg1 (by rw [hz1, frameUnit_self, one_pow, one_smul]) hs1
  rw [Nat.cast_add, ← xMul_pow_single] at hs2
  exact Sat.of_xMul_pow n' hs2

theorem eq_sum_single {e : ℤ} {f : (Mf ι hθ).M} (hf : f ∈ (Mf ι hθ).grade e) :
    f = ∑ k ∈ hf.2.2.2.toFinset, FamilyFrames.single ι G e k (f e k) := by
  refine FamilyFrames.ext fun e' k' j => ?_
  rw [sum_apply']
  by_cases he : e' = e
  · subst he
    rw [Finset.sum_eq_single k' (fun k _ hk => by rw [FamilyFrames.single_apply_of_ne_level _ _ (Ne.symm hk), Pi.zero_apply])
      (fun hk => by
        have h0 : f e' k' = 0 := by
          by_contra h
          exact hk (hf.2.2.2.mem_toFinset.mpr h)
        rw [FamilyFrames.single_apply_self, h0]; rfl)]
    rw [FamilyFrames.single_apply_self]
  · rw [show f e' k' j = 0 from congrFun (congrFun (hf.1 e' he) k') j]
    exact (Finset.sum_eq_zero fun k _ => by rw [FamilyFrames.single_apply_of_ne_degree he, Pi.zero_apply, Pi.zero_apply]).symm

theorem sat_of_mem_grade (hιq : ι ≫ ProjSpace.π A r = q)
    (hgen : ∀ (k : ℕ) (U : P.affineOpens), (⨆ m : Fin ny, LinearMap.range ((θ m k).app U)) = ⊤)
    (hq : ∀ k, (G k).IsQuasicoherent) {e : ℤ} {f : (Mf ι hθ).M} (hf : f ∈ (Mf ι hθ).grade e) : Sat hθ 𝔤 l e f := by
  by_cases he : e < 0
  · have h0 : f = 0 := FamilyFrames.ext fun e' k' j => by
      by_cases hee : e' = e
      · subst hee; exact congrFun (congrFun (hf.2.1 he) k') j
      · exact congrFun (congrFun (hf.1 e' hee) k') j
    rw [h0]; exact sat_zero e
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, e = n := ⟨e.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [eq_sum_single hf]
    refine Sat.sum _ fun k _ => sat_single hιq hgen (hq k) ?_
    have h := hf.2.2.1 (by omega) k
    rwa [Int.toNat_natCast] at h

end Generation

section GensFinite

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)}

theorem res_injective_of_eq (F : OModulePresheaf q) {U W : P.Opens} (e : W = U) (h : W ≤ U) :
    Function.Injective (F.res h) := by
  subst e
  intro x y hxy
  rwa [F.res_refl_apply, F.res_refl_apply] at hxy

theorem exists_framesCompat_apply_eq (F : OModulePresheaf q) (hq : F.IsQuasicoherent) (l : Fin (r + 1))
    (z : F.obj (pullbackChart ι l)) :
    ∃ (N : ℕ) (g : ∀ j : Fin (r + 1), F.obj (pullbackChart ι j)), FramesCompat ι F N g ∧ g l = z := by
  have hle : (⨅ v : Fin (0 + 1), pullbackChart ι ((fun _ => l) v)) ≤ pullbackChart ι l := iInf_le _ 0
  have hge : pullbackChart ι l ≤ ⨅ v : Fin (0 + 1), pullbackChart ι ((fun _ => l) v) := le_iInf fun _ => le_rfl
  obtain ⟨N, t', ht', hres⟩ :=
    exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent ι F hq (fun _ : Fin (0 + 1) => l) 0
      (F.res hle z)
  refine ⟨0 + N * (0 + 1), t', ht', ?_⟩
  have h := hres l
  simp only [frameUnit_self, map_one, Finset.prod_const_one, one_pow, pow_zero, mul_one, one_smul] at h
  rw [res_res] at h
  have hW : pullbackChart ι l ⊓ (⨅ v : Fin (0 + 1), pullbackChart ι ((fun _ => l) v)) = pullbackChart ι l :=
    inf_eq_left.mpr hge
  exact res_injective_of_eq F hW _ h

variable (ι) (G : ℕ → OModulePresheaf q)

theorem nonempty_gens [IsFinite ι] (hc : (G 0).IsCoherent) (hq : (G 0).IsQuasicoherent) : Nonempty (Gens ι G) := by
  classical
  have hU : ∀ l : Fin (r + 1), IsAffineOpen (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)
      (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A)) := fun l =>
    Proj.isAffineOpen_basicOpen _ _ (X_mem_one A r l) one_pos

  have hβ : ∀ l : Fin (r + 1), ∃ (T : ℕ) (β : Fin T → Γ(P, pullbackChart ι l)), ∀ gf : Γ(P, pullbackChart ι l),
      ∃ c : Fin T → Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A),
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A) (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A)),
        gf = ∑ t, (show Γ(P, pullbackChart ι l) from
          (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A) (MvPolynomial.X l))).hom (c t)) * β t := by
    intro l
    letI alg : Algebra
        Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A),
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A) (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A))
        Γ(P, pullbackChart ι l) :=
      (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)
        (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A))).hom.toAlgebra
    haveI hfin : Module.Finite
        Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A),
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A) (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A))
        Γ(P, pullbackChart ι l) :=
      IsFinite.finite_app ι _ (hU l)
    obtain ⟨T, β, hβ⟩ := Module.Finite.exists_fin
      (R := Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A),
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A) (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A)))
      (M := Γ(P, pullbackChart ι l))
    refine ⟨T, β, fun gf => ?_⟩
    have hgf : gf ∈ Submodule.span
        Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A),
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A) (MvPolynomial.X l : MvPolynomial (Fin (r + 1)) A))
        (Set.range β) := by rw [hβ]; exact Submodule.mem_top
    obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hgf
    exact ⟨c, by rw [← hc']; rfl⟩

  have hw : ∀ l : Fin (r + 1), ∃ (n : ℕ) (w : Fin n → (G 0).obj (pullbackChart ι l)),
      Submodule.span Γ(P, pullbackChart ι l) (Set.range w) = ⊤ := by
    intro l
    haveI : Module.Finite Γ(P, pullbackChart ι l) ((G 0).obj (pullbackChart ι l)) := hc (framesChart ι l)
    exact Module.Finite.exists_fin
  choose T β hβ using hβ
  choose n w hw using hw

  have hext := fun σ : (Σ l : Fin (r + 1), Fin (T l) × Fin (n l)) =>
    exists_framesCompat_apply_eq (ι := ι) (G 0) hq σ.1 (β σ.1 σ.2.1 ⨳ w σ.1 σ.2.2)
  choose N g hg using hext
  let d₁ : ℕ := Finset.univ.sup N
  let sg' : (Σ l : Fin (r + 1), Fin (T l) × Fin (n l)) → ∀ j : Fin (r + 1), (G 0).obj (pullbackChart ι j) :=
    fun σ j => frameUnit ι j σ.1 ^ (d₁ - N σ) ⨳ g σ j
  have hsg'c : ∀ σ, FramesCompat ι (G 0) d₁ (sg' σ) := fun σ => by
    have h := framesCompat_pow_smul (l := σ.1) (hg σ).1 (d₁ - N σ)
    rwa [Nat.add_sub_cancel' (Finset.le_sup (f := N) (Finset.mem_univ σ))] at h
  have hsg'l : ∀ σ, sg' σ σ.1 = β σ.1 σ.2.1 ⨳ w σ.1 σ.2.2 := fun σ => by
    show frameUnit ι σ.1 σ.1 ^ (d₁ - N σ) ⨳ g σ σ.1 = _
    rw [frameUnit_self, one_pow, one_smul, (hg σ).2]
  let ε := Fintype.equivFin (Σ l : Fin (r + 1), Fin (T l) × Fin (n l))
  refine ⟨⟨d₁, Fintype.card (Σ l : Fin (r + 1), Fin (T l) × Fin (n l)), fun a => sg' (ε.symm a),
    fun a => hsg'c (ε.symm a), fun l z => ?_⟩⟩

  have hz : z ∈ Submodule.span Γ(P, pullbackChart ι l) (Set.range (w l)) := by rw [hw l]; exact Submodule.mem_top
  obtain ⟨gf, hgf⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hz
  choose c hcβ using fun i => hβ l (gf i)
  rw [← hgf]
  refine AddSubmonoid.sum_mem _ fun i _ => ?_
  rw [hcβ i, Finset.sum_smul]
  refine AddSubmonoid.sum_mem _ fun t _ => ?_
  rw [mul_smul]
  refine AddSubmonoid.subset_closure ⟨(c i t, ε ⟨l, (t, i)⟩), ?_⟩
  show _ ⨳ sg' (ε.symm (ε ⟨l, (t, i)⟩)) l = _
  rw [Equiv.symm_apply_apply]
  exact congrArg _ (hsg'l ⟨l, (t, i)⟩)

end GensFinite

section Main

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsFinite ι]
  {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
  (G : ℕ → OModulePresheaf q) (hc : ∀ k, (G k).IsCoherent) (hq : ∀ k, (G k).IsQuasicoherent)
  {ny : ℕ} (θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))) (hθ : YComm G θ)
  (hgen : ∀ (k : ℕ) (U : P.affineOpens), (⨆ m : Fin ny, LinearMap.range ((θ m k).app U)) = ⊤)

include hιq hc hq hgen in
theorem main :
    ∃ (D : GradedModule (MvPolynomial (Fin ny) A) r) (_ : GradedModule.IsFG D)
      (h : GradedModule.Hom D (familyFramesGradedModule ι G θ hθ)),
      Function.Injective h.toLinearMap ∧
      ∀ (e : ℤ) (f : (familyFramesGradedModule ι G θ hθ).M),
        f ∈ (familyFramesGradedModule ι G θ hθ).grade e → ∀ l : Fin (r + 1),
          ∃ (N : ℕ) (f' : D.M), f' ∈ D.grade (e + N) ∧
            h.toLinearMap f' = ((familyFramesGradedModule ι G θ hθ).xMul l ^ N) f := by
  obtain ⟨𝔤⟩ := nonempty_gens ι G (hc 0) (hq 0)
  refine ⟨D hθ 𝔤, ⟨pres hθ 𝔤⟩, hHom hθ 𝔤, hHom_injective 𝔤, fun e f hf l => ?_⟩
  obtain ⟨N, p, hp, hΦ⟩ := sat_of_mem_grade (hθ := hθ) (𝔤 := 𝔤) (l := l) hιq hgen hq hf
  exact ⟨N, (K hθ 𝔤).mkQ p, ⟨p, hp, rfl⟩, by rw [hHom_mkQ, hΦ]⟩

end Main

end P2mFamFG

end

theorem solution
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsFinite ι]
    {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (G : ℕ → OModulePresheaf q) (hc : ∀ k, (G k).IsCoherent) (hq : ∀ k, (G k).IsQuasicoherent)
    {s : ℕ} (θ : Fin s → ∀ k : ℕ, OModulePresheaf.AffHom (G k) (G (k + 1))) (hθ : OModulePresheaf.YComm G θ)
    (hgen : ∀ (k : ℕ) (U : P.affineOpens), (⨆ m : Fin s, LinearMap.range ((θ m k).app U)) = ⊤) :
    ∃ (D : ProjSpaceCech.GradedModule (MvPolynomial (Fin s) A) r) (_ : ProjSpaceCech.GradedModule.IsFG D)
      (h : ProjSpaceCech.GradedModule.Hom D (OModulePresheaf.familyFramesGradedModule ι G θ hθ)),
      Function.Injective h.toLinearMap ∧
      ∀ (e : ℤ) (f : (OModulePresheaf.familyFramesGradedModule ι G θ hθ).M),
        f ∈ (OModulePresheaf.familyFramesGradedModule ι G θ hθ).grade e → ∀ l : Fin (r + 1),
          ∃ (N : ℕ) (f' : D.M), f' ∈ D.grade (e + N) ∧
            h.toLinearMap f' = ((OModulePresheaf.familyFramesGradedModule ι G θ hθ).xMul l ^ N) f :=
  P2mFamFG.main ι hιq G hc hq θ hθ hgen

end S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite (solution)
