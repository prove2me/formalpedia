-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:43.845827+00:00
-- url     : https://prove2.me/theorems/b33f56a8-d84e-4170-9a28-d5dcdeb1569e
-- title:
--   Restrict Pullback Iso Hom App Pullback Sections
-- statement:
--   Definitions and structural lemmas for Restrict Pullback Iso Hom App Pullback Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_res
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_zero
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen_iff
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_iff_forall_affine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_forall_exists_affine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_restrict_fromSpec_iff
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_res_res
import Theorems.Thm_GlobalTheory_QCoh_res_res_ring
import Theorems.Thm_GlobalTheory_QCoh_res_self
import Theorems.Thm_GlobalTheory_QCoh_res_self_ring
import Theorems.Thm_GlobalTheory_QCoh_restrict_fromSpec_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
namespace GlobalTheory.QCoh
section Qcqs
variable {X : Scheme.{u}} (F : X.Modules) {U W : X.Opens}
theorem section_eq_of_cover {ι : Type*} (𝒰 : ι → X.Opens) (h : ∀ i, 𝒰 i ≤ W)
    (hcov : W ≤ iSup 𝒰) (s t : Γ(F, W))
    (H : ∀ i, F.presheaf.map (homOfLE (h i)).op s = F.presheaf.map (homOfLE (h i)).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) 𝒰 W
    (fun i ↦ homOfLE (h i)) hcov s t H
theorem exists_finite_affine_cover_of_isCompact (hW : IsCompact (W : Set X)) :
    ∃ (ι : Type u) (_ : Fintype ι) (𝒰 : ι → X.Opens), (∀ i, IsAffineOpen (𝒰 i)) ∧
      W = iSup 𝒰 := by
  obtain ⟨s, hs', hs⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hW, W.2⟩
  exact ⟨s, hs'.fintype, fun i ↦ i.1.1, fun i ↦ i.1.2, by ext1; simpa using hs⟩
variable [F.IsQuasicoherent]
theorem exists_pow_res_smul_eq_zero_of_isCompact (hW : IsCompact (W : Set X)) (h : W ≤ U)
    (f : Γ(X, U)) (t : Γ(F, W))
    (ht : F.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen f ≤ W)).op t = 0) :
    ∃ n : ℕ, X.presheaf.map (homOfLE h).op f ^ n • t = 0 := by
  obtain ⟨ι, _, 𝒰, haff, hcov⟩ := exists_finite_affine_cover_of_isCompact hW
  have hle (i : ι) : 𝒰 i ≤ W := hcov ▸ le_iSup 𝒰 i
  have H (i : ι) : ∃ n : ℕ, X.presheaf.map (homOfLE ((hle i).trans h)).op f ^ n •
      F.presheaf.map (homOfLE (hle i)).op t = 0 := by
    refine exists_pow_smul_eq_zero F (haff i) _ (V := 𝒰 i ⊓ X.basicOpen f) inf_le_left
      (X.basicOpen_res _ _).symm _ ?_
    rw [res_res, ← res_res F inf_le_left (inf_le_inf_right _ (hle i)), ht, map_zero]
  choose n hn using H
  refine ⟨Finset.univ.sup n, section_eq_of_cover F 𝒰 hle hcov.le _ _ fun i ↦ ?_⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ i))
  rw [F.map_smul, map_pow, res_res_ring, hm, pow_add, mul_smul, hn, smul_zero, map_zero]
theorem exists_pow_res_smul_eq_res_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) (s : Γ(F, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(F, U)), X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s =
      F.presheaf.map (homOfLE (X.basicOpen_le f)).op t := by
  obtain ⟨ι, _, 𝒰, haff, hcov⟩ := exists_finite_affine_cover_of_isCompact hU
  have hle (i : ι) : 𝒰 i ≤ U := hcov ▸ le_iSup 𝒰 i
  have H (i : ι) : ∃ (n : ℕ) (t : Γ(F, 𝒰 i)),
      X.presheaf.map (homOfLE ((inf_le_left : 𝒰 i ⊓ X.basicOpen f ≤ _).trans (hle i))).op f ^ n •
        F.presheaf.map (homOfLE (inf_le_right : 𝒰 i ⊓ X.basicOpen f ≤ _)).op s =
      F.presheaf.map (homOfLE inf_le_left).op t := by
    have := exists_pow_smul_eq_res F (haff i) (X.presheaf.map (homOfLE (hle i)).op f)
      (V := 𝒰 i ⊓ X.basicOpen f) inf_le_left (X.basicOpen_res _ _).symm
      (F.presheaf.map (homOfLE inf_le_right).op s)
    rwa [res_res_ring] at this
  choose n t ht using H
  have H' (i : ι) : ∃ (t : Γ(F, 𝒰 i)),
      X.presheaf.map (homOfLE ((inf_le_left : 𝒰 i ⊓ X.basicOpen f ≤ _).trans (hle i))).op f ^
        Finset.univ.sup n •
        F.presheaf.map (homOfLE (inf_le_right : 𝒰 i ⊓ X.basicOpen f ≤ _)).op s =
      F.presheaf.map (homOfLE inf_le_left).op t := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ i))
    refine ⟨X.presheaf.map (homOfLE (hle i)).op f ^ m • t i, ?_⟩
    rw [F.map_smul, map_pow, res_res_ring, hm, pow_add, mul_smul, ht]
  generalize Finset.univ.sup n = N at H'
  clear ht t n
  choose t ht using H'
  have ht' (i : ι) (V : X.Opens) (h₁ : V ≤ 𝒰 i) (h₂ : V ≤ X.basicOpen f) :
      F.presheaf.map (homOfLE h₁).op (t i) =
        X.presheaf.map (homOfLE (h₁.trans (hle i))).op f ^ N •
          F.presheaf.map (homOfLE h₂).op s := by
    rw [← res_res F inf_le_left (le_inf h₁ h₂), ← ht, F.map_smul, map_pow, res_res_ring, res_res]
  have H (p : ι × ι) : ∃ m : ℕ,
      X.presheaf.map (homOfLE ((inf_le_left : 𝒰 p.1 ⊓ 𝒰 p.2 ≤ _).trans (hle p.1))).op f ^ m •
        (F.presheaf.map (homOfLE (inf_le_left : 𝒰 p.1 ⊓ 𝒰 p.2 ≤ _)).op (t p.1) -
          F.presheaf.map (homOfLE inf_le_right).op (t p.2)) = 0 := by
    refine exists_pow_res_smul_eq_zero_of_isCompact F
      (hU' _ _ (hle p.1) (𝒰 p.1).2 (haff _).isCompact (hle p.2) (𝒰 p.2).2 (haff _).isCompact)
      _ f _ ?_
    rw [map_sub, res_res, res_res, ht' _ _ _ inf_le_right, ht' _ _ _ inf_le_right, sub_self]
  choose m hm using H
  obtain ⟨T, hT, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) 𝒰 U (fun i ↦ homOfLE (hle i)) hcov.le
    (fun i ↦ X.presheaf.map (homOfLE (hle i)).op f ^ Finset.univ.sup m • t i) (by
      intro i j
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := m) (Finset.mem_univ (i, j)))
      change F.presheaf.map (homOfLE inf_le_left).op _ = F.presheaf.map (homOfLE inf_le_right).op _
      rw [F.map_smul, F.map_smul, map_pow, map_pow, res_res_ring, res_res_ring, ← sub_eq_zero,
        ← smul_sub, hk, pow_add, mul_smul, hm (i, j), smul_zero])
  replace hT (i : ι) : F.presheaf.map (homOfLE (hle i)).op T =
    X.presheaf.map (homOfLE (hle i)).op f ^ Finset.univ.sup m • t i := hT i
  refine ⟨Finset.univ.sup m + N, T, section_eq_of_cover F (fun i ↦ 𝒰 i ⊓ X.basicOpen f)
    (fun _ ↦ inf_le_right) ?_ _ _ fun i ↦ ?_⟩
  · rw [← iSup_inf_eq, ← hcov]
    exact le_inf (X.basicOpen_le f) le_rfl
  · rw [res_res, ← res_res F (hle i) inf_le_left, hT, F.map_smul, F.map_smul, map_pow, map_pow,
      res_res_ring, res_res_ring, ht' _ _ _ inf_le_right, pow_add, mul_smul]
end Qcqs
section Push
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
theorem pushforward_smul (V : Y.Opens) (r : Γ(Y, V))
    (s : Γ((Scheme.Modules.pushforward f).obj F, V)) :
    r • s = (f.app V r • (show Γ(F, f ⁻¹ᵁ V) from s) : Γ(F, f ⁻¹ᵁ V)) := rfl
instance isQuasicoherent_pushforward [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affine _).mpr fun V hV g ↦ ?_
  have hc : IsCompact (f ⁻¹ᵁ V : Set X) := f.isCompact_preimage hV.isCompact
  have hs : IsQuasiSeparated (f ⁻¹ᵁ V : Set X) := f.isQuasiSeparated_preimage hV.isQuasiSeparated
  have key (D : X.Opens) (h : D ≤ f ⁻¹ᵁ V) (hD : D = X.basicOpen (f.app V g)) :
      (∀ s : Γ(F, D), ∃ (n : ℕ) (t : Γ(F, f ⁻¹ᵁ V)),
        X.presheaf.map (homOfLE h).op (f.app V g) ^ n • s = F.presheaf.map (homOfLE h).op t) ∧
      (∀ t : Γ(F, f ⁻¹ᵁ V), F.presheaf.map (homOfLE h).op t = 0 →
        ∃ n : ℕ, f.app V g ^ n • t = 0) := by
    subst hD
    refine ⟨exists_pow_res_smul_eq_res_of_qcqs F hc hs _, fun t ht ↦ ?_⟩
    have := exists_pow_res_smul_eq_zero_of_isCompact F hc le_rfl (f.app V g) t (by
      rw [← res_res F h inf_le_right, ht, map_zero])
    rwa [res_self_ring] at this
  obtain ⟨h₁, h₂⟩ := key (f ⁻¹ᵁ Y.basicOpen g) (f.preimage_mono (Y.basicOpen_le g))
    (f.preimage_basicOpen g)
  rw [isLocalizedModule_resBasicOpen_iff]
  refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨n, t, ht⟩ := h₁ s
    refine ⟨n, t, Eq.trans ?_ ht⟩
    rw [pushforward_smul, map_pow]
    congr 2
    exact congr($(f.naturality (homOfLE (Y.basicOpen_le g)).op) g)
  · obtain ⟨n, hn⟩ := h₂ t ht
    exact ⟨n, by rw [pushforward_smul, map_pow]; exact hn⟩
end Push
section Sections
variable {X Y : Scheme.{u}}
def homAppLinear {F F' : X.Modules} (φ : F ⟶ F') (U : X.Opens) : Γ(F, U) →ₗ[Γ(X, U)] Γ(F', U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := φ.app_smul
variable (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) {U U' : X.Opens} {V V' : Y.Opens}
abbrev appLEAlgebra (e : U ≤ f ⁻¹ᵁ V) : Algebra Γ(Y, V) Γ(X, U) :=
  (f.appLE V U e).hom.toAlgebra
abbrev appLEModule (e : U ≤ f ⁻¹ᵁ V) : Module Γ(Y, V) Γ(F, U) :=
  Module.compHom Γ(F, U) (f.appLE V U e).hom
theorem appLE_isScalarTower (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEAlgebra f e
    letI := appLEModule f F e
    IsScalarTower Γ(Y, V) Γ(X, U) Γ(F, U) :=
  letI := appLEAlgebra f e
  letI := appLEModule f F e
  .of_algebraMap_smul fun _ _ ↦ rfl
def pullbackSections (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
    Γ(G, V) →ₗ[Γ(Y, V)] Γ((Scheme.Modules.pullback f).obj G, U) :=
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  { toFun s := ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE e).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s)
    map_add' s t := by
      rw [map_add]
      exact map_add _ _ _
    map_smul' r s :=
      (congr(((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE e).op
        $(((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app_smul r s))).trans
        (((Scheme.Modules.pullback f).obj G).map_smul (homOfLE e) (f.app V r) _) }
theorem res_bijective_of_eq (h : U' ≤ U) (e : U' = U) :
    Function.Bijective (F.presheaf.map (homOfLE h).op) := by
  subst e
  have : ⇑(F.presheaf.map (homOfLE h).op) = id := funext (res_self F h)
  rw [this]
  exact Function.bijective_id
theorem fromSpec_image_top (hU : IsAffineOpen U) : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
def sectionsEquivFromSpec (hU : IsAffineOpen U) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F.restrict hU.fromSpec, ⊤) :=
  LinearEquiv.ofBijective (M₂ := Γ(F.restrict hU.fromSpec, ⊤))
    { toFun s := F.presheaf.map (homOfLE (fromSpec_image_le hU ⊤)).op s
      map_add' s t := map_add (F.presheaf.map (homOfLE (fromSpec_image_le hU ⊤)).op).hom s t
      map_smul' r s := (F.map_smul _ r s).trans (restrict_fromSpec_smul F hU ⊤ r _).symm }
    (res_bijective_of_eq F _ (fromSpec_image_top hU))
end Sections
section SpecCase
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
set_option backward.isDefEq.respectTransparency false in

def pushforwardSpecΓIso :
    moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom ≅
      Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
  NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (X₁ := (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj M)
    (X₂ := (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).obj M)
    { __ := AddEquiv.refl _
      map_smul' := fun r m ↦ by
        change (φ r • (show Γ(M, ⊤) from m) : Γ(M, ⊤)) =
          ((Spec.map φ).app ⊤ ((Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op
            ((Scheme.ΓSpecIso R).inv r)) • (show Γ(M, (Spec.map φ) ⁻¹ᵁ ⊤) from m) :)
        rw [Scheme.Modules.smul_Spec_def]
        congr 1
        have h₁ := res_self_ring (X := Spec R) (U := ⊤) le_rfl ((Scheme.ΓSpecIso R).inv r)
        have h₂ := res_self_ring (X := Spec S) (U := ⊤) le_rfl ((Scheme.ΓSpecIso S).inv (φ r))
        refine h₂.trans (Eq.trans ?_ congr((Spec.map φ).app ⊤ $h₁).symm)
        exact congr($(Scheme.ΓSpecIso_inv_naturality φ) r) }) fun _ ↦ rfl
set_option backward.isDefEq.respectTransparency false in

def tildePullbackIso :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ≅
      tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) :=
  (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).ofNatIsoRight
    (pushforwardSpecΓIso φ)).leftAdjointUniq
    (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
set_option backward.isDefEq.respectTransparency false in

def tildeIsoPullback (M : (Spec R).Modules) [M.IsQuasicoherent] :
    tilde ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) ≅
      (Scheme.Modules.pullback (Spec.map φ)).obj M :=
  haveI := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  (tildePullbackIso φ).app _ ≪≫ (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ)
theorem isQuasicoherent_pullback_Spec (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso (tildeIsoPullback φ M)
    (inferInstanceAs (tilde ((ModuleCat.extendScalars φ.hom).obj
      (moduleSpecΓFunctor.obj M))).IsQuasicoherent)
end SpecCase
section Square
variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {p : X' ⟶ Y'} {j : X' ⟶ X} {i : Y' ⟶ Y}
  [IsOpenImmersion i] [IsOpenImmersion j] (w : p ≫ i = j ≫ f)
def restrictPullbackIso :
    Scheme.Modules.restrictFunctor i ⋙ Scheme.Modules.pullback p ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor j :=
  (((Scheme.Modules.restrictAdjunction i).comp
    (Scheme.Modules.pullbackPushforwardAdjunction p)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp p i ≪≫ Scheme.Modules.pushforwardCongr w ≪≫
        (Scheme.Modules.pushforwardComp j f).symm)).leftAdjointUniq
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j))
end Square
section Pull
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) {U : X.Opens} {V : Y.Opens}
theorem exists_affine_pair (x : X) {W : X.Opens} (hx : x ∈ W) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧ U ≤ W ∧
      U ≤ f ⁻¹ᵁ V := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ W ⊓ f ⁻¹ᵁ V from ⟨hx, hxV⟩)
      (W ⊓ f ⁻¹ᵁ V).2
  exact ⟨U, V, hU, hV, hxU, fun _ h ↦ (hle h).1, fun _ h ↦ (hle h).2⟩
variable [G.IsQuasicoherent]
set_option backward.isDefEq.respectTransparency false in

instance isQuasicoherent_pullback : ((Scheme.Modules.pullback f).obj G).IsQuasicoherent := by
  refine isQuasicoherent_of_forall_exists_affine _ fun x ↦ ?_
  obtain ⟨U, V, hU, hV, hx, -, e⟩ := exists_affine_pair f x (W := ⊤) trivial
  refine ⟨U, hU, hx, (isQuasicoherent_restrict_fromSpec_iff _ hU).mp ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
    ((restrictPullbackIso (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e)).app G)
    (isQuasicoherent_pullback_Spec (f.appLE V U e) (G.restrict hV.fromSpec))
end Pull
section Exact
variable {X Y : Scheme.{u}} {F F' : X.Modules}
variable (f : X ⟶ Y)
end Exact
end GlobalTheory.QCoh


