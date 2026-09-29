-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ca5b58e1-8edd-5165-8e52-d27cf41888c0

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top
import Theorems.Thm_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top
import Theorems.Thm_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace X1aRed

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

abbrev RW (W : P.affineOpens) : Type u := ↑(P.presheaf.obj (op W.1))

theorem noeth [IsLocallyNoetherian P] (W : P.affineOpens) : IsNoetherianRing (RW W) :=
  IsLocallyNoetherian.component_noetherian W

theorem exists_pres (H : OModulePresheaf q) (hHc : H.IsCoherent) (W : P.affineOpens) :
    ∃ (n : ℕ) (f : (Fin n → RW W) →ₗ[RW W] H.obj W.1), Function.Surjective f :=
  @Module.Finite.exists_fin' (RW W) (H.obj W.1) _ _ _ (hHc W)

abbrev JU (q : P ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (U : P.Opens) : Ideal Γ(P, U) :=
  I.map (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap

theorem mem_bridge (I : Ideal A) (F : OModulePresheaf q) (U : P.Opens) (m : ℕ) (x : F.obj U) :
    x ∈ JU q I U ^ m • (⊤ : Submodule Γ(P, U) (F.obj U)) ↔ x ∈ I ^ m • (⊤ : Submodule A (F.obj U)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  haveI : IsScalarTower A Γ(P, U) (F.obj U) := F.isScalarTower U
  have h1 : JU q I U ^ m = (I ^ m).map (algebraMap A Γ(P, U)) := (Ideal.map_pow _ I m).symm
  rw [h1, ← Submodule.restrictScalars_mem A, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

theorem pi_mem_smul_top (I : Ideal A) {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (f : ∀ i, M i)
    (hf : ∀ i, f i ∈ I • (⊤ : Submodule A (M i))) : f ∈ I • (⊤ : Submodule A (∀ i, M i)) := by
  rw [← Finset.univ_sum_single f]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : Pi.single i (f i) = LinearMap.single A M i (f i) := rfl
  rw [this]
  have hm : LinearMap.single A M i (f i) ∈ (I • (⊤ : Submodule A (M i))).map (LinearMap.single A M i) :=
    Submodule.mem_map_of_mem (hf i)
  rw [Submodule.map_smul''] at hm
  exact (smul_mono_right I (le_top (a := Submodule.map (LinearMap.single A M i) ⊤))) hm

section Sections

variable {F G H : OModulePresheaf q} (U : P.affineOpens)

theorem ker_appSections_eq (I : Ideal A) (θ : OModulePresheaf.AffHom F G) (m : ℕ)
    (h : LinearMap.ker (θ.app U) = I ^ m • (⊤ : Submodule A (F.obj U.1))) :
    LinearMap.ker (θ.appSections U) = JU q I U.1 ^ m • (⊤ : Submodule Γ(P, U.1) (F.obj U.1)) := by
  ext x
  rw [mem_bridge, ← h, LinearMap.mem_ker, LinearMap.mem_ker, OModulePresheaf.AffHom.appSections_apply]

theorem ker_appSections_le (I : Ideal A) (θ : OModulePresheaf.AffHom F G) (m : ℕ)
    (h : LinearMap.ker (θ.app U) ≤ I ^ m • (⊤ : Submodule A (F.obj U.1))) :
    LinearMap.ker (θ.appSections U) ≤ JU q I U.1 ^ m • (⊤ : Submodule Γ(P, U.1) (F.obj U.1)) := by
  intro x hx
  rw [mem_bridge]
  exact h hx

theorem range_appSections_eq_ker (θ : OModulePresheaf.AffHom F G) (η : OModulePresheaf.AffHom G H)
    (h : LinearMap.range (θ.app U) = LinearMap.ker (η.app U)) :
    LinearMap.range (θ.appSections U) = LinearMap.ker (η.appSections U) := by
  ext x
  have := SetLike.ext_iff.mp h x
  rw [LinearMap.mem_range, LinearMap.mem_ker] at this ⊢
  exact this

theorem comp_appSections_eq (θ : OModulePresheaf.AffHom G H) (η : OModulePresheaf.AffHom F G)
    (κ : OModulePresheaf.AffHom F H) (h : θ.app U ∘ₗ η.app U = κ.app U) :
    θ.appSections U ∘ₗ η.appSections U = κ.appSections U :=
  LinearMap.ext fun x => LinearMap.congr_fun h x

theorem comp_appSections_comm {F' : OModulePresheaf q} (θ : OModulePresheaf.AffHom G H) (η : OModulePresheaf.AffHom F G)
    (θ' : OModulePresheaf.AffHom F' H) (η' : OModulePresheaf.AffHom F F')
    (h : θ.app U ∘ₗ η.app U = θ'.app U ∘ₗ η'.app U) :
    θ.appSections U ∘ₗ η.appSections U = θ'.appSections U ∘ₗ η'.appSections U :=
  LinearMap.ext fun x => LinearMap.congr_fun h x

end Sections

@[reducible] noncomputable def algOf {W W' : P.affineOpens} (h : W'.1 ≤ W.1) : Algebra (RW W) (RW W') :=
  (P.presheaf.map (homOfLE h).op).hom.toAlgebra

@[reducible] noncomputable def modOf (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    Module (RW W) (F.obj W'.1) :=
  Module.compHom (F.obj W'.1) (P.presheaf.map (homOfLE h).op).hom

theorem towOf (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := algOf (P := P) h; letI := modOf F h
    IsScalarTower (RW W) (RW W') (F.obj W'.1) :=
  letI := algOf (P := P) h; letI := modOf F h
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

noncomputable def mu (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := modOf F h
    F.obj W.1 →ₗ[RW W] F.obj W'.1 :=
  letI := modOf F h
  { toFun := F.res h
    map_add' := map_add _
    map_smul' := fun a x => F.res_smul h a x }

theorem mu_apply (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) (x : F.obj W.1) :
    letI := modOf F h
    mu F h x = F.res h x := rfl

theorem flatOf {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := algOf (P := P) h
    Module.Flat (RW W) (RW W') := by
  have e : W'.1 ≤ (𝟙 P : P ⟶ P) ⁻¹ᵁ W.1 := h
  have h1 : RingHom.Flat ((𝟙 P : P ⟶ P).appLE W.1 W'.1 e).hom :=
    HasRingHomProperty.appLE @Flat (f := 𝟙 P) inferInstance W W' e
  have h2 : (𝟙 P : P ⟶ P).appLE W.1 W'.1 e = P.presheaf.map (homOfLE h).op := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    rfl
  rw [h2] at h1
  exact h1

theorem mu_isBaseChange (F : OModulePresheaf q) (hF : F.IsQuasicoherent) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := algOf (P := P) h; letI := modOf F h; letI := towOf F h
    IsBaseChange (RW W') (mu F h) := by
  letI := algOf (P := P) h; letI := modOf F h; letI := towOf F h
  obtain ⟨β, hβ⟩ :=
    AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res F hF W W' h
  exact IsBaseChange.of_equiv β hβ

theorem map_refl (W : P.Opens) (a : Γ(P, W)) : (P.presheaf.map (homOfLE (le_refl W)).op).hom a = a := by
  have : (homOfLE (le_refl W)).op = 𝟙 (op W) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this, CategoryTheory.Functor.map_id]; rfl

abbrev ee (R : Type u) [CommRing R] {r : ℕ} (i : Fin r) : Fin r → R := fun j => if i = j then 1 else 0

noncomputable def bc (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) {r : ℕ}
    (f : (Fin r → RW W) →ₗ[RW W] F.obj W.1) : (Fin r → RW W') →ₗ[RW W'] F.obj W'.1 :=
  ∑ i : Fin r, (LinearMap.proj i).smulRight (F.res h (f (ee (RW W) i)))

theorem bc_apply (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) {r : ℕ}
    (f : (Fin r → RW W) →ₗ[RW W] F.obj W.1) (w : Fin r → RW W') :
    bc F h f w = ∑ i : Fin r, w i • F.res h (f (ee (RW W) i)) := by
  simp only [bc, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

theorem bc_apply_res (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) {r : ℕ}
    (f : (Fin r → RW W) →ₗ[RW W] F.obj W.1) (v : Fin r → RW W) :
    bc F h f (fun i => (P.presheaf.map (homOfLE h).op).hom (v i)) = F.res h (f v) := by
  rw [bc_apply, LinearMap.pi_apply_eq_sum_univ f v, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.res_smul]

theorem appSections_comp_bc {F G : OModulePresheaf q} (θ : OModulePresheaf.AffHom F G) {W W' : P.affineOpens}
    (h : W'.1 ≤ W.1) {r : ℕ} (f : (Fin r → RW W) →ₗ[RW W] F.obj W.1) :
    θ.appSections W' ∘ₗ bc F h f = bc G h (θ.appSections W ∘ₗ f) := by
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.comp_apply, bc_apply, bc_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, OModulePresheaf.AffHom.appSections_apply, LinearMap.comp_apply,
    OModulePresheaf.AffHom.appSections_apply, θ.naturality_apply h]

end X1aRed

namespace X1aRed

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

theorem mem_span_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) (y : N) :
    y ∈ Submodule.span S (Set.range f) := by
  induction y using hf.inductionOn with
  | zero => exact Submodule.zero_mem _
  | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ s hn
  | add n₁ n₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂

theorem bc_surjective (GE : OModulePresheaf q) (hGEq : GE.IsQuasicoherent) {W W' : P.affineOpens} (h : W'.1 ≤ W.1)
    {r : ℕ} (p : (Fin r → RW W) →ₗ[RW W] GE.obj W.1) (hp : Function.Surjective p) :
    Function.Surjective (bc GE h p) := by
  letI := algOf (P := P) h; letI := modOf GE h; letI := towOf GE h
  have hμ := mu_isBaseChange GE hGEq h
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro y _
  refine Submodule.span_le.mpr ?_ (mem_span_of_isBaseChange hμ y)
  rintro _ ⟨m, rfl⟩
  obtain ⟨v, rfl⟩ := hp m
  exact ⟨fun i => (P.presheaf.map (homOfLE h).op).hom (v i), bc_apply_res GE h p v⟩

theorem transport (GE GK Fm : OModulePresheaf q) (hGEq : GE.IsQuasicoherent) (hGKq : GK.IsQuasicoherent)
    {W W' : P.affineOpens} (h : W'.1 ≤ W.1) {r : ℕ}
    (p : (Fin r → RW W) →ₗ[RW W] GE.obj W.1)
    (lam : OModulePresheaf.AffHom GK Fm) (ℓ : (Fin r → RW W) →ₗ[RW W] Fm.obj W.1)
    (δ : ↥(LinearMap.ker p) →ₗ[RW W] GK.obj W.1) (hδ : lam.appSections W ∘ₗ δ = ℓ ∘ₗ (LinearMap.ker p).subtype) :
    ∃ δ' : ↥(LinearMap.ker (bc GE h p)) →ₗ[RW W'] GK.obj W'.1,
      (∀ (s : ↥(LinearMap.ker p))
         (hs : (fun i => (P.presheaf.map (homOfLE h).op).hom ((s : Fin r → RW W) i)) ∈ LinearMap.ker (bc GE h p)),
         δ' ⟨_, hs⟩ = GK.res h (δ s)) ∧
      lam.appSections W' ∘ₗ δ' = bc Fm h ℓ ∘ₗ (LinearMap.ker (bc GE h p)).subtype := by
  letI := algOf (P := P) h
  letI := modOf GE h; letI := towOf GE h
  letI := modOf GK h; letI := towOf GK h
  haveI := flatOf (P := P) h
  obtain ⟨g, hgc, hg, -⟩ := LinearMap.exists_isBaseChange_ker_span_range_eq_top_of_flat
      (mu GE h) (mu_isBaseChange GE hGEq h) p (bc GE h p) (fun v => bc_apply_res GE h p v)
  have hgv : ∀ s : ↥(LinearMap.ker p),
      ((g s : ↥(LinearMap.ker (bc GE h p))) : Fin r → RW W') = fun i => (P.presheaf.map (homOfLE h).op).hom ((s : Fin r → RW W) i) :=
    fun s => funext fun i => hgc s i
  refine ⟨hg.lift (mu GK h ∘ₗ δ), fun s hs => ?_, ?_⟩
  · have : (⟨_, hs⟩ : ↥(LinearMap.ker (bc GE h p))) = g s := Subtype.ext (hgv s).symm
    rw [this, hg.lift_eq]
    rfl
  · refine hg.algHom_ext _ _ fun s => ?_
    rw [LinearMap.comp_apply, hg.lift_eq, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, hgv,
      bc_apply_res, mu_apply, OModulePresheaf.AffHom.appSections_apply, lam.naturality_apply h]
    congr 1
    exact LinearMap.congr_fun hδ s

noncomputable def gres {W W' : P.affineOpens} (h : W'.1 ≤ W.1) (r : ℕ) : (Fin r → RW W) →+ (Fin r → RW W') where
  toFun v i := (P.presheaf.map (homOfLE h).op).hom (v i)
  map_zero' := funext fun _ => map_zero _
  map_add' v w := funext fun i => map_add _ _ _

theorem gres_apply {W W' : P.affineOpens} (h : W'.1 ≤ W.1) (r : ℕ) (v : Fin r → RW W) (i : Fin r) :
    gres h r v i = (P.presheaf.map (homOfLE h).op).hom (v i) := rfl

theorem gres_smul {W W' : P.affineOpens} (h : W'.1 ≤ W.1) (r : ℕ) (a : RW W) (v : Fin r → RW W) :
    gres h r (a • v) = (P.presheaf.map (homOfLE h).op).hom a • gres h r v :=
  funext fun i => by
    show (P.presheaf.map (homOfLE h).op).hom (a * v i) = (P.presheaf.map (homOfLE h).op).hom a * (P.presheaf.map (homOfLE h).op).hom (v i)
    exact map_mul _ _ _

def gleft (R : Type u) [CommRing R] (r₁ r₂ : ℕ) : (Fin r₁ → R) →+ (Fin (r₁ + r₂) → R) where
  toFun v := Fin.append v 0
  map_zero' := by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_add' v w := by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

def gright (R : Type u) [CommRing R] (r₁ r₂ : ℕ) : (Fin r₂ → R) →+ (Fin (r₁ + r₂) → R) where
  toFun w := Fin.append 0 w
  map_zero' := by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_add' v w := by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem gleft_smul (R : Type u) [CommRing R] (r₁ r₂ : ℕ) (a : R) (v : Fin r₁ → R) :
    gleft R r₁ r₂ (a • v) = a • gleft R r₁ r₂ v := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [gleft]

theorem gright_smul (R : Type u) [CommRing R] (r₁ r₂ : ℕ) (a : R) (w : Fin r₂ → R) :
    gright R r₁ r₂ (a • w) = a • gright R r₁ r₂ w := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [gright]

abbrev π₁ (R : Type u) [CommRing R] (r₁ r₂ : ℕ) : (Fin (r₁ + r₂) → R) →ₗ[R] (Fin r₁ → R) :=
  LinearMap.funLeft R R (Fin.castAdd r₂)
abbrev π₂ (R : Type u) [CommRing R] (r₁ r₂ : ℕ) : (Fin (r₁ + r₂) → R) →ₗ[R] (Fin r₂ → R) :=
  LinearMap.funLeft R R (Fin.natAdd r₁)

theorem π₁_append {R : Type u} [CommRing R] {r₁ r₂ : ℕ} (v : Fin r₁ → R) (w : Fin r₂ → R) :
    π₁ R r₁ r₂ (Fin.append v w) = v := by
  funext i; simp [LinearMap.funLeft_apply]

theorem π₂_append {R : Type u} [CommRing R] {r₁ r₂ : ℕ} (v : Fin r₁ → R) (w : Fin r₂ → R) :
    π₂ R r₁ r₂ (Fin.append v w) = w := by
  funext i; simp [LinearMap.funLeft_apply]

abbrev idx (K : P.OrderedAffineCover) (s : K.Idx 1) (j : Fin 2) : K.ι := (K.face s j).1 0

theorem inter_le_idx (K : P.OrderedAffineCover) (s : K.Idx 1) (j : Fin 2) : K.inter s ≤ K.U (idx K s j) :=
  (K.inter_le_inter_face s j).trans (K.inter_le (K.face s j) 0)

abbrev Uc (K : P.OrderedAffineCover) (i : K.ι) : P.affineOpens := ⟨K.U i, K.isAffineOpen i⟩

end X1aRed

namespace X1aRed

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

theorem chart_local (I : Ideal A) [IsLocallyNoetherian P]
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (U : P.affineOpens) {r : ℕ} (p : (Fin r → RW U) →ₗ[RW U] GE.obj U.1) :
    ∃ (ℓ : ∀ n : ℕ, (Fin r → RW U) →ₗ[RW U] (F n).obj U.1) (δs : ∀ n : ℕ, ↥(LinearMap.ker p) →ₗ[RW U] GK.obj U.1),
      (∀ n, (ε n).appSections U ∘ₗ ℓ n = (ψE n).appSections U ∘ₗ p) ∧
      (∀ n, (φ n).appSections U ∘ₗ ℓ (n + 1) = ℓ n) ∧
      (∀ n, (lam n).appSections U ∘ₗ δs n = ℓ n ∘ₗ (LinearMap.ker p).subtype) ∧
      (∀ n, δs (n + 1) - δs n ∈ JU q I U.1 ^ (n + 1) • (⊤ : Submodule (RW U) (↥(LinearMap.ker p) →ₗ[RW U] GK.obj U.1))) ∧
      (∀ d n, (lam n).appSections U ∘ₗ δs (n + d) = ℓ n ∘ₗ (LinearMap.ker p).subtype) := by
  haveI : IsNoetherianRing (RW U) := noeth U
  haveI : Module.Finite (RW U) (GK.obj U.1) := hGKc U
  obtain ⟨ℓ, δs, ha, hb, hc, hd⟩ :=
    LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top
      (JU q I U.1) (GE := GE.obj U.1) (GK := GK.obj U.1) p
      (fun k => (F k).obj U.1) (fun k => (E k).obj U.1)
      (fun k => (φ k).appSections U) (fun k => hφs k U)
      (fun k => ker_appSections_eq U I (φ k) (k + 1) (hφk k U))
      (fun k => (τ k).appSections U)
      (fun k => ker_appSections_eq U I (τ k) (k + 1) (hτk k U))
      (fun k => (ε k).appSections U) (fun k => hεs k U)
      (fun k => comp_appSections_comm U (τ k) (ε (k + 1)) (ε k) (φ k) (hεc k U))
      (fun k => (ψE k).appSections U)
      (fun k => comp_appSections_eq U (τ k) (ψE (k + 1)) (ψE k) (hψEc k U))
      (fun k => (lam k).appSections U)
      (fun k => comp_appSections_eq U (φ k) (lam (k + 1)) (lam k) (hlamc k U))
      (fun k => range_appSections_eq_ker U (lam k) (ε k) (hlamr k U))
      ((hlami U).imp fun c hc k => ker_appSections_le U I (lam (k + c)) (k + 1) (hc k))
  refine ⟨ℓ, δs, ha, hb, hc, hd, ?_⟩
  intro d
  induction d with
  | zero => intro n; exact hc n
  | succ d ih =>
    intro n
    rw [show n + (d + 1) = (n + 1) + d by omega,
      ← comp_appSections_eq U (φ n) (lam (n + 1)) (lam n) (hlamc n U), LinearMap.comp_assoc,
      ih (n + 1), ← LinearMap.comp_assoc, hb n]

theorem hleD (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q] (K : P.OrderedAffineCover) (s : K.Idx 1) (j : Fin 2) :
    (K.affineInter q s).1 ≤ (Uc K (idx K s j)).1 :=
  inter_le_idx K s j

noncomputable def PsD [IsSeparated q] (GE : OModulePresheaf q) (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
    (pr : ∀ i : K.ι, (Fin (rk i) → RW (Uc K i)) →ₗ[RW (Uc K i)] GE.obj (K.U i)) (s : K.Idx 1) :
    (Fin (rk (idx K s 0) + rk (idx K s 1)) → RW (K.affineInter q s)) →ₗ[RW (K.affineInter q s)] GE.obj (K.inter s) :=
  bc GE (hleD q K s 0) (pr (idx K s 0)) ∘ₗ π₁ (RW (K.affineInter q s)) _ _
    + bc GE (hleD q K s 1) (pr (idx K s 1)) ∘ₗ π₂ (RW (K.affineInter q s)) _ _

theorem PsD_append [IsSeparated q] (GE : OModulePresheaf q) (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
    (pr : ∀ i : K.ι, (Fin (rk i) → RW (Uc K i)) →ₗ[RW (Uc K i)] GE.obj (K.U i)) (s : K.Idx 1)
    (v : Fin (rk (idx K s 0)) → RW (K.affineInter q s)) (w : Fin (rk (idx K s 1)) → RW (K.affineInter q s)) :
    PsD GE K rk pr s (Fin.append v w) = bc GE (hleD q K s 0) (pr (idx K s 0)) v + bc GE (hleD q K s 1) (pr (idx K s 1)) w := by
  simp only [PsD, LinearMap.add_apply, LinearMap.comp_apply, π₁_append, π₂_append]

end X1aRed

namespace X1aRed

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

set_option maxHeartbeats 3200000 in

theorem overlap_aux (I : Ideal A) (GE GK X : OModulePresheaf q) (hGEq : GE.IsQuasicoherent) (hGKq : GK.IsQuasicoherent)
    (εX : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (GK.obj W.1) (LinearMap.ker p).subtype))))
    (hXf : ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] GE.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = GE.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] GK.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = GK.res h (δ s)),
        X.res h ((εX W r p hp).symm (Submodule.Quotient.mk δ)) = (εX W' r' p' hp').symm (Submodule.Quotient.mk δ'))
    (Fm Em : OModulePresheaf q) (lam : OModulePresheaf.AffHom GK Fm) (εm : OModulePresheaf.AffHom Fm Em)
    (ψEm : OModulePresheaf.AffHom GE Em)
    {W0 W1 W' : P.affineOpens} (h0 : W'.1 ≤ W0.1) (h1 : W'.1 ≤ W1.1)
    {r0 r1 : ℕ} (p0 : (Fin r0 → RW W0) →ₗ[RW W0] GE.obj W0.1) (hp0 : Function.Surjective p0)
    (p1 : (Fin r1 → RW W1) →ₗ[RW W1] GE.obj W1.1) (hp1 : Function.Surjective p1)
    (ℓ0 : (Fin r0 → RW W0) →ₗ[RW W0] Fm.obj W0.1) (hℓ0 : εm.appSections W0 ∘ₗ ℓ0 = ψEm.appSections W0 ∘ₗ p0)
    (ℓ1 : (Fin r1 → RW W1) →ₗ[RW W1] Fm.obj W1.1) (hℓ1 : εm.appSections W1 ∘ₗ ℓ1 = ψEm.appSections W1 ∘ₗ p1)
    (δ0 : ↥(LinearMap.ker p0) →ₗ[RW W0] GK.obj W0.1) (hδ0 : lam.appSections W0 ∘ₗ δ0 = ℓ0 ∘ₗ (LinearMap.ker p0).subtype)
    (δ1 : ↥(LinearMap.ker p1) →ₗ[RW W1] GK.obj W1.1) (hδ1 : lam.appSections W1 ∘ₗ δ1 = ℓ1 ∘ₗ (LinearMap.ker p1).subtype)
    (P' : (Fin (r0 + r1) → RW W') →ₗ[RW W'] GE.obj W'.1)
    (hP' : ∀ (v : Fin r0 → RW W') (w : Fin r1 → RW W'), P' (Fin.append v w) = bc GE h0 p0 v + bc GE h1 p1 w)
    (e : ℕ)
    (hov : ∀ (ℓ₁ : (Fin r0 → RW W') →ₗ[RW W'] Fm.obj W'.1) (_ : εm.appSections W' ∘ₗ ℓ₁ = ψEm.appSections W' ∘ₗ bc GE h0 p0)
      (ℓ₂ : (Fin r1 → RW W') →ₗ[RW W'] Fm.obj W'.1) (_ : εm.appSections W' ∘ₗ ℓ₂ = ψEm.appSections W' ∘ₗ bc GE h1 p1)
      (δ₁ : ↥(LinearMap.ker (bc GE h0 p0)) →ₗ[RW W'] GK.obj W'.1)
      (_ : lam.appSections W' ∘ₗ δ₁ = ℓ₁ ∘ₗ (LinearMap.ker (bc GE h0 p0)).subtype)
      (δ₂ : ↥(LinearMap.ker (bc GE h1 p1)) →ₗ[RW W'] GK.obj W'.1)
      (_ : lam.appSections W' ∘ₗ δ₂ = ℓ₂ ∘ₗ (LinearMap.ker (bc GE h1 p1)).subtype),
      ∃ δ₁' δ₂' : ↥(LinearMap.ker P') →ₗ[RW W'] GK.obj W'.1,
        (∀ (s : ↥(LinearMap.ker (bc GE h0 p0))) (hs : Fin.append (s : Fin r0 → RW W') (0 : Fin r1 → RW W') ∈ LinearMap.ker P'),
          δ₁' ⟨Fin.append (s : Fin r0 → RW W') 0, hs⟩ = δ₁ s) ∧
        (∀ (s : ↥(LinearMap.ker (bc GE h1 p1))) (hs : Fin.append (0 : Fin r0 → RW W') (s : Fin r1 → RW W') ∈ LinearMap.ker P'),
          δ₂' ⟨Fin.append 0 (s : Fin r1 → RW W'), hs⟩ = δ₂ s) ∧
        Submodule.Quotient.mk δ₁' - Submodule.Quotient.mk δ₂' ∈
          JU q I W'.1 ^ e • (⊤ : Submodule (RW W') ((↥(LinearMap.ker P') →ₗ[RW W'] GK.obj W'.1) ⧸
            LinearMap.range (LinearMap.lcomp (RW W') (GK.obj W'.1) (LinearMap.ker P').subtype)))) :
    X.res h0 ((εX W0 r0 p0 hp0).symm (Submodule.Quotient.mk δ0))
      - X.res h1 ((εX W1 r1 p1 hp1).symm (Submodule.Quotient.mk δ1))
      ∈ JU q I W'.1 ^ e • (⊤ : Submodule (RW W') (X.obj W'.1)) := by
  have hs0 := bc_surjective GE hGEq h0 p0 hp0
  have hs1 := bc_surjective GE hGEq h1 p1 hp1
  have hP's : Function.Surjective P' := fun y => by
    obtain ⟨v, rfl⟩ := hs0 y
    exact ⟨Fin.append v 0, by rw [hP', map_zero, add_zero]⟩

  obtain ⟨δ0', h0a, h0b⟩ := transport GE GK Fm hGEq hGKq h0 p0 lam ℓ0 δ0 hδ0
  obtain ⟨δ1', h1a, h1b⟩ := transport GE GK Fm hGEq hGKq h1 p1 lam ℓ1 δ1 hδ1

  have hℓ0' : εm.appSections W' ∘ₗ bc Fm h0 ℓ0 = ψEm.appSections W' ∘ₗ bc GE h0 p0 := by
    rw [appSections_comp_bc, hℓ0, ← appSections_comp_bc]
  have hℓ1' : εm.appSections W' ∘ₗ bc Fm h1 ℓ1 = ψEm.appSections W' ∘ₗ bc GE h1 p1 := by
    rw [appSections_comp_bc, hℓ1, ← appSections_comp_bc]
  obtain ⟨δ0'', δ1'', h0'', h1'', hdiff⟩ := hov _ hℓ0' _ hℓ1' δ0' h0b δ1' h1b

  have A0 := hXf W0 W' h0 r0 p0 hp0 r0 (bc GE h0 p0) hs0 (gres h0 r0) (gres_smul h0 r0)
    (fun v => bc_apply_res GE h0 p0 v) δ0 δ0' (fun x => h0a x _)
  have A1 := hXf W1 W' h1 r1 p1 hp1 r1 (bc GE h1 p1) hs1 (gres h1 r1) (gres_smul h1 r1)
    (fun v => bc_apply_res GE h1 p1 v) δ1 δ1' (fun x => h1a x _)
  have B0 := hXf W' W' (le_refl W'.1) r0 (bc GE h0 p0) hs0 (r0 + r1) P' hP's (gleft (RW W') r0 r1)
    (fun a v => by rw [map_refl]; exact gleft_smul _ _ _ a v)
    (fun v => by
      show P' (Fin.append v 0) = GE.res (le_refl _) (bc GE h0 p0 v)
      rw [hP', map_zero, add_zero, GE.res_refl_apply])
    δ0' δ0'' (fun x => by rw [GK.res_refl_apply]; exact h0'' x _)
  have B1 := hXf W' W' (le_refl W'.1) r1 (bc GE h1 p1) hs1 (r0 + r1) P' hP's (gright (RW W') r0 r1)
    (fun a v => by rw [map_refl]; exact gright_smul _ _ _ a v)
    (fun w => by
      show P' (Fin.append 0 w) = GE.res (le_refl _) (bc GE h1 p1 w)
      rw [hP', map_zero, zero_add, GE.res_refl_apply])
    δ1' δ1'' (fun x => by rw [GK.res_refl_apply]; exact h1'' x _)
  rw [X.res_refl_apply] at B0 B1
  rw [A0, A1, B0, B1, ← map_sub]
  have hmem := Submodule.mem_map_of_mem (f := ((εX W' _ P' hP's).symm : _ →ₗ[RW W'] X.obj W'.1)) hdiff
  rw [Submodule.map_smul''] at hmem
  exact (smul_mono_right _ (le_top (a := Submodule.map _ ⊤))) hmem

end X1aRed

namespace X1aRed
variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

theorem d_zero_apply (X : OModulePresheaf q) (K : P.OrderedAffineCover) (c : X.cochain K 0) (s : K.Idx 1) :
    X.d K 0 c s = X.res (K.inter_le_inter_face s 0) (c (K.face s 0)) - X.res (K.inter_le_inter_face s 1) (c (K.face s 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, sub_eq_add_neg]

end X1aRed

end

set_option maxHeartbeats 8000000 in
open X1aRed in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))

    (X : OModulePresheaf q) (hXc : X.IsCoherent) (hXq : X.IsQuasicoherent)
    (εX : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (GK.obj W.1) (LinearMap.ker p).subtype))))
    (hXf : ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] GE.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = GE.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] GK.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = GK.res h (δ s)),
        X.res h ((εX W r p hp).symm (Submodule.Quotient.mk δ)) = (εX W' r' p' hp').symm (Submodule.Quotient.mk δ')) :
    ∃ (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
      (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
      (hpr : ∀ i : K.ι, Function.Surjective (pr i))
      (ℓ : ∀ (i : K.ι) (n : ℕ), (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] (F n).obj (K.U i))
      (δs : ∀ (i : K.ι) (n : ℕ), ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
      (t : ℕ → X.cochain K 0),

      (∀ (i : K.ι) (n : ℕ) (v : Fin (rk i) → Γ(P, K.U i)),
        (ε n).app ⟨K.U i, K.isAffineOpen i⟩ (ℓ i n v) = (ψE n).app ⟨K.U i, K.isAffineOpen i⟩ (pr i v)) ∧

      (∀ (i : K.ι) (n : ℕ) (v : Fin (rk i) → Γ(P, K.U i)),
        (φ n).app ⟨K.U i, K.isAffineOpen i⟩ (ℓ i (n + 1) v) = ℓ i n v) ∧

      (∀ (i : K.ι) (n : ℕ) (s : ↥(LinearMap.ker (pr i))),
        (lam n).app ⟨K.U i, K.isAffineOpen i⟩ (δs i n s) = ℓ i n (s : Fin (rk i) → Γ(P, K.U i))) ∧

      (∀ (i : K.ι) (n : ℕ),
        δs i (n + 1) - δs i n ∈
          (I.map (Scheme.TwoAffineOpenCover.algebraOfHom q (K.U i)).algebraMap) ^ (n + 1) •
            (⊤ : Submodule Γ(P, K.U i) (↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i)))) ∧

      (∀ (n : ℕ) (s : K.Idx 0),
        t n s = X.res (K.inter_le s 0)
          ((εX ⟨K.U (s.1 0), K.isAffineOpen (s.1 0)⟩ (rk (s.1 0)) (pr (s.1 0)) (hpr (s.1 0))).symm (Submodule.Quotient.mk (δs (s.1 0) n)))) ∧

      (∀ n : ℕ, X.d K 0 (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (X.cochain K 1))) ∧

      (∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (X.cochain K 0))) := by
  classical

  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  let K : P.OrderedAffineCover := (AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace_univ P).some

  have hpres := fun i : K.ι => exists_pres GE hGEc (Uc K i)
  choose rk pr hpr using hpres

  have hloc := fun i : K.ι =>
    chart_local I F φ hφs hφk E τ hτk ε hεs hεc GE ψE hψEc GK hGKc lam hlamc hlamr hlami (Uc K i) (pr i)
  choose ℓ δL hla hlb hlc hld hcd using hloc

  have hov := fun s : K.Idx 1 => by
    haveI : IsNoetherianRing Γ(P, K.inter s) := noeth (K.affineInter q s)
    haveI : Module.Finite Γ(P, K.inter s) (GK.obj (K.inter s)) := hGKc (K.affineInter q s)
    exact LinearMap.exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top
      (JU q I (K.inter s)) (GE := GE.obj (K.inter s)) (GK := GK.obj (K.inter s))
      (fun k => (F k).obj (K.inter s)) (fun k => (E k).obj (K.inter s))
      (fun k => (ε k).appSections (K.affineInter q s)) (fun k => (ψE k).appSections (K.affineInter q s))
      (fun k => (lam k).appSections (K.affineInter q s))
      (fun k => range_appSections_eq_ker (K.affineInter q s) (lam k) (ε k) (hlamr k (K.affineInter q s)))
      ((hlami (K.affineInter q s)).imp fun c hc k => ker_appSections_le (K.affineInter q s) I (lam (k + c)) (k + 1) (hc k))
      (bc GE (hleD q K s 0) (pr _)) (bc_surjective GE hGEq (hleD q K s 0) (pr _) (hpr _))
      (bc GE (hleD q K s 1) (pr _)) (bc_surjective GE hGEq (hleD q K s 1) (pr _) (hpr _))
      (PsD GE K rk pr s) (PsD_append GE K rk pr s)
  choose cO hcO using hov
  have hCex : ∃ C : ℕ, ∀ s, cO s ≤ C :=
    ⟨∑ s, cO s, fun s => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)⟩
  choose C hC using hCex

  have aux : ∀ (s : K.Idx 1) (n' : ℕ),
      X.res (hleD q K s 0) ((εX (Uc K (idx K s 0)) _ (pr _) (hpr _)).symm (Submodule.Quotient.mk (δL (idx K s 0) (n' + cO s))))
        - X.res (hleD q K s 1) ((εX (Uc K (idx K s 1)) _ (pr _) (hpr _)).symm (Submodule.Quotient.mk (δL (idx K s 1) (n' + cO s))))
      ∈ JU q I (K.inter s) ^ (n' + 1) • (⊤ : Submodule (RW (K.affineInter q s)) (X.obj (K.inter s))) :=
    fun s n' => overlap_aux I GE GK X hGEq hGKq εX hXf (F (n' + cO s)) (E (n' + cO s)) (lam _) (ε _) (ψE _)
      (hleD q K s 0) (hleD q K s 1) (pr _) (hpr _) (pr _) (hpr _) (ℓ _ _) (hla _ _) (ℓ _ _) (hla _ _)
      (δL (idx K s 0) (n' + cO s)) (hlc _ _) (δL (idx K s 1) (n' + cO s)) (hlc _ _)
      (PsD GE K rk pr s) (PsD_append GE K rk pr s) (n' + 1) (hcO s n')

  refine ⟨K, rk, pr, hpr, ℓ, fun i n => δL i (n + C),
    fun n s => X.res (K.inter_le s 0)
      ((εX ⟨K.U (s.1 0), K.isAffineOpen (s.1 0)⟩ (rk (s.1 0)) (pr (s.1 0)) (hpr (s.1 0))).symm
        (Submodule.Quotient.mk (δL (s.1 0) (n + C)))),
    ?_, ?_, ?_, ?_, fun n s => rfl, ?_, ?_⟩
  · exact fun i n v => LinearMap.congr_fun (hla i n) v
  · exact fun i n v => LinearMap.congr_fun (hlb i n) v
  · exact fun i n s => LinearMap.congr_fun (hcd i C n) s
  · intro i n
    show δL i (n + 1 + C) - δL i (n + C) ∈ _
    rw [show n + 1 + C = n + C + 1 by omega]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (I := JU q I (K.U i)) (show n + 1 ≤ n + C + 1 by omega))
      (hld i (n + C))
  ·
    intro n
    beta_reduce
    refine pi_mem_smul_top (I ^ (n + 1)) _ _ fun s => ?_
    rw [d_zero_apply, X.res_res, X.res_res, ← mem_bridge I X (K.inter s)]
    have key := aux s (n + (C - cO s))
    rw [show n + (C - cO s) + cO s = n + C by have := hC s; omega] at key
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) key
  ·
    intro n
    beta_reduce
    refine pi_mem_smul_top (I ^ (n + 1)) _ _ fun s => ?_
    change X.res (K.inter_le s 0) ((εX ⟨K.U (s.1 0), K.isAffineOpen (s.1 0)⟩ (rk (s.1 0)) (pr (s.1 0)) (hpr (s.1 0))).symm
          (Submodule.Quotient.mk (δL (s.1 0) (n + 1 + C))))
        - X.res (K.inter_le s 0) ((εX ⟨K.U (s.1 0), K.isAffineOpen (s.1 0)⟩ (rk (s.1 0)) (pr (s.1 0)) (hpr (s.1 0))).symm
          (Submodule.Quotient.mk (δL (s.1 0) (n + C)))) ∈ _
    rw [show n + 1 + C = n + C + 1 by omega, ← map_sub, ← map_sub, ← Submodule.Quotient.mk_sub]
    have hd' := Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (I := JU q I (K.U (s.1 0))) (show n + 1 ≤ n + C + 1 by omega)) (hld (s.1 0) (n + C))
    have h1 := Submodule.mem_map_of_mem
      (f := (LinearMap.range (LinearMap.lcomp Γ(P, K.U (s.1 0)) (GK.obj (K.U (s.1 0))) (LinearMap.ker (pr (s.1 0))).subtype)).mkQ) hd'
    rw [Submodule.map_smul''] at h1
    have h2 := (smul_mono_right _ (le_top (a := Submodule.map _ ⊤))) h1
    have h3 := Submodule.mem_map_of_mem
      (f := ((εX ⟨K.U (s.1 0), K.isAffineOpen (s.1 0)⟩ (rk (s.1 0)) (pr (s.1 0)) (hpr (s.1 0))).symm :
        _ →ₗ[Γ(P, K.U (s.1 0))] X.obj (K.U (s.1 0)))) h2
    rw [Submodule.map_smul''] at h3
    have h4 := (smul_mono_right _ (le_top (a := Submodule.map _ ⊤))) h3
    rw [Submodule.mkQ_apply, LinearEquiv.coe_coe, mem_bridge I X (K.U (s.1 0))] at h4
    have h5 := Submodule.mem_map_of_mem (f := X.res (K.inter_le s 0)) h4
    rw [Submodule.map_smul''] at h5
    exact (smul_mono_right _ (le_top (a := Submodule.map _ ⊤))) h5

end S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete (solution)
