-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedProjectiveLines.isNodeUnitModule_one_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/459b3a8c-7fa3-5f1c-a27e-3fdb2df62efc

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines Opposite TopologicalSpace TensorProduct

noncomputable section

namespace TwoGluedLinesC1
namespace ConductorFlat

variable {A : Type u} [CommRing A] {R : Type v} [CommRing R] [Algebra A R]

lemma tmul_one_mk_eq_zero_iff (I : Ideal A) (r : R) :
    r ⊗ₜ[A] (Ideal.Quotient.mk I 1) = (0 : R ⊗[A] (A ⧸ I)) ↔ r ∈ I.map (algebraMap A R) := by
  rw [← (TensorProduct.tensorQuotEquivQuotSMul R I).map_eq_zero_iff,
    TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul, Submodule.Quotient.mk_eq_zero,
    Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]

theorem map_inf_of_flat [Module.Flat A R] (I₁ I₂ : Ideal A) :
    (I₁ ⊓ I₂).map (algebraMap A R) = I₁.map (algebraMap A R) ⊓ I₂.map (algebraMap A R) := by
  refine le_antisymm (Ideal.map_inf_le _) ?_
  intro r hr
  obtain ⟨h₁, h₂⟩ := hr

  let φ : (A ⧸ (I₁ ⊓ I₂)) →ₗ[A] (A ⧸ I₁) × (A ⧸ I₂) :=
    (I₁ ⊓ I₂).liftQ ((Submodule.mkQ I₁).prod (Submodule.mkQ I₂)) (by
      intro a ha
      change (Submodule.Quotient.mk a, Submodule.Quotient.mk a) = ((0, 0) : (A ⧸ I₁) × (A ⧸ I₂))
      rw [Prod.mk.injEq, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
      exact ha)
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have : (Submodule.Quotient.mk a, Submodule.Quotient.mk a) = ((0, 0) : (A ⧸ I₁) × (A ⧸ I₂)) := hz
    simp only [Prod.mk.injEq, Submodule.Quotient.mk_eq_zero] at this
    exact (Submodule.Quotient.mk_eq_zero _).mpr this

  have hφR : Function.Injective (φ.lTensor R) := Module.Flat.lTensor_preserves_injective_linearMap φ hφ

  have key : φ.lTensor R (r ⊗ₜ[A] Ideal.Quotient.mk (I₁ ⊓ I₂) 1) = 0 := by
    rw [LinearMap.lTensor_tmul]
    apply (TensorProduct.prodRight A A R (A ⧸ I₁) (A ⧸ I₂)).injective
    rw [LinearEquiv.map_zero, TensorProduct.prodRight_tmul]
    change (r ⊗ₜ[A] Ideal.Quotient.mk I₁ 1, r ⊗ₜ[A] Ideal.Quotient.mk I₂ 1) = (0, 0)
    rw [(tmul_one_mk_eq_zero_iff I₁ r).mpr h₁, (tmul_one_mk_eq_zero_iff I₂ r).mpr h₂]
  have hz : r ⊗ₜ[A] Ideal.Quotient.mk (I₁ ⊓ I₂) 1 = 0 := hφR (by rw [key, map_zero])
  exact (tmul_one_mk_eq_zero_iff (I₁ ⊓ I₂) r).mp hz

theorem map_iInf_of_flat [Module.Flat A R] {ι : Type*} [Finite ι] (𝔪 : ι → Ideal A) :
    (⨅ i, 𝔪 i).map (algebraMap A R) = ⨅ i, (𝔪 i).map (algebraMap A R) := by
  classical
  haveI := Fintype.ofFinite ι

  suffices h : ∀ s : Finset ι, (s.inf 𝔪).map (algebraMap A R) = s.inf fun i => (𝔪 i).map (algebraMap A R) by
    have := h Finset.univ
    simpa [Finset.inf_univ_eq_iInf] using this
  intro s
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert i s hi ih => rw [Finset.inf_insert, Finset.inf_insert, map_inf_of_flat, ih]

end TwoGluedLinesC1.ConductorFlat

namespace TwoGluedLinesC1
namespace LocalToGlobal

variable {Y : Scheme.{u}} {M P₁ P₂ : Y.Modules} (j₁ : M ⟶ P₁) (j₂ : M ⟶ P₂)

def pair (W : Y.Opens) (m : Γ(M, W)) : Γ(P₁, W) × Γ(P₂, W) := (j₁.app W m, j₂.app W m)

omit j₁ j₂ in

def resPair {W W' : Y.Opens} (h : W' ≤ W) (p : Γ(P₁, W) × Γ(P₂, W)) : Γ(P₁, W') × Γ(P₂, W') :=
  (P₁.presheaf.map (homOfLE h).op p.1, P₂.presheaf.map (homOfLE h).op p.2)

omit j₁ j₂ in
lemma resPair_resPair {W W' W'' : Y.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (p : Γ(P₁, W) × Γ(P₂, W)) :
    resPair h' (resPair h p) = resPair (h'.trans h) p := by
  simp only [resPair, Prod.mk.injEq]
  constructor <;>
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

lemma app_map {N N' : Y.Modules} (φ : N ⟶ N') {W W' : Y.Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h n

lemma pair_map {W W' : Y.Opens} (h : W' ≤ W) (m : Γ(M, W)) :
    pair j₁ j₂ W' (M.presheaf.map (homOfLE h).op m) = resPair h (pair j₁ j₂ W m) := by
  simp only [pair, resPair, app_map]

structure IsLocalFamily (S : ∀ W : Y.Opens, Set (Γ(P₁, W) × Γ(P₂, W))) : Prop where
  res : ∀ {W W' : Y.Opens} (h : W' ≤ W) (p : Γ(P₁, W) × Γ(P₂, W)), p ∈ S W → resPair h p ∈ S W'
  glue : ∀ {W : Y.Opens} (𝒲 : Set Y.Opens) (hle : ∀ W' ∈ 𝒲, W' ≤ W) (_ : W ≤ sSup 𝒲)
    (p : Γ(P₁, W) × Γ(P₂, W)), (∀ W' (hW' : W' ∈ 𝒲), resPair (hle W' hW') p ∈ S W') → p ∈ S W

variable {j₁ j₂}

section

variable (B : Set Y.Opens) (hB : ∀ (W : Y.Opens) (y : Y), y ∈ W → ∃ W' ∈ B, y ∈ W' ∧ W' ≤ W)

def inside (W : Y.Opens) : Set Y.Opens := {W' | W' ∈ B ∧ W' ≤ W}

omit hB in
lemma inside_le {W W' : Y.Opens} (h : W' ∈ inside B W) : W' ≤ W := h.2

include hB in
lemma le_sSup_inside (W : Y.Opens) : W ≤ sSup (inside B W) := by
  intro y hy
  obtain ⟨W', hW'B, hyW', hW'W⟩ := hB W y hy
  exact Opens.mem_sSup.mpr ⟨W', ⟨hW'B, hW'W⟩, hyW'⟩

include hB in
lemma le_iSup_inside (W : Y.Opens) : W ≤ ⨆ k : inside B W, (k : Y.Opens) := by
  rw [← sSup_eq_iSup']
  exact le_sSup_inside B hB W

include hB

theorem injective_pair_of_basis
    (hloc : ∀ W ∈ B, Function.Injective (pair j₁ j₂ W)) (W : Y.Opens) :
    Function.Injective (pair j₁ j₂ W) := by
  intro m m' hmm'
  let F : TopCat.Sheaf Ab Y := ⟨M.presheaf, M.isSheaf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun k : inside B W => (k : Y.Opens)) W
    (fun k => homOfLE (inside_le B k.2)) (le_iSup_inside B hB W) m m' fun k => ?_
  apply hloc k.1 k.2.1
  change pair j₁ j₂ k.1 (M.presheaf.map (homOfLE (inside_le B k.2)).op m) =
    pair j₁ j₂ k.1 (M.presheaf.map (homOfLE (inside_le B k.2)).op m')
  rw [pair_map, pair_map, hmm']

theorem range_pair_eq_of_basis (S : ∀ W : Y.Opens, Set (Γ(P₁, W) × Γ(P₂, W))) (hS : IsLocalFamily S)
    (hloc : ∀ W ∈ B, Function.Injective (pair j₁ j₂ W) ∧ Set.range (pair j₁ j₂ W) = S W) (W : Y.Opens) :
    Set.range (pair j₁ j₂ W) = S W := by
  have hinj : ∀ W', Function.Injective (pair j₁ j₂ W') :=
    injective_pair_of_basis B hB fun W hW => (hloc W hW).1
  apply le_antisymm
  ·
    rintro _ ⟨m, rfl⟩
    refine hS.glue (inside B W) (fun W' h => inside_le B h) (le_sSup_inside B hB W) _ fun W' hW' => ?_
    rw [← pair_map, ← (hloc W' hW'.1).2]
    exact ⟨_, rfl⟩
  ·
    intro p hp
    have hk : ∀ k : inside B W, ∃ m : Γ(M, k.1), pair j₁ j₂ k.1 m = resPair (inside_le B k.2) p := by
      intro k
      have : resPair (inside_le B k.2) p ∈ Set.range (pair j₁ j₂ k.1) := by
        rw [(hloc k.1 k.2.1).2]; exact hS.res _ p hp
      exact this
    choose mk hmk using hk
    let F : TopCat.Sheaf Ab Y := ⟨M.presheaf, M.isSheaf⟩
    have hcompat : TopCat.Presheaf.IsCompatible F.1 (fun k : inside B W => (k : Y.Opens)) mk := by
      intro k l
      apply hinj
      change pair j₁ j₂ _ (M.presheaf.map (homOfLE inf_le_left).op (mk k)) =
        pair j₁ j₂ _ (M.presheaf.map (homOfLE inf_le_right).op (mk l))
      rw [pair_map, pair_map, hmk, hmk, resPair_resPair, resPair_resPair]
    obtain ⟨m, hm, -⟩ := TopCat.Sheaf.existsUnique_gluing' F (fun k : inside B W => (k : Y.Opens)) W
      (fun k => homOfLE (inside_le B k.2)) (le_iSup_inside B hB W) mk hcompat
    refine ⟨m, ?_⟩

    have hloc_eq : ∀ k : inside B W, resPair (inside_le B k.2) (pair j₁ j₂ W m) = resPair (inside_le B k.2) p := by
      intro k
      rw [← pair_map, ← hmk k]
      exact congrArg _ (hm k)
    ext
    · let G : TopCat.Sheaf Ab Y := ⟨P₁.presheaf, P₁.isSheaf⟩
      exact TopCat.Sheaf.eq_of_locally_eq' G (fun k : inside B W => (k : Y.Opens)) W
        (fun k => homOfLE (inside_le B k.2)) (le_iSup_inside B hB W) _ _
        fun k => congrArg Prod.fst (hloc_eq k)
    · let G : TopCat.Sheaf Ab Y := ⟨P₂.presheaf, P₂.isSheaf⟩
      exact TopCat.Sheaf.eq_of_locally_eq' G (fun k : inside B W => (k : Y.Opens)) W
        (fun k => homOfLE (inside_le B k.2)) (le_iSup_inside B hB W) _ _
        fun k => congrArg Prod.snd (hloc_eq k)

theorem injective_and_range_eq_of_basis (S : ∀ W : Y.Opens, Set (Γ(P₁, W) × Γ(P₂, W)))
    (hS : IsLocalFamily S)
    (hloc : ∀ W ∈ B, Function.Injective (pair j₁ j₂ W) ∧ Set.range (pair j₁ j₂ W) = S W) (W : Y.Opens) :
    Function.Injective (pair j₁ j₂ W) ∧ Set.range (pair j₁ j₂ W) = S W :=
  ⟨injective_pair_of_basis B hB (fun W hW => (hloc W hW).1) W, range_pair_eq_of_basis B hB S hS hloc W⟩

end

end TwoGluedLinesC1.LocalToGlobal

namespace TwoGluedLinesC1
namespace NodeLocal

variable {κ : Type u} [Field κ] [IsAlgClosed κ]
  {X : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
  {M₁ M₂ : CurveModel κ (RatFunc κ)} {i₁ : M₁.C ⟶ X} {i₂ : M₂.C ⟶ X}
  {hi₁ : i₁ ≫ x = M₁.toBase} {hi₂ : i₂ ≫ x = M₂.toBase}
  {s : ℕ} {a b : Fin s → κˣ}
  {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} (u : Fin s → Γ(T, ⊤)ˣ)

local notation "XT" => pullback x h
local notation "i₁T" => curveChange i₁ hi₁ h
local notation "i₂T" => curveChange i₂ hi₂ h
local notation "σ¹" => nodeSectionFst M₁ a h
local notation "σ²" => nodeSectionSnd M₂ b h
local notation "nl" => nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h

omit [IsAlgClosed κ] in
lemma preimage_mono {Y Z : Scheme.{u}} (f : Y ⟶ Z) {W W' : Z.Opens} (hW : W' ≤ W) : f ⁻¹ᵁ W' ≤ f ⁻¹ᵁ W :=
  fun _ hy => hW hy

lemma nodeLocus_mono (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W) : nl i W' ≤ nl i W :=
  inf_le_inf (preimage_mono _ (preimage_mono _ hW)) (preimage_mono _ (preimage_mono _ hW))

lemma appLE_fst_res (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W)
    (f : Γ(pullback M₁.toBase h, (i₁T) ⁻¹ᵁ W)) :
    (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W') (nl i W') inf_le_left
        ((pullback M₁.toBase h).presheaf.map (homOfLE (preimage_mono (i₁T) hW)).op f) =
      T.presheaf.map (homOfLE (nodeLocus_mono i hW)).op
        ((σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left f) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

lemma appLE_snd_res (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W)
    (g : Γ(pullback M₂.toBase h, (i₂T) ⁻¹ᵁ W)) :
    (σ² i).appLE ((i₂T) ⁻¹ᵁ W') (nl i W') inf_le_right
        ((pullback M₂.toBase h).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op g) =
      T.presheaf.map (homOfLE (nodeLocus_mono i hW)).op
        ((σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right g) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

omit [IsAlgClosed κ] in
lemma unit_res {V V' : T.Opens} (hV : V' ≤ V) (i : Fin s) :
    T.presheaf.map (homOfLE hV).op (T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (u i : Γ(T, ⊤))) =
      T.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (u i : Γ(T, ⊤)) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

theorem nodeCondition_res (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W)
    (f : Γ(pullback M₁.toBase h, (i₁T) ⁻¹ᵁ W)) (g : Γ(pullback M₂.toBase h, (i₂T) ⁻¹ᵁ W))
    (hfg : NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i f g) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W' i
      ((pullback M₁.toBase h).presheaf.map (homOfLE (preimage_mono (i₁T) hW)).op f)
      ((pullback M₂.toBase h).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op g) := by
  unfold NodeCondition at hfg ⊢
  rw [appLE_fst_res i hW f, appLE_snd_res i hW g, hfg, map_mul, unit_res]

lemma nodeLocus_eq (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h = nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h)
    (i : Fin s) (W : (XT).Opens) : nl i W = ((σ¹ i) ≫ (i₁T)) ⁻¹ᵁ W := by
  change (σ¹ i) ⁻¹ᵁ ((i₁T) ⁻¹ᵁ W) ⊓ (σ² i) ⁻¹ᵁ ((i₂T) ⁻¹ᵁ W) = _
  have h1 : (σ¹ i) ⁻¹ᵁ ((i₁T) ⁻¹ᵁ W) = ((σ¹ i) ≫ (i₁T)) ⁻¹ᵁ W := rfl
  have h2 : (σ² i) ⁻¹ᵁ ((i₂T) ⁻¹ᵁ W) = ((σ² i) ≫ (i₂T)) ⁻¹ᵁ W := rfl
  rw [h1, h2, ← hν i, inf_idem]

lemma nodeLocus_le_iSup (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h = nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h)
    (i : Fin s) {W : (XT).Opens} (𝒲 : Set (XT).Opens) (hcov : W ≤ sSup 𝒲) :
    nl i W ≤ ⨆ k : 𝒲, nl i (k : (XT).Opens) := by
  intro t ht
  rw [nodeLocus_eq hν] at ht
  have : ((σ¹ i) ≫ (i₁T)).base t ∈ sSup 𝒲 := hcov ht
  obtain ⟨W', hW', ht'⟩ := Opens.mem_sSup.mp this
  refine Opens.mem_iSup.mpr ⟨⟨W', hW'⟩, ?_⟩
  rw [nodeLocus_eq hν]
  exact ht'

theorem nodeCondition_glue (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h = nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h)
    (i : Fin s) {W : (XT).Opens} (𝒲 : Set (XT).Opens) (hle : ∀ W' ∈ 𝒲, W' ≤ W)
    (hcov : W ≤ sSup 𝒲)
    (f : Γ(pullback M₁.toBase h, (i₁T) ⁻¹ᵁ W)) (g : Γ(pullback M₂.toBase h, (i₂T) ⁻¹ᵁ W))
    (hloc : ∀ W' (hW' : W' ∈ 𝒲), NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W' i
      ((pullback M₁.toBase h).presheaf.map (homOfLE (preimage_mono (i₁T) (hle W' hW'))).op f)
      ((pullback M₂.toBase h).presheaf.map (homOfLE (preimage_mono (i₂T) (hle W' hW'))).op g)) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i f g := by
  unfold NodeCondition at hloc ⊢
  refine TopCat.Sheaf.eq_of_locally_eq' T.sheaf (fun k : 𝒲 => nl i (k : (XT).Opens)) (nl i W)
    (fun k => homOfLE (nodeLocus_mono i (hle k.1 k.2))) (nodeLocus_le_iSup hν i 𝒲 hcov) _ _ fun k => ?_
  have := hloc k.1 k.2
  rw [appLE_fst_res i (hle k.1 k.2) f, appLE_snd_res i (hle k.1 k.2) g] at this
  change T.presheaf.map _ _ = T.presheaf.map _ _
  rw [this, map_mul, unit_res u]

end TwoGluedLinesC1.NodeLocal

namespace TwoGluedLinesC1
namespace NodeLocal

theorem nodeSectionFst_comp_eq_nodeSectionSnd_comp
    {κ : Type u} [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    {s : ℕ} (a b : Fin s → κˣ)
    (hpts : ∀ i, (pointAt M₁ (a i : κ)).1 ≫ i₁ = (pointAt M₂ (b i : κ)).1 ≫ i₂)
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (i : Fin s) :
    nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h = nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h := by
  let ν : SchemeHomOver (𝟙 (Spec (.of κ))) x :=
    ⟨(pointAt M₁ (a i : κ)).1 ≫ i₁, by rw [Category.assoc, hi₁, (pointAt M₁ (a i : κ)).2]⟩
  have h1 : nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h = rigSection x h ν :=
    rigSection_curveChange i₁ hi₁ (ε' := pointAt M₁ (a i : κ)) (ε := ν) rfl h
  have h2 : nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h = rigSection x h ν :=
    rigSection_curveChange i₂ hi₂ (ε' := pointAt M₂ (b i : κ)) (ε := ν) (hpts i).symm h
  rw [h1, h2]

end TwoGluedLinesC1.NodeLocal

namespace TwoGluedLinesC1
namespace BaseChange

theorem ker_includeRight_eq {A B R : Type u} [CommRing A] [CommRing B] [CommRing R] [Algebra A B]
    [Algebra A R] (hB : Function.Surjective (algebraMap A B)) :
    RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := R)).toRingHom =
      (RingHom.ker (algebraMap A B)).map (algebraMap A R) := by
  set I := RingHom.ker (algebraMap A B) with hI

  let e : (A ⧸ I) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hB

  let Φ : B ⊗[A] R →ₐ[A] (R ⧸ I.map (algebraMap A R)) :=
    (((Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).restrictScalars A).symm.toAlgHom).comp
      (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).toAlgHom
  have hΦinj : Function.Injective Φ := by
    change Function.Injective (((Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).restrictScalars
      A).symm ∘ (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl (R := A) (A₁ := R))))
    exact (AlgEquiv.injective _).comp (AlgEquiv.injective _)
  have hΦ : ∀ r : R, Φ (Algebra.TensorProduct.includeRight r) = Ideal.Quotient.mk _ r := by
    intro r
    change ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).restrictScalars A).symm
      (Algebra.TensorProduct.congr e.symm AlgEquiv.refl ((1 : B) ⊗ₜ[A] r)) = _
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    change ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).restrictScalars A).symm
      ((1 : A ⧸ I) ⊗ₜ[A] r) = _
    rw [AlgEquiv.symm_apply_eq]
    rfl
  ext r
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← hΦ, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, map_eq_zero_iff Φ hΦinj]

theorem surjective_and_ker_app_eq {Y X T S : Scheme.{u}} {g : Y ⟶ X} {iY : Y ⟶ T} {iX : X ⟶ S}
    {f : T ⟶ S} (H : IsPullback g iY iX f) [IsClosedImmersion iX]
    {US : S.Opens} (hUS : IsAffineOpen US) {UT : T.Opens} (hUT : IsAffineOpen UT)
    (hUST : UT ≤ f ⁻¹ᵁ US) :
    Function.Surjective (iY.app UT) ∧
      RingHom.ker (iY.app UT).hom = (RingHom.ker (iX.app US).hom).map (f.appLE US UT hUST).hom := by
  haveI : IsClosedImmersion iY := MorphismProperty.of_isPullback H inferInstance
  refine ⟨iY.app_surjective UT hUT, ?_⟩
  have hUSX : iX ⁻¹ᵁ US ≤ iX ⁻¹ᵁ US := le_rfl
  have hUY : iY ⁻¹ᵁ UT = g ⁻¹ᵁ (iX ⁻¹ᵁ US) ⊓ iY ⁻¹ᵁ UT := by
    refine le_antisymm (le_inf ?_ le_rfl) inf_le_right
    change iY ⁻¹ᵁ UT ≤ (g ≫ iX) ⁻¹ᵁ US
    rw [H.w]
    exact fun y hy => hUST hy
  have hUX : IsAffineOpen (iX ⁻¹ᵁ US) := hUS.preimage iX
  have hiso := isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX
  have HP := (isIso_pushoutSection_iff H hUST hUSX hUY).mp hiso

  set A := Γ(S, US)
  set B := Γ(X, iX ⁻¹ᵁ US)
  set R := Γ(T, UT)
  set φX := iX.appLE US (iX ⁻¹ᵁ US) hUSX with hφX
  set φ := f.appLE US UT hUST with hφ
  algebraize [φX.hom, φ.hom]
  let e := ((CommRingCat.isPushout_tensorProduct A B R).isoIsPushout _ _ HP)
  have he : (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := R)).toRingHom)
      ≫ e.hom = iY.appLE UT (iY ⁻¹ᵁ UT) (by rw [hUY]) :=
    (CommRingCat.isPushout_tensorProduct A B R).inr_isoIsPushout_hom _ _ HP
  have happ : iY.app UT = iY.appLE UT (iY ⁻¹ᵁ UT) le_rfl := iY.app_eq_appLE
  rw [happ, ← he]
  have hB : Function.Surjective (algebraMap A B) := by
    change Function.Surjective φX
    rw [hφX, ← Scheme.Hom.app_eq_appLE]
    exact iX.app_surjective US hUS
  have hker : RingHom.ker (iX.app US).hom = RingHom.ker (algebraMap A B) := by
    change RingHom.ker (iX.app US).hom = RingHom.ker φX.hom
    rw [hφX, ← Scheme.Hom.app_eq_appLE]
  rw [hker, CommRingCat.hom_comp, RingHom.ker_comp_of_injective, CommRingCat.hom_ofHom,
    ker_includeRight_eq hB]
  · rfl
  · exact (ConcreteCategory.bijective_of_isIso e.hom).1

end TwoGluedLinesC1.BaseChange

namespace TwoGluedLinesC1
namespace Conductor

theorem ker_eq_vanishingIdeal_closure_range {T Y : Scheme.{u}} [IsReduced T] (f : T ⟶ Y) :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range f.base)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot (X := T),
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  simp only [Closeds.coe_closure, Closeds.coe_top, Set.image_univ]

theorem ker_le_ker_of_range_subset {T Z Y : Scheme.{u}} [IsReduced T] (i : Z ⟶ Y) [IsClosedImmersion i]
    (f : T ⟶ Y) (hf : Set.range f.base ⊆ Set.range i.base) : i.ker ≤ f.ker := by
  rw [ker_eq_vanishingIdeal_closure_range f]
  refine le_trans ?_ (Scheme.IdealSheafData.vanishingIdeal_antimono
    (T := ⟨Set.range i.base, i.isClosedEmbedding.isClosed_range⟩) ?_)
  · rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    exact i.range_subset_ker_support
  · change closure (Set.range f.base) ⊆ Set.range i.base
    exact closure_minimal hf i.isClosedEmbedding.isClosed_range

theorem pointAt_comp_eq_pointAt_comp'
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X) [IsClosedImmersion i₁]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase) (c d : κ)
    (h : i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ c)).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ d)).1) :
    (pointAt M₁ c).1 ≫ i₁ = (pointAt M₂ d).1 ≫ i₂ := by
  set pα := pointAt M₁ c with hpα
  set pβ := pointAt M₂ d with hpβ
  have hαpt : pα.1.base (IsLocalRing.closedPoint κ) =
      (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ c)).1 := by
    change ((pointEquivClosedPoint M₁.toBase) pα).1 = _
    rw [hpα, pointAt, CurveModel.pointEquivPlace, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  have hβpt : pβ.1.base (IsLocalRing.closedPoint κ) =
      (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ d)).1 := by
    change ((pointEquivClosedPoint M₂.toBase) pβ).1 = _
    rw [hpβ, pointAt, CurveModel.pointEquivPlace, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  let g : Spec (.of κ) ⟶ X := pβ.1 ≫ i₂
  have hg_range : Set.range g.base ⊆ Set.range i₁.base := by
    rintro _ ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
    refine ⟨(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ c)).1, ?_⟩
    change _ = i₂.base (pβ.1.base (IsLocalRing.closedPoint κ))
    rw [hβpt, h]
  let q : Spec (.of κ) ⟶ M₁.C := IsClosedImmersion.lift i₁ g (ker_le_ker_of_range_subset i₁ g hg_range)
  have hq : q ≫ i₁ = g := IsClosedImmersion.lift_fac _ _ _
  have hq_base : q ≫ M₁.toBase = 𝟙 _ := by
    rw [← hi₁, ← Category.assoc, hq]
    change (pβ.1 ≫ i₂) ≫ x = 𝟙 _
    rw [Category.assoc, hi₂, pβ.2]
  have hq_pt : q.base (IsLocalRing.closedPoint κ) = pα.1.base (IsLocalRing.closedPoint κ) := by
    apply i₁.isClosedEmbedding.injective
    change (q ≫ i₁).base _ = _
    rw [hq, hαpt, h]
    change i₂.base (pβ.1.base (IsLocalRing.closedPoint κ)) = _
    rw [hβpt]
  have hqα : q = pα.1 := ext_of_apply_closedPoint_eq M₁.toBase hq_base pα.2 hq_pt
  rw [← hqα, hq]

section Setting

variable {κ : Type u} [Field κ] [IsAlgClosed κ]
  {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
  (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
  {s : ℕ} (a b : Fin s → κˣ)

noncomputable def nodePt (i : Fin s) : Spec (.of κ) ⟶ X := (pointAt M₁ (a i : κ)).1 ≫ i₁

theorem pointAt_base_closedPoint (M : CurveModel κ (RatFunc κ)) (c : κ) :
    (pointAt M c).1.base (IsLocalRing.closedPoint κ) =
      (M.placeEquiv.symm (RationalFunctionField.placeOfPoint κ c)).1 := by
  change ((pointEquivClosedPoint M.toBase) (pointAt M c)).1 = _
  rw [pointAt, CurveModel.pointEquivPlace, Equiv.symm_trans_apply, Equiv.apply_symm_apply]

include hi₁ in
theorem nodePt_comp (i : Fin s) : nodePt M₁ i₁ a i ≫ x = 𝟙 _ := by
  rw [nodePt, Category.assoc, hi₁, (pointAt M₁ (a i : κ)).2]

include hi₁ in
theorem isClosedImmersion_nodePt (i : Fin s) : IsClosedImmersion (nodePt M₁ i₁ a i) :=
  isClosedImmersion_of_comp_eq_id x _ (nodePt_comp x M₁ i₁ hi₁ a i)

theorem nodePt_base_closedPoint (i : Fin s) :
    (nodePt M₁ i₁ a i).base (IsLocalRing.closedPoint κ) =
      i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1 := by
  change i₁.base ((pointAt M₁ (a i : κ)).1.base _) = _
  rw [pointAt_base_closedPoint]

theorem range_nodePt (i : Fin s) :
    Set.range (nodePt M₁ i₁ a i).base =
      {i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1} := by
  ext y
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
    exact nodePt_base_closedPoint M₁ i₁ a i
  · rintro rfl
    exact ⟨_, nodePt_base_closedPoint M₁ i₁ a i⟩

variable [IsClosedImmersion i₁] [IsClosedImmersion i₂]

omit [IsAlgClosed κ] in

theorem ker_inf_ker_eq_bot [IsReduced X] (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (V : X.affineOpens) :
    RingHom.ker (i₁.app V).hom ⊓ RingHom.ker (i₂.app V).hom = ⊥ := by
  have h : i₁.ker ⊓ i₂.ker = ⊥ := by
    rw [ker_eq_vanishingIdeal_closure_range i₁, ker_eq_vanishingIdeal_closure_range i₂,
      ← Scheme.IdealSheafData.vanishingIdeal_sup]
    have : Closeds.closure (Set.range i₁.base) ⊔ Closeds.closure (Set.range i₂.base) = (⊤ : Closeds X) := by
      apply top_le_iff.mp
      intro y _
      have hy : y ∈ Set.range i₁.base ∪ Set.range i₂.base := by rw [hcover]; trivial
      rcases hy with hy | hy
      · exact Or.inl (subset_closure hy)
      · exact Or.inr (subset_closure hy)
    rw [this, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
  have := congrArg (fun I : X.IdealSheafData => I.ideal V) h
  simpa only [Scheme.IdealSheafData.ideal_inf, Scheme.Hom.ker_apply, Pi.inf_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using this

include hi₁ hi₂ in

theorem ker_sup_ker_eq_iInf
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1
                = i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i : κ))).1)
    (hinter : ∀ p q, i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i))).1)
    (htrans : IsReduced (pullback i₁ i₂)) (V : X.affineOpens) :
    RingHom.ker (i₁.app V).hom ⊔ RingHom.ker (i₂.app V).hom =
      ⨅ i, RingHom.ker ((nodePt M₁ i₁ a i).app V).hom := by
  haveI := fun i => isClosedImmersion_nodePt x M₁ i₁ hi₁ a i
  apply le_antisymm
  ·
    refine le_iInf fun i => sup_le ?_ ?_
    · intro r hr
      simp only [RingHom.mem_ker] at hr ⊢
      rw [nodePt, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, hr, map_zero]
    · intro r hr
      simp only [RingHom.mem_ker] at hr ⊢
      have e : nodePt M₁ i₁ a i = (pointAt M₂ (b i : κ)).1 ≫ i₂ :=
        pointAt_comp_eq_pointAt_comp' κ x M₁ M₂ i₁ i₂ hi₁ hi₂
          (a i : κ) (b i : κ) (hnode i)
      rw [e, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, hr, map_zero]
  ·
    let g : pullback i₁ i₂ ⟶ X := pullback.fst i₁ i₂ ≫ i₁

    have hle : (⨅ i, (nodePt M₁ i₁ a i).ker) ≤ g.ker := by
      simp_rw [ker_eq_vanishingIdeal_closure_range]
      rw [← Scheme.IdealSheafData.vanishingIdeal_iSup]
      apply Scheme.IdealSheafData.vanishingIdeal_antimono
      change closure (Set.range g.base) ⊆ _
      refine closure_minimal ?_ (Closeds.isClosed _)
      rintro _ ⟨z, rfl⟩
      have hz : i₁.base ((pullback.fst i₁ i₂).base z) = i₂.base ((pullback.snd i₁ i₂).base z) := by
        have := congrArg (fun f : pullback i₁ i₂ ⟶ X => f.base z) (pullback.condition (f := i₁) (g := i₂))
        simpa using this
      obtain ⟨i, hp, -⟩ := hinter _ _ hz
      have : g.base z ∈ (Closeds.closure (Set.range (nodePt M₁ i₁ a i).base) : Set X) := by
        apply subset_closure
        rw [range_nodePt]
        change i₁.base ((pullback.fst i₁ i₂).base z) = _
        rw [hp]
      exact (le_iSup (fun i => Closeds.closure (Set.range (nodePt M₁ i₁ a i).base)) i) this
    have hleV := (Scheme.IdealSheafData.ideal_mono hle) V
    rw [Scheme.IdealSheafData.ideal_iInf] at hleV
    simp only [iInf_apply, Scheme.Hom.ker_apply] at hleV
    refine hleV.trans (le_of_eq ?_)

    have HP : IsPullback (pullback.snd i₁ i₂) (pullback.fst i₁ i₂) i₂ i₁ := (IsPullback.of_hasPullback i₁ i₂).flip
    obtain ⟨-, hk⟩ := TwoGluedLinesC1.BaseChange.surjective_and_ker_app_eq HP V.2 (V.2.preimage i₁)
      (le_refl (i₁ ⁻¹ᵁ (V : X.Opens)))
    change RingHom.ker ((pullback.fst i₁ i₂ ≫ i₁).app V).hom = _
    rw [Scheme.Hom.comp_app, CommRingCat.hom_comp, ← RingHom.comap_ker, hk, ← Scheme.Hom.app_eq_appLE,
      Ideal.comap_map_of_surjective _ (i₁.app_surjective V V.2), sup_comm]
    rfl

end Setting

end TwoGluedLinesC1.Conductor

namespace TwoGluedLinesC1
namespace Conductor

theorem injective_and_range_pair_eq {R S₁ S₂ : Type u} [CommRing R] [CommRing S₁] [CommRing S₂]
    {ι : Type*} {E : ι → Type u} [∀ i, CommRing (E i)]
    (q₁ : R →+* S₁) (q₂ : R →+* S₂) (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂)
    (e₁ : ∀ i, S₁ →+* E i) (e₂ : ∀ i, S₂ →+* E i) (he : ∀ i, (e₁ i).comp q₁ = (e₂ i).comp q₂)
    (hinf : RingHom.ker q₁ ⊓ RingHom.ker q₂ = ⊥)
    (hsup : RingHom.ker q₁ ⊔ RingHom.ker q₂ = ⨅ i, RingHom.ker ((e₁ i).comp q₁)) :
    Function.Injective (fun r => (q₁ r, q₂ r)) ∧
      Set.range (fun r => (q₁ r, q₂ r)) = {p | ∀ i, e₁ i p.1 = e₂ i p.2} := by
  constructor
  · intro r r' hrr'
    simp only [Prod.mk.injEq] at hrr'
    rw [← sub_eq_zero, ← Ideal.mem_bot, ← hinf]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, map_sub, hrr'.1, sub_self]
    · rw [RingHom.mem_ker, map_sub, hrr'.2, sub_self]
  · ext ⟨f, g⟩
    simp only [Set.mem_range, Prod.mk.injEq, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, rfl, rfl⟩ i
      exact congrArg (fun φ : R →+* E i => φ r) (he i)
    · intro hfg
      obtain ⟨r₁, rfl⟩ := hq₁ f
      obtain ⟨r₂, rfl⟩ := hq₂ g
      have hmem : r₁ - r₂ ∈ RingHom.ker q₁ ⊔ RingHom.ker q₂ := by
        rw [hsup, Ideal.mem_iInf]
        intro i
        rw [RingHom.mem_ker, map_sub, sub_eq_zero]
        change e₁ i (q₁ r₁) = ((e₁ i).comp q₁) r₂
        rw [he i]
        exact hfg i
      obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := Submodule.mem_sup.mp hmem
      refine ⟨r₁ - k₁, ?_, ?_⟩
      · rw [map_sub, RingHom.mem_ker.mp hk₁, sub_zero]
      · have : r₁ - k₁ = r₂ + k₂ := by linear_combination -hk
        rw [this, map_add, RingHom.mem_ker.mp hk₂, add_zero]

lemma appLE_eq_of_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (hfg : f = g) (U : Z.Opens) (V : Y.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (hfg ▸ e) := by
  subst hfg; rfl

lemma presheaf_map_injective_of_eq {Y : Scheme.{u}} {U U' : Y.Opens} (e : U = U') (hle : U ≤ U') :
    Function.Injective (Y.presheaf.map (homOfLE hle).op) := by
  subst e
  have : homOfLE hle = 𝟙 U := Subsingleton.elim _ _
  rw [this, op_id, Y.presheaf.map_id]
  exact fun a b hab => hab

lemma ker_hom_toAlgebra_flat {A R : Type u} [CommRing A] [CommRing R] (φ : A →+* R) (hφ : φ.Flat) :
    letI := φ.toAlgebra; Module.Flat A R := hφ

section OverT

variable {κ : Type u} [Field κ] [IsAlgClosed κ]
  {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
  (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
  {s : ℕ} (a b : Fin s → κˣ)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))

scoped instance flat_toSpecField : Flat h := inferInstance

omit [IsAlgClosed κ] in

theorem isPullback_curveChange {C : Scheme.{u}} {c : C ⟶ Spec (.of κ)} (f : C ⟶ X) (hf : f ≫ x = c) :
    IsPullback (pullback.fst c h) (curveChange f hf h) f (pullback.fst x h) := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd x h) (v₁₃ := h) (h₂₂ := x) ?_ ?_
    (IsPullback.of_hasPullback x h).flip).flip
  · rw [curveChange_snd, hf]
    exact (IsPullback.of_hasPullback c h).flip
  · simp only [curveChange, pullback.lift_fst]

noncomputable def nodeSec (i : Fin s) : T ⟶ pullback x h :=
  rigSection x h ⟨nodePt M₁ i₁ a i, nodePt_comp x M₁ i₁ hi₁ a i⟩

theorem isPullback_nodeSec (i : Fin s) :
    IsPullback h (nodeSec x M₁ i₁ hi₁ a h i) (nodePt M₁ i₁ a i) (pullback.fst x h) := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd x h) (v₁₃ := h) (h₂₂ := x) ?_ ?_
    (IsPullback.of_hasPullback x h).flip).flip
  · have h1 : nodeSec x M₁ i₁ hi₁ a h i ≫ pullback.snd x h = 𝟙 T := by
      simp only [nodeSec, rigSection, pullback.lift_snd]
    rw [h1, nodePt_comp x M₁ i₁ hi₁ a i]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · simp only [nodeSec, rigSection, pullback.lift_fst]

theorem nodeSectionFst_comp (i : Fin s) :
    nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h = nodeSec x M₁ i₁ hi₁ a h i :=
  rigSection_curveChange i₁ hi₁ (ε' := pointAt M₁ (a i : κ))
    (ε := ⟨nodePt M₁ i₁ a i, nodePt_comp x M₁ i₁ hi₁ a i⟩) rfl h

noncomputable def jFst : @Quiver.Hom (pullback x h).Modules _
    (SheafOfModules.unit (pullback x h).ringCatSheaf)
    ((Scheme.Modules.pushforward (curveChange i₁ hi₁ h)).obj
      (SheafOfModules.unit (pullback M₁.toBase h).ringCatSheaf)) :=
  SheafOfModules.unitToPushforwardObjUnit (curveChange i₁ hi₁ h).toRingCatSheafHom

omit [IsAlgClosed κ] in
theorem jFst_app (W : (pullback x h).Opens) (m : Γ(pullback x h, W)) :
    (jFst x M₁ i₁ hi₁ h).app W m = (curveChange i₁ hi₁ h).app W m := rfl

theorem nodeCondition_one_iff (W : (pullback x h).Opens) (i : Fin s)
    (f : Γ(pullback M₁.toBase h, (curveChange i₁ hi₁ h) ⁻¹ᵁ W))
    (g : Γ(pullback M₂.toBase h, (curveChange i₂ hi₂ h) ⁻¹ᵁ W)) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i f g ↔
      (nodeSectionFst M₁ a h i).appLE ((curveChange i₁ hi₁ h) ⁻¹ᵁ W)
          (nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h i W) inf_le_left f =
        (nodeSectionSnd M₂ b h i).appLE ((curveChange i₂ hi₂ h) ⁻¹ᵁ W)
          (nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h i W) inf_le_right g := by
  simp only [NodeCondition, Pi.one_apply, Units.val_one, map_one, one_mul]

variable [IsClosedImmersion i₁] [IsClosedImmersion i₂]

theorem local_affine [IsReduced X]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1
                = i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i : κ))).1)
    (hinter : ∀ p q, i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (W : (pullback x h).Opens) (hW : IsAffineOpen W) (V : X.affineOpens)
    (hWV : W ≤ (pullback.fst x h) ⁻¹ᵁ (V : X.Opens)) :
    Function.Injective (fun m : Γ(SheafOfModules.unit (pullback x h).ringCatSheaf, W) =>
        ((jFst x M₁ i₁ hi₁ h).app W m, (jFst x M₂ i₂ hi₂ h).app W m)) ∧
      Set.range (fun m : Γ(SheafOfModules.unit (pullback x h).ringCatSheaf, W) =>
        ((jFst x M₁ i₁ hi₁ h).app W m, (jFst x M₂ i₂ hi₂ h).app W m)) =
        {fg | ∀ i : Fin s, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i fg.1 fg.2} := by
  haveI := fun i => isClosedImmersion_nodePt x M₁ i₁ hi₁ a i

  set pr := pullback.fst x h with hpr
  set φ := pr.appLE V W hWV with hφ
  set q₁ := (curveChange i₁ hi₁ h).app W with hq₁
  set q₂ := (curveChange i₂ hi₂ h).app W with hq₂
  set σ₁ := fun i => nodeSectionFst M₁ a h i with hσ₁
  set σ₂ := fun i => nodeSectionSnd M₂ b h i with hσ₂
  set nl := fun i => nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h i W with hnl
  set e₁ := fun i => (σ₁ i).appLE ((curveChange i₁ hi₁ h) ⁻¹ᵁ W) (nl i) inf_le_left with he₁
  set e₂ := fun i => (σ₂ i).appLE ((curveChange i₂ hi₂ h) ⁻¹ᵁ W) (nl i) inf_le_right with he₂

  have hpts : ∀ i, (pointAt M₁ (a i : κ)).1 ≫ i₁ = (pointAt M₂ (b i : κ)).1 ≫ i₂ := fun i =>
    pointAt_comp_eq_pointAt_comp' κ x M₁ M₂ i₁ i₂ hi₁ hi₂
      (a i : κ) (b i : κ) (hnode i)
  have hν : ∀ i, σ₁ i ≫ curveChange i₁ hi₁ h = σ₂ i ≫ curveChange i₂ hi₂ h := fun i =>
    TwoGluedLinesC1.NodeLocal.nodeSectionFst_comp_eq_nodeSectionSnd_comp x M₁ M₂ i₁ i₂ hi₁ hi₂ a b hpts h i
  have hρ₁ : ∀ i, σ₁ i ≫ curveChange i₁ hi₁ h = nodeSec x M₁ i₁ hi₁ a h i := fun i =>
    nodeSectionFst_comp x M₁ i₁ hi₁ a h i
  have hρ₂ : ∀ i, σ₂ i ≫ curveChange i₂ hi₂ h = nodeSec x M₁ i₁ hi₁ a h i := fun i =>
    (hν i).symm.trans (hρ₁ i)

  have hnl_le : ∀ i, nl i ≤ (nodeSec x M₁ i₁ hi₁ a h i) ⁻¹ᵁ W := by
    intro i
    rw [hnl]
    dsimp only
    rw [TwoGluedLinesC1.NodeLocal.nodeLocus_eq hν i W, hρ₁ i]
  have hcomp₁ : ∀ i, q₁ ≫ e₁ i = (nodeSec x M₁ i₁ hi₁ a h i).appLE W (nl i) (hnl_le i) := by
    intro i
    rw [hq₁, he₁, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (hρ₁ i)]
  have hcomp₂ : ∀ i, q₂ ≫ e₂ i = (nodeSec x M₁ i₁ hi₁ a h i).appLE W (nl i) (hnl_le i) := by
    intro i
    rw [hq₂, he₂, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (hρ₂ i)]

  obtain ⟨hsurj₁, hker₁⟩ := TwoGluedLinesC1.BaseChange.surjective_and_ker_app_eq
    (isPullback_curveChange x h i₁ hi₁) V.2 hW hWV
  obtain ⟨hsurj₂, hker₂⟩ := TwoGluedLinesC1.BaseChange.surjective_and_ker_app_eq
    (isPullback_curveChange x h i₂ hi₂) V.2 hW hWV
  have hkerν : ∀ i, RingHom.ker ((nodeSec x M₁ i₁ hi₁ a h i).app W).hom =
      (RingHom.ker ((nodePt M₁ i₁ a i).app V).hom).map φ.hom := fun i =>
    (TwoGluedLinesC1.BaseChange.surjective_and_ker_app_eq (isPullback_nodeSec x M₁ i₁ hi₁ a h i)
      V.2 hW hWV).2
  have hkerν' : ∀ i, RingHom.ker ((e₁ i).hom.comp q₁.hom) =
      (RingHom.ker ((nodePt M₁ i₁ a i).app V).hom).map φ.hom := by
    intro i
    rw [← hkerν i, ← CommRingCat.hom_comp, hcomp₁ i, Scheme.Hom.appLE, CommRingCat.hom_comp,
      ← RingHom.comap_ker]
    have hinj := presheaf_map_injective_of_eq
      ((TwoGluedLinesC1.NodeLocal.nodeLocus_eq hν i W).trans (by rw [hρ₁ i])) (hnl_le i)
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    rfl

  have hflat : φ.hom.Flat := pr.flat_appLE V.2 hW hWV
  letI := φ.hom.toAlgebra
  haveI : Module.Flat Γ(X, V) Γ(pullback x h, W) := hflat

  have hinf : RingHom.ker q₁.hom ⊓ RingHom.ker q₂.hom = ⊥ := by
    rw [hq₁, hq₂, hker₁, hker₂]
    change Ideal.map (algebraMap _ _) _ ⊓ Ideal.map (algebraMap _ _) _ = ⊥
    rw [← TwoGluedLinesC1.ConductorFlat.map_inf_of_flat, ker_inf_ker_eq_bot M₁ M₂ i₁ i₂ hcover V, Ideal.map_bot]
  have hsup : RingHom.ker q₁.hom ⊔ RingHom.ker q₂.hom = ⨅ i, RingHom.ker ((e₁ i).hom.comp q₁.hom) := by
    simp_rw [hkerν']
    rw [hq₁, hq₂, hker₁, hker₂]
    change Ideal.map (algebraMap _ _) _ ⊔ Ideal.map (algebraMap _ _) _ =
      ⨅ i, Ideal.map (algebraMap _ _) _
    rw [← Ideal.map_sup, ker_sup_ker_eq_iInf x M₁ M₂ i₁ i₂ hi₁ hi₂ a b hnode hinter htrans V,
      TwoGluedLinesC1.ConductorFlat.map_iInf_of_flat]

  obtain ⟨hinj, hrange⟩ := injective_and_range_pair_eq q₁.hom q₂.hom hsurj₁ hsurj₂
    (fun i => (e₁ i).hom) (fun i => (e₂ i).hom)
    (fun i => by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hcomp₁, hcomp₂]) hinf hsup
  refine ⟨hinj, ?_⟩
  refine hrange.trans ?_
  ext ⟨f, g⟩
  simp only [Set.mem_setOf_eq, nodeCondition_one_iff]
  rfl

end OverT

end TwoGluedLinesC1.Conductor
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit.TwoGluedLinesC1 P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit.TwoGluedLinesC1.Conductor"
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit.TwoGluedLinesC1"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit.TwoGluedLinesC1 P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit.TwoGluedLinesC1.Conductor"

open TwoGluedLinesC1.Conductor in
theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → κˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1
                = i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i : κ))).1)
    (hinter : ∀ p q, i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) :
    IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 (SheafOfModules.unit (pullback x h).ringCatSheaf) := by
  refine ⟨jFst x M₁ i₁ hi₁ h, jFst x M₂ i₂ hi₂ h, fun W => ?_⟩

  have hpts : ∀ i, (pointAt M₁ (a i : κ)).1 ≫ i₁ = (pointAt M₂ (b i : κ)).1 ≫ i₂ := fun i =>
    pointAt_comp_eq_pointAt_comp' κ x M₁ M₂ i₁ i₂ hi₁ hi₂
      (a i : κ) (b i : κ) (hnode i)
  have hν : ∀ i, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h =
      nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h := fun i =>
    TwoGluedLinesC1.NodeLocal.nodeSectionFst_comp_eq_nodeSectionSnd_comp x M₁ M₂ i₁ i₂ hi₁ hi₂ a b hpts h i

  let B : Set (pullback x h).Opens :=
    {W | IsAffineOpen W ∧ ∃ V : X.affineOpens, W ≤ (pullback.fst x h) ⁻¹ᵁ (V : X.Opens)}
  have hB : ∀ (W : (pullback x h).Opens) (y : ↥(pullback x h)), y ∈ W → ∃ W' ∈ B, y ∈ W' ∧ W' ≤ W := by
    intro W y hy
    obtain ⟨V, hV, hyV, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show (pullback.fst x h).base y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨W', hW', hyW', hW'le⟩ := (Opens.isBasis_iff_nbhd.mp (pullback x h).isBasis_affineOpens)
      (show y ∈ W ⊓ (pullback.fst x h) ⁻¹ᵁ V from ⟨hy, hyV⟩)
    exact ⟨W', ⟨hW', ⟨V, hV⟩, fun z hz => (hW'le hz).2⟩, hyW', fun z hz => (hW'le hz).1⟩

  let S : ∀ W : (pullback x h).Opens,
      Set (Γ((Scheme.Modules.pushforward (curveChange i₁ hi₁ h)).obj
              (SheafOfModules.unit (pullback M₁.toBase h).ringCatSheaf), W) ×
           Γ((Scheme.Modules.pushforward (curveChange i₂ hi₂ h)).obj
              (SheafOfModules.unit (pullback M₂.toBase h).ringCatSheaf), W)) :=
    fun W => {fg | ∀ i : Fin s, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i fg.1 fg.2}
  have hS : TwoGluedLinesC1.LocalToGlobal.IsLocalFamily S := by
    refine ⟨fun hle p hp i => ?_, fun 𝒲 hle hcov p hp i => ?_⟩
    · exact TwoGluedLinesC1.NodeLocal.nodeCondition_res 1 i hle p.1 p.2 (hp i)
    · exact TwoGluedLinesC1.NodeLocal.nodeCondition_glue 1 hν i 𝒲 hle hcov p.1 p.2 (fun W' hW' => hp W' hW' i)
  exact TwoGluedLinesC1.LocalToGlobal.injective_and_range_eq_of_basis B hB S hS
    (fun W' hW' => by
      obtain ⟨hW', V, hle⟩ := hW'
      exact local_affine x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h hcover hnode hinter htrans W' hW' V hle) W

end S_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit (solution)
