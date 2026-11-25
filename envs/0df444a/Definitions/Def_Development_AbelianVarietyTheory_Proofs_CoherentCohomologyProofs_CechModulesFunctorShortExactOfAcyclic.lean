-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:37.469286+00:00
-- url     : https://prove2.me/theorems/ddc06128-b356-4549-ad6b-8d64a5713372
-- title:
--   Cech Modules Functor Short Exact Of Acyclic
-- statement:
--   Definitions and structural lemmas for Cech Modules Functor Short Exact Of Acyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Theorems.Thm_GlobalTheory_AddEquivOfSurjectiveKernel_exists_addEquiv_of_surjective_of_ker_iff
import Theorems.Thm_GlobalTheory_Flasque_injectiveShortComplex_shortExact
import Theorems.Thm_GlobalTheory_SheafLES_equivZero_map
import Theorems.Thm_GlobalTheory_SheafLES_injective_zero
import Theorems.Thm_GlobalTheory_SheafLES_map_equivZero_symm
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_sections_surjective_of_subsingleton
import Theorems.Thm_GlobalTheory_cechAbFunctor_shortExact
import Theorems.Thm_GlobalTheory_cechAbHEquiv_map
import Theorems.Thm_GlobalTheory_cechAbHMap_id
import Theorems.Thm_GlobalTheory_cechAbHZeroEquiv_map
import Theorems.Thm_GlobalTheory_cechHMap_smulHom_apply
import Theorems.Thm_GlobalTheory_cechModulesFunctor_shortExact
import Theorems.Thm_GlobalTheory_cohOn_injective_zero
import Theorems.Thm_GlobalTheory_subsingleton_cechAbH_succ_of_isFlasque
import Theorems.Thm_P2M_GlobalTheory_Flasque_exists_hom____eq_9f8583d26737
import Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_injective_53c598f24470
import Theorems.Thm_P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7
import Theorems.Thm_P2M_GlobalTheory_SheafLES___surjective_of_subsingleton_5836d34aca61
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b
import Theorems.Thm_P2M_GlobalTheory_cohOn___naturality_642b907f030d
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__9304e9eeff37
import Theorems.Thm_P2M_GlobalTheory_cohOn_exact__c8d68170d18d
import Theorems.Thm_P2M_GlobalTheory_cohOn_subsingleton__f1f7d3cc4818
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.cechAbHMap_id


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
namespace GlobalTheory
theorem exists_addEquiv_of_surjective_of_ker {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : A →+ C) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : ∀ a, f a = 0 ↔ g a = 0) :
    ∃ e : B ≃+ C, ∀ a, e (f a) = g a := by
  first
  | exact @_root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff
  | exact _root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff
  | (apply _root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff ..)
section Cube
variable {ι : Type} [LinearOrder ι] {R : Type v} [Ring R]
end Cube
section Ab
variable {T : TopCat.{u}} {ι : Type}
def CechAcyclic (V : Opens T) (U : ι → Opens T)
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) : Prop :=
  ∀ s : Finset ι, s.Nonempty → ∀ q, Subsingleton (Sheaf.H'.{u} F (q + 1) (cechOpen V U s))
variable {V : Opens T} {U : ι → Opens T}
theorem cechAcyclic_of_injective (I : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    [Injective I] : CechAcyclic V U I := fun _ _ q => Flasque.subsingleton_H'_of_injective I q _
theorem CechAcyclic.of_shortExact₃
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (h₁ : CechAcyclic V U S.X₁) (h₂ : CechAcyclic V U S.X₂) : CechAcyclic V U S.X₃ :=
  fun s hs q => SheafLES.subsingleton₃ hS _ _ (h₂ s hs q) (h₁ s hs (q + 1))
theorem sections_shortExact_of_subsingleton
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (W : Opens T) (h : Subsingleton (Sheaf.H'.{u} S.X₁ 1 W)) :
    Function.Injective (S.f.hom.app (op W)) ∧
      Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) ∧
      Function.Surjective (S.g.hom.app (op W)) := by
  refine ⟨fun x y hxy => ?_, fun x => ?_, SheafLES.sections_surjective_of_subsingleton hS W h⟩
  · obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{u} S.X₁ W).surjective x
    obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{u} S.X₁ W).surjective y
    rw [← SheafLES.equivZero_map, ← SheafLES.equivZero_map] at hxy
    rw [SheafLES.injective_zero hS W ((SheafLES.equivZero.{u} S.X₂ W).injective hxy)]
  · obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{u} S.X₂ W).surjective x
    rw [← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (SheafLES.equivZero_map S.f W y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{u} S.X₁ W).surjective y
      exact ⟨y, (SheafLES.equivZero.{u} S.X₂ W).injective
        ((SheafLES.equivZero_map S.f W y).trans hy)⟩
variable [LinearOrder ι]
variable (V U) in

abbrev cechAbSheafFunctor : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⥤
    CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  sheafToPresheaf _ _ ⋙ cechAbFunctor V U
section Delta
variable {S S' : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})}
  (hS : S.ShortExact) (h₁ : CechAcyclic V U S.X₁)
include hS h₁ in

theorem cechAbSheafFunctor_shortExact : (S.map (cechAbSheafFunctor V U)).ShortExact :=
  cechAbFunctor_shortExact V U (S.map (sheafToPresheaf _ _)) fun s hs =>
    sections_shortExact_of_subsingleton hS _ (h₁ s hs 0)
def cechAbδ (n : ℕ) : cechAbH S.X₃.obj V U n →ₗ[ℤ] cechAbH S.X₁.obj V U (n + 1) :=
  ((cechAbSheafFunctor_shortExact hS h₁).δ n (n + 1) rfl).hom
theorem cechAbδ_exact₃ (n : ℕ) :
    Function.Exact (cechAbHMap V U S.g.hom n).hom (cechAbδ hS h₁ n) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cechAbSheafFunctor_shortExact hS h₁).homology_exact₃ n (n + 1) rfl)
theorem cechAbδ_exact₁ (n : ℕ) :
    Function.Exact (cechAbδ hS h₁ n) (cechAbHMap V U S.f.hom (n + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cechAbSheafFunctor_shortExact hS h₁).homology_exact₁ n (n + 1) rfl)
theorem cechAbδ_naturality (hS' : S'.ShortExact) (h₁' : CechAcyclic V U S'.X₁) (φ : S ⟶ S')
    (n : ℕ) (x : cechAbH S.X₃.obj V U n) :
    (cechAbHMap V U φ.τ₁.hom (n + 1)).hom (cechAbδ hS h₁ n x) =
      cechAbδ hS' h₁' n ((cechAbHMap V U φ.τ₃.hom n).hom x) :=
  congr(($(HomologicalComplex.HomologySequence.δ_naturality
    ((cechAbSheafFunctor V U).mapShortComplex.map φ) (cechAbSheafFunctor_shortExact hS h₁)
    (cechAbSheafFunctor_shortExact hS' h₁') n (n + 1) rfl)).hom x)
theorem cechAbδ_surjective [Finite ι] [Injective S.X₂] (n : ℕ) :
    Function.Surjective (cechAbδ hS h₁ n) := fun x =>
  haveI := Flasque.isFlasque_of_injective (X := T) S.X₂ (hI := ‹_›)
  (cechAbδ_exact₁ hS h₁ n x).1
    (@Subsingleton.elim _ (subsingleton_cechAbH_succ_of_isFlasque (T := T) S.X₂ V U n) _ _)
end Delta
variable (V U) in

def CechComparison (n : ℕ) : Type (u + 1) :=
  {e : ∀ F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}, CechAcyclic V U F →
      (cechAbH F.obj V U n ≃+ Sheaf.H'.{u} F n V) //
    ∀ (F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (hF : CechAcyclic V U F)
      (hG : CechAcyclic V U G) (φ : F ⟶ G) (x : cechAbH F.obj V U n),
      e G hG ((cechAbHMap V U φ.hom n).hom x) = SheafLES.map φ n V (e F hF x)}
def CechComparison.zero (hc : V ≤ ⨆ i, U i) : CechComparison V U 0 :=
  ⟨fun F _ => (cechAbHZeroEquiv F.property hc).toAddEquiv.trans (SheafLES.equivZero F V).symm,
    fun F G _ _ φ x => by
      refine Eq.trans ?_ (SheafLES.map_equivZero_symm φ V _).symm
      exact congrArg (SheafLES.equivZero G V).symm
        (cechAbHZeroEquiv_map F.property G.property hc φ.hom x)⟩
theorem CechComparison.exists_succ [Finite ι] {n : ℕ} (e : CechComparison V U n) :
    ∃ e' : CechComparison V U (n + 1),
      ∀ (S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}))
        (hS : S.ShortExact) (h₁ : CechAcyclic V U S.X₁) (h₃ : CechAcyclic V U S.X₃) x,
        e'.1 S.X₁ h₁ (cechAbδ hS h₁ n x) = SheafLES.δ hS n V (e.1 S.X₃ h₃ x) := by
  obtain ⟨e, he⟩ := e
  let I (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :=
    Flasque.injectiveShortComplex F
  have hI F : (I F).ShortExact := Flasque.injectiveShortComplex_shortExact F
  have inj F : Injective (I F).X₂ := inferInstanceAs (Injective (Injective.under F))
  have a₂ F : CechAcyclic V U (I F).X₂ := cechAcyclic_of_injective _
  have a₃ F (hF : CechAcyclic V U F) : CechAcyclic V U (I F).X₃ :=
    CechAcyclic.of_shortExact₃ (hI F) hF (a₂ F)
  have ex F (hF : CechAcyclic V U F) : ∃ e' : cechAbH F.obj V U (n + 1) ≃+ Sheaf.H'.{u} F (n + 1) V,
      ∀ x, e' (cechAbδ (hI F) hF n x) = SheafLES.δ (hI F) n V (e _ (a₃ F hF) x) := by
    refine exists_addEquiv_of_surjective_of_ker (cechAbδ (hI F) hF n).toAddMonoidHom
      ((SheafLES.δ (hI F) n V).comp (e _ (a₃ F hF)).toAddMonoidHom)
      (cechAbδ_surjective (hI F) hF n)
      ((SheafLES.δ_surjective_of_subsingleton (hI F) n V
        (Flasque.subsingleton_H'_of_injective _ n V)).comp (e _ (a₃ F hF)).surjective)
      fun x => ((cechAbδ_exact₃ (hI F) hF n x).trans ?_).trans
        (SheafLES.exact₃ (hI F) n V (e _ (a₃ F hF) x)).symm
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (he _ _ (a₂ F) _ _ y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (e _ (a₂ F)).surjective y
      exact ⟨y, (e _ (a₃ F hF)).injective ((he _ _ (a₂ F) _ _ y).trans hy)⟩
  choose e' he' using ex
  have key (S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}))
      (hS : S.ShortExact) (h₁ : CechAcyclic V U S.X₁) (h₃ : CechAcyclic V U S.X₃) G hG
      (f : S.X₁ ⟶ G) (x : cechAbH S.X₃.obj V U n) :
      e' G hG ((cechAbHMap V U f.hom (n + 1)).hom (cechAbδ hS h₁ n x)) =
        SheafLES.map f (n + 1) V (SheafLES.δ hS n V (e S.X₃ h₃ x)) := by
    obtain ⟨φ, hφ⟩ := Flasque.exists_hom_τ₁_eq (T := I G) hS f
    have e₁ := cechAbδ_naturality hS h₁ (hI G) hG φ n x
    have e₂ := SheafLES.δ_naturality hS (hI G) φ n V (e S.X₃ h₃ x)
    rw [hφ] at e₁ e₂
    refine (congrArg (e' G hG) e₁).trans ((he' G hG _).trans (Eq.trans ?_ e₂.symm))
    exact congrArg _ (he _ _ h₃ _ φ.τ₃ x)
  refine ⟨⟨e', fun F G hF hG φ x => ?_⟩, fun S hS h₁ h₃ x => ?_⟩
  · obtain ⟨x, rfl⟩ := cechAbδ_surjective (hI F) hF n x
    exact (key (I F) (hI F) hF (a₃ F hF) G hG φ x).trans (congrArg _ (he' F hF x).symm)
  · have := key S hS h₁ h₃ S.X₁ h₁ (𝟙 _) x
    rw [SheafLES.map_id] at this
    refine Eq.trans (congrArg _ ?_) this
    exact (congr(($(cechAbHMap_id S.X₁.obj V U (n + 1))).hom (cechAbδ hS h₁ n x))).symm
variable [Finite ι] (hc : V ≤ ⨆ i, U i)
def cechComparisonOfCover (n : ℕ) : CechComparison V U n :=
  Nat.rec (motive := fun n => CechComparison V U n) (CechComparison.zero hc)
    (fun _ e => e.exists_succ.choose) n
variable {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}
def cechAbHEquivH' (hF : CechAcyclic V U F) (n : ℕ) :
    cechAbH F.obj V U n ≃+ Sheaf.H'.{u} F n V :=
  (cechComparisonOfCover hc n).1 F hF
theorem cechAbHEquivH'_map (hF : CechAcyclic V U F) (hG : CechAcyclic V U G) (φ : F ⟶ G) (n : ℕ)
    (x : cechAbH F.obj V U n) :
    cechAbHEquivH' hc hG n ((cechAbHMap V U φ.hom n).hom x) =
      SheafLES.map φ n V (cechAbHEquivH' hc hF n x) :=
  (cechComparisonOfCover hc n).2 F G hF hG φ x
end Ab
section Modules
variable {X : Scheme.{u}} {ι : Type}
def CechAcyclicMod (V : X.Opens) (U : ι → X.Opens) (F : X.Modules) : Prop :=
  ∀ s : Finset ι, s.Nonempty → ∀ q, Subsingleton (cohOn F (cechOpen V U s) (q + 1))
variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}
theorem cechAcyclicMod_iff : CechAcyclicMod V U F ↔
    CechAcyclic (T := X.toPresheafedSpace.carrier) V U ((toAbSheaf X).obj F) := Iff.rfl
variable [LinearOrder ι] (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
section Delta
variable {S S' : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : CechAcyclicMod V U S.X₁)
include hS h₁ in

theorem cechModulesFunctor_shortExact_of_acyclic :
    (S.map (cechModulesFunctor R V U)).ShortExact :=
  cechModulesFunctor_shortExact R V U S fun s hs =>
    sections_shortExact_of_subsingleton (T := X.toPresheafedSpace.carrier)
      (shortExact_toAbSheaf hS) _ (h₁ s hs 0)
def cechδ (n : ℕ) : cechH R S.X₃ V U n →ₗ[R] cechH R S.X₁ V U (n + 1) :=
  ((cechModulesFunctor_shortExact_of_acyclic R hS h₁).δ n (n + 1) rfl).hom
end Delta
variable [Finite ι] (hc : V ≤ ⨆ i, U i)
def cechHAddEquivCohOn (hF : CechAcyclicMod V U F) (n : ℕ) : cechH R F V U n ≃+ cohOn F V n :=
  ((cechAbHEquiv R F V U n).symm.trans
    (cechAbHEquivH' (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF) n)).trans
    (cohOn.toH' F V n).symm
theorem toH'_cechHAddEquivCohOn (hF : CechAcyclicMod V U F) (n : ℕ)
    (x : cechAbH F.presheaf V U n) :
    cohOn.toH' F V n (cechHAddEquivCohOn R hc hF n (cechAbHEquiv R F V U n x)) =
      cechAbHEquivH' (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF) n x :=
  congrArg (cechAbHEquivH' (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF) n)
    ((cechAbHEquiv R F V U n).symm_apply_apply x)
theorem cechHAddEquivCohOn_map (hF : CechAcyclicMod V U F) (hG : CechAcyclicMod V U G)
    (φ : F ⟶ G) (n : ℕ) (x : cechH R F V U n) :
    cechHAddEquivCohOn R hc hG n ((cechHMap R V U φ n).hom x) =
      cohOn.map R φ V n (cechHAddEquivCohOn R hc hF n x) := by
  obtain ⟨y, rfl⟩ := (cechAbHEquiv R F V U n).surjective x
  apply (cohOn.toH' G V n).injective
  rw [← cechAbHEquiv_map, toH'_cechHAddEquivCohOn, cohOn.toH'_map, toH'_cechHAddEquivCohOn]
  exact cechAbHEquivH'_map (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF)
    (cechAcyclicMod_iff.1 hG) ((toAbSheaf X).map φ) n y
def cechHEquivCohOn (hF : CechAcyclicMod V U F) (n : ℕ) : cechH R F V U n ≃ₗ[R] cohOn F V n :=
  { cechHAddEquivCohOn R hc hF n with
    map_smul' := fun r x =>
      (congrArg (cechHAddEquivCohOn R hc hF n) (cechHMap_smulHom_apply R F V U r n x).symm).trans
        (cechHAddEquivCohOn_map R hc hF hF _ n x) }
end Modules
end GlobalTheory


