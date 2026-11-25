-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PushComparisonBijectiveOfIsClosedEmbedding
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PushComparisonBijectiveOfIsClosedEmbedding
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:10.655102+00:00
-- url     : https://prove2.me/theorems/df0fb4e6-bdb3-5a6f-b788-df3bfa80ddbb
-- title:
--   Push Comparison Bijective Of Is Closed Embedding
-- statement:
--   Definitions and structural lemmas for Push Comparison Bijective Of Is Closed Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_Flasque_injectiveShortComplex_shortExact
import Theorems.Thm_GlobalTheory_SheafLES_equivZero_res
import Theorems.Thm_GlobalTheory_SheafLES_map_comp
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafPull_sitePull_bijective_succ
import Theorems.Thm_GlobalTheory_SheafPull_sitePull_bijective_zero
import Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_injective_53c598f24470
import Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_199e9bf4dfbd
import Theorems.Thm_P2M_GlobalTheory_SheafLES___equivZero_symm_eq_zero_iff_47a22b9ce459
import Theorems.Thm_P2M_GlobalTheory_SheafLES___injective_of_subsingleton_bddba28211f5
import Theorems.Thm_P2M_GlobalTheory_SheafLES___res_2b8f5cf68032
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id


set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' u
noncomputable section
namespace GlobalTheory
namespace SheafPull
section Space
open SheafLES Flasque
abbrev AbSheaf (X : TopCat.{u}) := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
variable {X Y : TopCat.{u}}
abbrev push (f : Y ⟶ X) : AbSheaf Y ⥤ AbSheaf X :=
  (Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u} _ _
abbrev restr {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j) : AbSheaf X ⥤ AbSheaf Y :=
  haveI := hj.functor_isContinuous
  hj.functor.sheafPushforwardContinuous AddCommGrpCat.{u} _ _
instance (f : Y ⟶ X) : (push f).IsRightAdjoint :=
  inferInstanceAs (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).IsRightAdjoint
instance preservesFiniteLimits_sheafPullback (f : Y ⟶ X) : PreservesFiniteLimits
    ((Opens.map f).sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y)) := by
  apply Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
instance {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j) : (restr hj).Additive where
  map_add := rfl
instance preservesFiniteLimits_restr {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j) :
    PreservesFiniteLimits (restr hj) :=
  preservesFiniteLimits_of_natIso (F := (Opens.map j).sheafPullback AddCommGrpCat.{u} _ _)
    (hj.sheafPullbackIso AddCommGrpCat.{u})
instance preservesFiniteColimits_restr {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j) :
    PreservesFiniteColimits (restr hj) :=
  preservesFiniteColimits_of_natIso (F := (Opens.map j).sheafPullback AddCommGrpCat.{u} _ _)
    (hj.sheafPullbackIso AddCommGrpCat.{u})
theorem shortExact_map_restr {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j)
    {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) : (S.map (restr hj)).ShortExact :=
  hS.map_of_exact _
theorem isFlasque_restr {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j) (F : AbSheaf X)
    (hF : TopCat.Sheaf.IsFlasque F) : TopCat.Sheaf.IsFlasque ((restr hj).obj F) where
  epi i := hF.epi (hj.functor.op.map i)
theorem isFlasque_push (f : Y ⟶ X) (G : AbSheaf Y) (hG : TopCat.Sheaf.IsFlasque G) :
    TopCat.Sheaf.IsFlasque ((push f).obj G) where
  epi i := hG.epi ((Opens.map f).op.map i)
lemma isFlasque_of_injective' (I : AbSheaf X) [hI : Injective I] : TopCat.Sheaf.IsFlasque I :=
  isFlasque_of_injective I (hI := hI)
def restrUnit {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j) : 𝟭 _ ⟶ restr hj ⋙ push j where
  app F := ⟨{ app V := F.obj.map (hj.isOpenMap.adjunction.counit.app V.unop).op
              naturality V V' i := (F.obj.map_comp _ _).symm.trans
                (F.obj.map_comp (hj.isOpenMap.adjunction.counit.app V.unop).op
                  (hj.functor.map ((Opens.map j).map i.unop)).op) }⟩
  naturality F G s := by
    ext V : 3
    exact (s.hom.naturality _).symm
lemma epi_push_map (f : Y ⟶ X) {G G' : AbSheaf Y} (g : G ⟶ G')
    (h : ∀ (V : Opens X) (t : G'.obj.obj (op ((Opens.map f).obj V))), ∀ x ∈ V,
      ∃ (W : Opens X) (i : W ⟶ V), x ∈ W ∧ ∃ s, g.hom.app (op ((Opens.map f).obj W)) s =
        G'.obj.map ((Opens.map f).map i).op t) : Epi ((push f).map g) := by
  rw [← Sheaf.isLocallySurjective_iff_epi']
  refine ⟨fun {V} t x hx ↦ ?_⟩
  obtain ⟨W, i, hW, s, hs⟩ := h V t x hx
  exact ⟨W, i, ⟨s, hs⟩, hW⟩
lemma shortExact_map_push (f : Y ⟶ X) {S : ShortComplex (AbSheaf Y)} (hS : S.ShortExact)
    (h : Epi ((push f).map S.g)) : (S.map (push f)).ShortExact :=
  have := hS.mono_f
  ShortComplex.ShortExact.mk' (hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance)
    (inferInstanceAs (Mono ((push f).map S.f))) h
theorem preservesEpimorphisms_push {f : Y ⟶ X} (hf : Topology.IsClosedEmbedding f) :
    (push f).PreservesEpimorphisms where
  preserves {G G'} g hg := by
    refine epi_push_map f g fun V t x hx ↦ ?_
    by_cases hxf : x ∈ Set.range f
    · obtain ⟨y, rfl⟩ := hxf
      rw [← Sheaf.isLocallySurjective_iff_epi'] at hg
      obtain ⟨W', k, ⟨s, hs⟩, hy⟩ := hg.imageSieve_mem t y hx
      obtain ⟨W₀, hW₀, hW'⟩ := hf.isInducing.isOpen_iff.1 W'.isOpen
      have hle : (Opens.map f).obj (V ⊓ ⟨W₀, hW₀⟩) ≤ W' := fun z hz ↦ by
        have : z ∈ f ⁻¹' W₀ := hz.2
        rwa [hW'] at this
      have hy' : y ∈ f ⁻¹' W₀ := by rwa [hW']
      refine ⟨V ⊓ ⟨W₀, hW₀⟩, homOfLE inf_le_left, ⟨hx, hy'⟩, G.obj.map (homOfLE hle).op s, ?_⟩
      refine (ConcreteCategory.congr_hom (g.hom.naturality (homOfLE hle).op) s).trans ?_
      rw [ConcreteCategory.comp_apply, hs, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    · let W : Opens X := V ⊓ ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
      have hW : (Opens.map f).obj W = ⊥ :=
        le_bot_iff.1 fun z hz ↦ (hz.2 ⟨z, rfl⟩).elim
      have : Subsingleton (G'.obj.obj (op ((Opens.map f).obj W))) :=
        AddCommGrpCat.subsingleton_of_isZero
          (TopCat.Sheaf.isTerminalOfEqEmpty G' hW).isZero
      exact ⟨W, homOfLE inf_le_left, ⟨hx, hxf⟩, 0, Subsingleton.elim _ _⟩
theorem shortExact_map_push_of_isClosedEmbedding {f : Y ⟶ X} (hf : Topology.IsClosedEmbedding f)
    {S : ShortComplex (AbSheaf Y)} (hS : S.ShortExact) : (S.map (push f)).ShortExact :=
  have := preservesEpimorphisms_push hf
  have := hS.epi_g
  shortExact_map_push f hS inferInstance
variable [HasExt.{w} (AbSheaf X)] [HasExt.{w'} (AbSheaf Y)]
abbrev pull (f : Y ⟶ X) {F : AbSheaf X} {G : AbSheaf Y} (φ : F ⟶ (push f).obj G) (n : ℕ)
    {V : Opens X} {W : Opens Y} (i : W ⟶ (Opens.map f).obj V) :
    Sheaf.H'.{w} F n V →+ Sheaf.H'.{w'} G n W :=
  sitePull.{w, w'} (Opens.map f) φ n i
section Open
variable {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j)
theorem pull_restrUnit_bijective (F : AbSheaf X) (n : ℕ) {V : Opens X} {W : Opens Y}
    (i : W ⟶ (Opens.map j).obj V) (h : V ≤ hj.functor.obj W) :
    Function.Bijective (pull.{w, w'} j ((restrUnit hj).app F) n i) := by
  induction n generalizing F with
  | zero =>
    refine sitePull_bijective_zero _ _ _ ?_
    have hk : hj.functor.obj W ≤ V := leOfHom ((hj.isOpenMap.adjunction.homEquiv _ _).symm i)
    have : IsIso (homOfLE hk) := ⟨homOfLE h, rfl, rfl⟩
    exact (congrArg Function.Bijective (funext fun s ↦
      (ConcreteCategory.congr_hom (F.obj.map_comp _ _) s).symm)).mpr
      (ConcreteCategory.bijective_of_isIso (F.obj.map (homOfLE hk).op))
  | succ n ih =>
    have hS := injectiveShortComplex_shortExact F
    have hI := isFlasque_of_injective' (Injective.under F)
    exact sitePull_bijective_succ _ hS (shortExact_map_restr hj hS)
      ((injectiveShortComplex F).mapNatTrans (restrUnit hj)) n i (ih _).surjective (ih _)
      (subsingleton_H'_of_injective _ n V)
      (subsingleton_H'_of_isFlasque _ (hF := isFlasque_restr hj _ hI) n W)
def restrEquiv (F : AbSheaf X) (n : ℕ) (V : Opens Y) :
    Sheaf.H'.{w} F n (hj.functor.obj V) ≃+ Sheaf.H'.{w'} ((restr hj).obj F) n V :=
  AddEquiv.ofBijective
    (pull.{w, w'} j ((restrUnit hj).app F) n (hj.isOpenMap.adjunction.unit.app V))
    (pull_restrUnit_bijective hj F n _ le_rfl)
end Open
section Push
variable (f : Y ⟶ X)
abbrev pushComparison (G : AbSheaf Y) (n : ℕ) (V : Opens X) :
    Sheaf.H'.{w} ((push f).obj G) n V →+ Sheaf.H'.{w'} G n ((Opens.map f).obj V) :=
  pull.{w, w'} f (𝟙 _) n (𝟙 _)
theorem pushComparison_bijective_zero (G : AbSheaf Y) (V : Opens X) :
    Function.Bijective (pushComparison.{w, w'} f G 0 V) := by
  refine sitePull_bijective_zero _ _ _ ?_
  exact (congrArg Function.Bijective (funext fun s ↦
    ConcreteCategory.congr_hom (G.obj.map_id _) _)).mpr Function.bijective_id
theorem pushComparison_bijective_of_class (P : AbSheaf Y → Prop)
    (hP : ∀ S : ShortComplex (AbSheaf Y), S.ShortExact → Injective S.X₂ → P S.X₁ →
      Epi ((push f).map S.g) ∧ P S.X₃)
    (G : AbSheaf Y) (hG : P G) (n : ℕ) (V : Opens X) :
    Function.Bijective (pushComparison.{w, w'} f G n V) := by
  induction n generalizing G with
  | zero => exact pushComparison_bijective_zero f G V
  | succ n ih =>
    have hS := injectiveShortComplex_shortExact G
    have hI := isFlasque_of_injective' (Injective.under G)
    obtain ⟨h₁, h₂⟩ := hP _ hS (Injective.injective_under G) hG
    refine sitePull_bijective_succ _ (shortExact_map_push f hS h₁) hS (𝟙 _) n _ ?_ (ih _ h₂)
      (subsingleton_H'_of_isFlasque _ (hF := isFlasque_push f _ hI) n V)
      (subsingleton_H'_of_injective _ n _)
    cases n with
    | zero => exact (pushComparison_bijective_zero f _ V).surjective
    | succ n =>
      have := subsingleton_H'_of_injective.{w'} (Injective.under G) n ((Opens.map f).obj V)
      exact fun y ↦ ⟨0, @Subsingleton.elim _ this _ _⟩
omit [HasExt.{w} (AbSheaf X)] in

def HigherDirectImagesVanish (G : AbSheaf Y) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (V : Opens X) (α : Sheaf.H'.{w'} G n ((Opens.map f).obj V)), ∀ x ∈ V,
    ∃ (W : Opens X) (i : W ⟶ V), x ∈ W ∧ res G n ((Opens.map f).map i) α = 0
variable {f}
omit [HasExt.{w} (AbSheaf X)] in

theorem HigherDirectImagesVanish.epi {S : ShortComplex (AbSheaf Y)} (hS : S.ShortExact)
    (h : HigherDirectImagesVanish.{w'} f S.X₁) : Epi ((push f).map S.g) := by
  refine epi_push_map f S.g fun V t x hx ↦ ?_
  obtain ⟨W, i, hW, h0⟩ := h 1 one_pos V (δ hS 0 _ ((equivZero _ _).symm t)) x hx
  refine ⟨W, i, hW, (δ_equivZero_symm_eq_zero_iff.{w'} hS _ _).1 ?_⟩
  rw [← h0, δ_res]
  congr 1
  rw [AddEquiv.symm_apply_eq, equivZero_res, AddEquiv.apply_symm_apply]
omit [HasExt.{w} (AbSheaf X)] in

theorem HigherDirectImagesVanish.quotient {S : ShortComplex (AbSheaf Y)} (hS : S.ShortExact)
    [Injective S.X₂] (h : HigherDirectImagesVanish.{w'} f S.X₁) :
    HigherDirectImagesVanish.{w'} f S.X₃ := by
  intro n hn V α x hx
  obtain ⟨W, i, hW, h0⟩ := h (n + 1) n.succ_pos V (δ hS n _ α) x hx
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  refine ⟨W, i, hW, δ_injective_of_subsingleton hS _ _ (subsingleton_H'_of_injective _ n _) ?_⟩
  rw [← δ_res, h0, map_zero]
theorem pushComparison_bijective {G : AbSheaf Y} (h : HigherDirectImagesVanish.{w'} f G) (n : ℕ)
    (V : Opens X) : Function.Bijective (pushComparison.{w, w'} f G n V) :=
  pushComparison_bijective_of_class f (HigherDirectImagesVanish.{w'} f)
    (fun _ hS _ h ↦ ⟨h.epi hS, h.quotient hS⟩) G h n V
theorem pushComparison_bijective_of_isClosedEmbedding (hf : Topology.IsClosedEmbedding f)
    (G : AbSheaf Y) (n : ℕ) (V : Opens X) :
    Function.Bijective (pushComparison.{w, w'} f G n V) :=
  pushComparison_bijective_of_class f (fun _ ↦ True)
    (fun _ hS _ _ ↦ ⟨(shortExact_map_push_of_isClosedEmbedding hf hS).epi_g, trivial⟩) G trivial n V
def pushEquiv {G : AbSheaf Y} (h : HigherDirectImagesVanish.{w'} f G) (n : ℕ) (V : Opens X) :
    Sheaf.H'.{w} ((push f).obj G) n V ≃+ Sheaf.H'.{w'} G n ((Opens.map f).obj V) :=
  AddEquiv.ofBijective _ (pushComparison_bijective.{w, w'} h n V)
def closedEquiv (hf : Topology.IsClosedEmbedding f) (G : AbSheaf Y) (n : ℕ) (V : Opens X) :
    Sheaf.H'.{w} ((push f).obj G) n V ≃+ Sheaf.H'.{w'} G n ((Opens.map f).obj V) :=
  AddEquiv.ofBijective _ (pushComparison_bijective_of_isClosedEmbedding.{w, w'} hf G n V)
end Push
end Space
section Functoriality
open SheafLES Flasque
variable {X Y Z : TopCat.{u}}
variable [HasExt.{w} (AbSheaf X)] [HasExt.{w'} (AbSheaf Y)] [HasExt.{w''} (AbSheaf Z)]
end Functoriality
section Scheme
open AlgebraicGeometry SheafLES
variable {X Y : Scheme.{u}}
def modulesRestrEquiv (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) (n : ℕ) (V : Y.Opens) :
    Sheaf.H'.{u} ((toAbSheaf X).obj M) n (j ''ᵁ V) ≃+
      Sheaf.H'.{u} ((toAbSheaf Y).obj (M.restrict j)) n V :=
  restrEquiv.{u, u} j.isOpenEmbedding ((toAbSheaf X).obj M) n V
def modulesClosedEquiv (f : Y ⟶ X) [IsClosedImmersion f] (M : Y.Modules) (n : ℕ) (V : X.Opens) :
    Sheaf.H'.{u} ((toAbSheaf X).obj ((Scheme.Modules.pushforward f).obj M)) n V ≃+
      Sheaf.H'.{u} ((toAbSheaf Y).obj M) n (f ⁻¹ᵁ V) :=
  closedEquiv.{u, u} f.isClosedEmbedding ((toAbSheaf Y).obj M) n V
end Scheme
end SheafPull
end GlobalTheory


