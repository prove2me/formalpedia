-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3982ef1d-c8ba-56ff-9edd-d95e3460e095

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"

set_option autoImplicit false

universe u

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Surjective Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf IsAffine Scheme.preimage_basicOpen Scheme IsOpenImmersion Scheme.Hom.isIso_app isAffineOpen_top Scheme.Modules.pullbackPushforwardAdjunction Scheme.Hom.preimage_image_eq IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Opens.ι_preimage_self Scheme.Opens.opensRange_ι toSpecΓ Scheme.Hom.image_le_opensRange OModulePresheaf OModulePresheaf.d_apply OModulePresheaf.ofModules OModulePresheaf.ofModules_res_apply Scheme.Modules.Hom.epi_iff_locallySurjective Scheme.Modules.Hom.mono_iff_injective Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.bijective_unit_app_of_le_opensRange OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial Scheme.Modules.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pushforward Modules.pullback Hom Γ Modules.Hom Hom.image_preimage_eq_opensRange_inf preimage_basicOpen Hom.naturality basicOpen Hom.isIso_app Modules.pullbackPushforwardAdjunction Hom.preimage_image_eq Modules Opens Opens.ι_preimage_self Opens.opensRange_ι basicOpen_le Hom.image_le_opensRange PresheafOfModules toSpecΓ OrderedAffineCover Modules.Hom.epi_iff_locallySurjective Modules.Hom.mono_iff_injective Modules.exists_app_eq_of_exact_of_app_eq_zero Modules.bijective_unit_app_of_le_opensRange Modules.IsInvertible"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward pullback presheaf Hom isSheaf pullbackPushforwardAdjunction IsFrameOn Hom.epi_iff_locallySurjective Hom.mono_iff_injective exists_app_eq_of_exact_of_app_eq_zero bijective_unit_app_of_le_opensRange IsInvertible"
namespace SesAffine
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V m) = φ.app U (M.presheaf.map i.op m) := by
  have h := PresheafOfModules.Hom.naturality φ.val i.op
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) m
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'.symm

theorem comp_app_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) (m : Γ(M, U)) :
    (φ ≫ ψ).app U m = ψ.app U (φ.app U m) := rfl

theorem zero_app_apply {M N : X.Modules} (U : X.Opens) (m : Γ(M, U)) : (0 : M ⟶ N).app U m = 0 := rfl

section OpenImm

variable {X' : Scheme.{u}} (p : X' ⟶ X) [IsOpenImmersion p] (M : X.Modules)

abbrev η : M ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M

abbrev pull (V : X.Opens) (m : Γ(M, V)) : Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ V) := (η p M).app V m

theorem pull_smul (V : X.Opens) (c : Γ(X, V)) (m : Γ(M, V)) :
    pull p M V (c • m) = p.app V c • pull p M V m := by
  rw [pull, Scheme.Modules.Hom.app_smul]
  rfl

theorem pull_add (V : X.Opens) (m m' : Γ(M, V)) : pull p M V (m + m') = pull p M V m + pull p M V m' := map_add _ _ _
theorem pull_sub (V : X.Opens) (m m' : Γ(M, V)) : pull p M V (m - m') = pull p M V m - pull p M V m' := map_sub _ _ _
theorem pull_zero (V : X.Opens) : pull p M V 0 = 0 := map_zero _

theorem map_pull {U V : X.Opens} (h : U ≤ V) (m : Γ(M, V)) :
    ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE ((Opens.map p.base).monotone h)).op (pull p M V m)
      = pull p M U (M.presheaf.map (homOfLE h).op m) := by
  rw [pull, pull, ← app_naturality (η p M) (homOfLE h) m]
  rfl

theorem pull_bijective (V : X.Opens) (hV : V ≤ p.opensRange) : Function.Bijective (pull p M V) :=
  Scheme.Modules.bijective_unit_app_of_le_opensRange p M V hV

theorem app_bijective (V : X.Opens) (hV : V ≤ p.opensRange) : Function.Bijective (p.app V) := by
  haveI := Scheme.Hom.isIso_app p V hV
  exact ConcreteCategory.bijective_of_isIso (p.app V)

theorem isFrameOn_pull {V : X.Opens} (hV : V ≤ p.opensRange) (s : Γ(M, V)) (hs : IsFrameOn s V) :
    IsFrameOn (pull p M V s) (p ⁻¹ᵁ V) := by
  intro W' hW'U hW'V

  have hWV : p ''ᵁ W' ≤ V := by
    have h1 : p ''ᵁ W' ≤ p ''ᵁ p ⁻¹ᵁ V := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨y, hW'U hy, rfl⟩
    calc p ''ᵁ W' ≤ p ''ᵁ p ⁻¹ᵁ V := h1
      _ = p.opensRange ⊓ V := Scheme.Hom.image_preimage_eq_opensRange_inf p V
      _ ≤ V := inf_le_right
  have hWr : p ''ᵁ W' ≤ p.opensRange := Scheme.Hom.image_le_opensRange p W'
  have hpre : p ⁻¹ᵁ p ''ᵁ W' = W' := Scheme.Hom.preimage_image_eq p W'

  have hsq : (pull p M (p ''ᵁ W')) ∘ (fun g : Γ(X, p ''ᵁ W') => g • M.presheaf.map (homOfLE hWV).op s)
      = (fun g' : Γ(X', p ⁻¹ᵁ p ''ᵁ W') =>
          g' • ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE ((Opens.map p.base).monotone hWV)).op
            (pull p M V s)) ∘ (p.app (p ''ᵁ W')) := by
    funext g
    simp only [Function.comp_apply]
    rw [pull_smul, map_pull]
  have h1 : Function.Bijective ((pull p M (p ''ᵁ W')) ∘
      (fun g : Γ(X, p ''ᵁ W') => g • M.presheaf.map (homOfLE hWV).op s)) :=
    (pull_bijective p M _ hWr).comp (hs hWV hWV)
  rw [hsq] at h1
  have h2 := (Function.Bijective.of_comp_iff _ (app_bijective p _ hWr)).mp h1

  clear hsq h1
  revert h2
  generalize_proofs e1
  revert e1
  rw [hpre]
  intro e1 h2
  exact h2

end OpenImm

section Lifts

variable (S : ShortComplex X.Modules) (U : X.Opens)

theorem exists_lifts (hS : S.ShortExact) (hU : IsAffineOpen U) (s : Γ(S.X₃, U)) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)) (t : ∀ i, Γ(S.X₂, X.basicOpen (f i))),
      (U ≤ ⨆ i, X.basicOpen (f i)) ∧
        ∀ i, S.g.app _ (t i) = S.X₃.presheaf.map (homOfLE (X.basicOpen_le (f i))).op s := by
  classical
  have hepi : Epi S.g := hS.epi_g
  have hloc := (Scheme.Modules.Hom.epi_iff_locallySurjective S.g).mp hepi U s
  have key : ∀ x : U, ∃ (fx : Γ(X, U)) (tx : Γ(S.X₂, X.basicOpen fx)), (x : X) ∈ X.basicOpen fx ∧
      S.g.app _ tx = S.X₃.presheaf.map (homOfLE (X.basicOpen_le fx)).op s := by
    rintro ⟨x, hx⟩
    obtain ⟨V, hVU, hxV, ⟨tV, htV⟩⟩ := hloc x hx
    obtain ⟨fx, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
    refine ⟨fx, S.X₂.presheaf.map (homOfLE hfV).op tV, hxf, ?_⟩
    rw [← app_naturality, htV]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  choose fx tx hxf htx using key
  obtain ⟨T, hT⟩ := hU.isCompact.elim_finite_subcover (fun x : U => (X.basicOpen (fx x) : Set X))
    (fun _ => (X.basicOpen _).isOpen) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxf ⟨y, hy⟩⟩)
  let e := T.equivFin
  refine ⟨T.card, fun i => fx (e.symm i).1, fun i => tx (e.symm i).1, ?_, fun i => htx _⟩
  intro y hy
  obtain ⟨x, hxT, hyx⟩ : ∃ x ∈ T, y ∈ (X.basicOpen (fx x) : Set X) := by
    simpa only [Set.mem_iUnion, exists_prop] using hT hy
  refine Opens.mem_iSup.mpr ⟨e ⟨x, hxT⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hyx

variable {n : ℕ} (f : Fin n → Γ(X, U))

abbrev D (i : Fin n) : X.Opens := X.basicOpen (f i)
abbrev D2 (i j : Fin n) : X.Opens := D U f i ⊓ D U f j
abbrev D3 (i j k : Fin n) : X.Opens := D U f i ⊓ D U f j ⊓ D U f k

variable (t : ∀ i, Γ(S.X₂, D U f i))

abbrev c (i j : Fin n) : Γ(S.X₂, D2 U f i j) :=
  S.X₂.presheaf.map (homOfLE inf_le_left).op (t i) - S.X₂.presheaf.map (homOfLE inf_le_right).op (t j)

omit t in
theorem D3_le_left (i j k : Fin n) : D3 U f i j k ≤ D U f i := inf_le_left.trans inf_le_left
omit t in
theorem D3_le_mid (i j k : Fin n) : D3 U f i j k ≤ D U f j := inf_le_left.trans inf_le_right
omit t in
theorem D3_le_right (i j k : Fin n) : D3 U f i j k ≤ D U f k := inf_le_right

theorem res_c {O : X.Opens} (a b : Fin n) (h : O ≤ D2 U f a b) (ha : O ≤ D U f a) (hb : O ≤ D U f b) :
    S.X₂.presheaf.map (homOfLE h).op (c S U f t a b)
      = S.X₂.presheaf.map (homOfLE ha).op (t a) - S.X₂.presheaf.map (homOfLE hb).op (t b) := by
  rw [map_sub]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

variable (s : Γ(S.X₃, U)) (ht : ∀ i, S.g.app _ (t i) = S.X₃.presheaf.map (homOfLE (X.basicOpen_le (f i))).op s)
include ht

theorem g_c (i j : Fin n) : S.g.app _ (c S U f t i j) = 0 := by
  rw [map_sub, ← app_naturality, ← app_naturality, ht, ht]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp, sub_self]

omit ht in

theorem exists_u (hS : S.ShortExact) (hg : ∀ i j, S.g.app _ (c S U f t i j) = 0) (i j : Fin n) :
    ∃ u : Γ(S.X₁, D2 U f i j), S.f.app _ u = c S U f t i j := by
  haveI : Mono S.f := hS.mono_f
  exact Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact _ _ (hg i j)

omit ht in

theorem cocycle (hS : S.ShortExact) (u : ∀ i j, Γ(S.X₁, D2 U f i j)) (hu : ∀ i j, S.f.app _ (u i j) = c S U f t i j)
    (i j k : Fin n) :
    S.X₁.presheaf.map (homOfLE (le_inf (D3_le_mid U f i j k) (D3_le_right U f i j k))).op (u j k)
      - S.X₁.presheaf.map (homOfLE (le_inf (D3_le_left U f i j k) (D3_le_right U f i j k))).op (u i k)
      + S.X₁.presheaf.map (homOfLE (le_inf (D3_le_left U f i j k) (D3_le_mid U f i j k))).op (u i j) = 0 := by
  haveI : Mono S.f := hS.mono_f
  apply (Scheme.Modules.Hom.mono_iff_injective S.f).mp inferInstance (D3 U f i j k)
  rw [map_add, map_sub, map_zero, ← app_naturality, ← app_naturality, ← app_naturality, hu, hu, hu,
    res_c S U f t j k _ (D3_le_mid U f i j k) (D3_le_right U f i j k),
    res_c S U f t i k _ (D3_le_left U f i j k) (D3_le_right U f i j k),
    res_c S U f t i j _ (D3_le_left U f i j k) (D3_le_mid U f i j k)]
  abel

end Lifts

section Transport

variable (S : ShortComplex X.Modules) (U : X.Opens) (hU : IsAffineOpen U) {n : ℕ} (f : Fin n → Γ(X, U))
  (hcov : U ≤ ⨆ i, X.basicOpen (f i))

def cover : (U : Scheme.{u}).OrderedAffineCover where
  ι := ULift.{u} (Fin n)
  instLinearOrder := LinearOrder.lift' ULift.down ULift.down_injective
  U i := U.ι ⁻¹ᵁ D U f i.down
  isAffineOpen i := by
    rw [Scheme.preimage_basicOpen U.ι (f i.down)]
    have htop : IsAffineOpen (U.ι ⁻¹ᵁ U) := by
      rw [Scheme.Opens.ι_preimage_self]
      haveI : IsAffine (U : Scheme.{u}) := hU
      exact isAffineOpen_top _
    exact htop.basicOpen _
  iSup_eq_top := by
    apply top_unique
    intro y _
    have hy : U.ι.base y ∈ U := y.2
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hy)
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩

theorem cover_U (i : ULift.{u} (Fin n)) : (cover U hU f hcov).U i = U.ι ⁻¹ᵁ D U f i.down := rfl

abbrev F : OModulePresheaf (U : Scheme.{u}).toSpecΓ :=
  OModulePresheaf.ofModules (U : Scheme.{u}).toSpecΓ ((Scheme.Modules.pullback U.ι).obj S.X₁)

omit hU in

theorem isQuasicoherent_F
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf)) :
    (F S U).IsQuasicoherent := by
  refine OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial _ _ fun y => ?_
  have hinv : Scheme.Modules.IsInvertible S.X₁ := ⟨htriv⟩
  obtain ⟨V, sV, hxV, hfr⟩ := hinv.exists_isFrameOn (U.ι.base y)

  let V' : X.Opens := V ⊓ U
  have hV'r : V' ≤ U.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact inf_le_right
  have hfr' : IsFrameOn (S.X₁.presheaf.map (homOfLE (inf_le_left : V' ≤ V)).op sV) V' :=
    (hfr.map (homOfLE (inf_le_left : V' ≤ V))).mono inf_le_left
  have hfr'' := isFrameOn_pull U.ι S.X₁ hV'r _ hfr'
  have hy : y ∈ U.ι ⁻¹ᵁ V' := ⟨hxV, y.2⟩
  exact ⟨U.ι ⁻¹ᵁ V', hy, hfr''.nonempty_pullback_iso_unit (U.ι ⁻¹ᵁ V') le_rfl le_rfl⟩

variable (u : ∀ i j, Γ(S.X₁, D2 U f i j))

theorem inter_le_pre (σ : (cover U hU f hcov).Idx 1) :
    (cover U hU f hcov).inter σ ≤ U.ι ⁻¹ᵁ D2 U f (σ.1 0).down (σ.1 1).down := fun y hy =>
  ⟨(cover U hU f hcov).inter_le σ 0 hy, (cover U hU f hcov).inter_le σ 1 hy⟩

def u' : (F S U).cochain (cover U hU f hcov) 1 := fun σ =>
  ((Scheme.Modules.pullback U.ι).obj S.X₁).presheaf.map (homOfLE (inter_le_pre U hU f hcov σ)).op
    (pull U.ι S.X₁ (D2 U f (σ.1 0).down (σ.1 1).down) (u (σ.1 0).down (σ.1 1).down))

theorem F_res_apply {O O' : (U : Scheme.{u}).Opens} (h : O ≤ O') (x : (F S U).obj O') :
    (F S U).res h x = ((Scheme.Modules.pullback U.ι).obj S.X₁).presheaf.map (homOfLE h).op x :=
  OModulePresheaf.ofModules_res_apply _ _ h x

set_option maxHeartbeats 6400000 in

theorem res_u'_eq (τ : (cover U hU f hcov).Idx 2) (j : Fin 3) (a b : Fin n)
    (e0 : (((cover U hU f hcov).face τ j).1 0).down = a) (e1 : (((cover U hU f hcov).face τ j).1 1).down = b)
    (h3 : (cover U hU f hcov).inter τ ≤ U.ι ⁻¹ᵁ D3 U f (τ.1 0).down (τ.1 1).down (τ.1 2).down)
    (hab3 : D3 U f (τ.1 0).down (τ.1 1).down (τ.1 2).down ≤ D2 U f a b) :
    (F S U).res ((cover U hU f hcov).inter_le_inter_face τ j) (u' S U hU f hcov u ((cover U hU f hcov).face τ j))
      = ((Scheme.Modules.pullback U.ι).obj S.X₁).presheaf.map (homOfLE h3).op
          (pull U.ι S.X₁ (D3 U f (τ.1 0).down (τ.1 1).down (τ.1 2).down) (S.X₁.presheaf.map (homOfLE hab3).op (u a b))) := by
  subst e0; subst e1
  rw [F_res_apply, u', ← map_pull]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem face_val (τ : (cover U hU f hcov).Idx 2) (j : Fin 3) (k : Fin 2) :
    ((cover U hU f hcov).face τ j).1 k = τ.1 (j.succAbove k) := rfl

theorem d_u' (hcoc : ∀ i j k : Fin n,
      S.X₁.presheaf.map (homOfLE (le_inf (D3_le_mid U f i j k) (D3_le_right U f i j k))).op (u j k)
        - S.X₁.presheaf.map (homOfLE (le_inf (D3_le_left U f i j k) (D3_le_right U f i j k))).op (u i k)
        + S.X₁.presheaf.map (homOfLE (le_inf (D3_le_left U f i j k) (D3_le_mid U f i j k))).op (u i j) = 0) :
    (F S U).d (cover U hU f hcov) 1 (u' S U hU f hcov u) = 0 := by
  funext τ
  have h3 : (cover U hU f hcov).inter τ ≤ U.ι ⁻¹ᵁ D3 U f (τ.1 0).down (τ.1 1).down (τ.1 2).down := fun y hy =>
    ⟨⟨(cover U hU f hcov).inter_le τ 0 hy, (cover U hU f hcov).inter_le τ 1 hy⟩, (cover U hU f hcov).inter_le τ 2 hy⟩
  rw [OModulePresheaf.d_apply, Fin.sum_univ_three]
  rw [res_u'_eq S U hU f hcov u τ 0 (τ.1 1).down (τ.1 2).down rfl rfl h3
      (le_inf (D3_le_mid U f _ _ _) (D3_le_right U f _ _ _)),
    res_u'_eq S U hU f hcov u τ 1 (τ.1 0).down (τ.1 2).down rfl rfl h3
      (le_inf (D3_le_left U f _ _ _) (D3_le_right U f _ _ _)),
    res_u'_eq S U hU f hcov u τ 2 (τ.1 0).down (τ.1 1).down rfl rfl h3
      (le_inf (D3_le_left U f _ _ _) (D3_le_mid U f _ _ _))]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_one_smul, Pi.zero_apply]
  rw [show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_smul, ← sub_eq_add_neg]
  have key2 := congrArg (pull U.ι S.X₁ (D3 U f (τ.1 0).down (τ.1 1).down (τ.1 2).down))
    (hcoc (τ.1 0).down (τ.1 1).down (τ.1 2).down)
  rw [pull_add, pull_sub, pull_zero] at key2
  have key3 := congrArg (((Scheme.Modules.pullback U.ι).obj S.X₁).presheaf.map (homOfLE h3).op) key2
  rw [map_add, map_sub, map_zero] at key3
  exact key3

def idx0 (i : Fin n) : (cover U hU f hcov).Idx 0 :=
  ⟨fun _ => ⟨i⟩, fun a b h => absurd (Subsingleton.elim (α := Fin 1) a b) (ne_of_lt h)⟩

theorem pre_le_inter_idx0 (i : Fin n) : U.ι ⁻¹ᵁ D U f i ≤ (cover U hU f hcov).inter (idx0 U hU f hcov i) :=
  le_iInf fun _ => le_rfl

def idx1 {a b : Fin n} (hab : a < b) : (cover U hU f hcov).Idx 1 :=
  ⟨![(⟨a⟩ : ULift.{u} (Fin n)), ⟨b⟩], by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · change a < b
      exact hab
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)⟩

theorem face_idx1_zero {a b : Fin n} (hab : a < b) :
    (cover U hU f hcov).face (idx1 U hU f hcov hab) 0 = idx0 U hU f hcov b := by
  apply Subtype.ext; funext k; fin_cases k; rfl

theorem face_idx1_one {a b : Fin n} (hab : a < b) :
    (cover U hU f hcov).face (idx1 U hU f hcov hab) 1 = idx0 U hU f hcov a := by
  apply Subtype.ext; funext k; fin_cases k; rfl

theorem inter_idx1 {a b : Fin n} (hab : a < b) :
    (cover U hU f hcov).inter (idx1 U hU f hcov hab) = U.ι ⁻¹ᵁ D2 U f a b := by
  refine le_antisymm (inter_le_pre U hU f hcov _) (le_iInf fun k => ?_)
  fin_cases k
  · exact fun y hy => hy.1
  · exact fun y hy => hy.2

theorem res_at_eq (c : (F S U).cochain (cover U hU f hcov) 0) {σ τ : (cover U hU f hcov).Idx 0} (e : σ = τ)
    {O : (U : Scheme.{u}).Opens} (hσ : O ≤ (cover U hU f hcov).inter σ) (hτ : O ≤ (cover U hU f hcov).inter τ) :
    (F S U).res hσ (c σ) = (F S U).res hτ (c τ) := by
  subst e; rfl

theorem map_injective_of_eq (N : (U : Scheme.{u}).Modules) {W W' : (U : Scheme.{u}).Opens} (h : W = W') (hle : W ≤ W') :
    Function.Injective (N.presheaf.map (homOfLE hle).op) := by
  subst h
  intro a b hab
  have : (homOfLE hle) = 𝟙 W := rfl
  rw [this, op_id, N.presheaf.map_id] at hab
  exact hab

theorem exists_v (v' : (F S U).cochain (cover U hU f hcov) 0)
    (hv' : (F S U).d (cover U hU f hcov) 0 v' = u' S U hU f hcov u) :
    ∃ v : ∀ i, Γ(S.X₁, D U f i), ∀ a b : Fin n, a < b →
      u a b = S.X₁.presheaf.map (homOfLE inf_le_right).op (v b) - S.X₁.presheaf.map (homOfLE inf_le_left).op (v a) := by
  have hDr : ∀ i, D U f i ≤ U.ι.opensRange := fun i => by
    rw [Scheme.Opens.opensRange_ι]; exact X.basicOpen_le _

  let w : ∀ i, Γ((Scheme.Modules.pullback U.ι).obj S.X₁, U.ι ⁻¹ᵁ D U f i) := fun i =>
    (F S U).res (pre_le_inter_idx0 U hU f hcov i) (v' (idx0 U hU f hcov i))
  choose v hv using fun i => (pull_bijective U.ι S.X₁ (D U f i) (hDr i)).2 (w i)
  refine ⟨v, fun a b hab => ?_⟩

  have hcomp := congrFun hv' (idx1 U hU f hcov hab)
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at hcomp
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul] at hcomp
  have hle2 : (cover U hU f hcov).inter (idx1 U hU f hcov hab) ≤ U.ι ⁻¹ᵁ D2 U f a b :=
    (inter_idx1 U hU f hcov hab).le

  have hb' : (F S U).res ((cover U hU f hcov).inter_le_inter_face (idx1 U hU f hcov hab) 0)
        (v' ((cover U hU f hcov).face (idx1 U hU f hcov hab) 0))
      = ((Scheme.Modules.pullback U.ι).obj S.X₁).presheaf.map (homOfLE hle2).op
          (pull U.ι S.X₁ (D2 U f a b) (S.X₁.presheaf.map (homOfLE inf_le_right).op (v b))) := by
    rw [res_at_eq S U hU f hcov v' (face_idx1_zero U hU f hcov hab) _
      (hle2.trans (((Opens.map U.ι.base).monotone inf_le_right).trans (pre_le_inter_idx0 U hU f hcov b))),
      ← (F S U).res_res ((hle2.trans ((Opens.map U.ι.base).monotone inf_le_right))) (pre_le_inter_idx0 U hU f hcov b)]
    change (F S U).res _ (w b) = _
    rw [← hv b, F_res_apply, ← map_pull]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  have ha' : (F S U).res ((cover U hU f hcov).inter_le_inter_face (idx1 U hU f hcov hab) 1)
        (v' ((cover U hU f hcov).face (idx1 U hU f hcov hab) 1))
      = ((Scheme.Modules.pullback U.ι).obj S.X₁).presheaf.map (homOfLE hle2).op
          (pull U.ι S.X₁ (D2 U f a b) (S.X₁.presheaf.map (homOfLE inf_le_left).op (v a))) := by
    rw [res_at_eq S U hU f hcov v' (face_idx1_one U hU f hcov hab) _
      (hle2.trans (((Opens.map U.ι.base).monotone inf_le_left).trans (pre_le_inter_idx0 U hU f hcov a))),
      ← (F S U).res_res ((hle2.trans ((Opens.map U.ι.base).monotone inf_le_left))) (pre_le_inter_idx0 U hU f hcov a)]
    change (F S U).res _ (w a) = _
    rw [← hv a, F_res_apply, ← map_pull]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  rw [hb', ha'] at hcomp

  have hu' : u' S U hU f hcov u (idx1 U hU f hcov hab)
      = ((Scheme.Modules.pullback U.ι).obj S.X₁).presheaf.map (homOfLE hle2).op
          (pull U.ι S.X₁ (D2 U f a b) (u a b)) := rfl
  rw [hu', ← sub_eq_add_neg] at hcomp
  have hcomp' : ((Scheme.Modules.pullback U.ι).obj S.X₁).presheaf.map (homOfLE hle2).op
        (pull U.ι S.X₁ (D2 U f a b)
          (S.X₁.presheaf.map (homOfLE inf_le_right).op (v b) - S.X₁.presheaf.map (homOfLE inf_le_left).op (v a)))
      = ((Scheme.Modules.pullback U.ι).obj S.X₁).presheaf.map (homOfLE hle2).op
          (pull U.ι S.X₁ (D2 U f a b) (u a b)) := by
    rw [pull_sub, map_sub]
    exact hcomp
  have hinj1 := map_injective_of_eq U ((Scheme.Modules.pullback U.ι).obj S.X₁) (inter_idx1 U hU f hcov hab) hle2
  have hinj2 := (pull_bijective U.ι S.X₁ (D2 U f a b) ((inf_le_left).trans (hDr a))).1
  exact (hinj2 (hinj1 hcomp')).symm

end Transport

section Glue

variable (S : ShortComplex X.Modules) (U : X.Opens) {n : ℕ} (f : Fin n → Γ(X, U))
  (t : ∀ i, Γ(S.X₂, D U f i)) (v : ∀ i, Γ(S.X₁, D U f i)) (s : Γ(S.X₃, U))

theorem surjective_aux (hcov : U ≤ ⨆ i, X.basicOpen (f i))
    (ht : ∀ i, S.g.app _ (t i) = S.X₃.presheaf.map (homOfLE (X.basicOpen_le (f i))).op s)
    (u : ∀ i j, Γ(S.X₁, D2 U f i j)) (hu : ∀ i j, S.f.app _ (u i j) = c S U f t i j)
    (huv : ∀ a b : Fin n, a < b →
      u a b = S.X₁.presheaf.map (homOfLE inf_le_right).op (v b) - S.X₁.presheaf.map (homOfLE inf_le_left).op (v a)) :
    ∃ tU : Γ(S.X₂, U), S.g.app U tU = s := by

  let t' : ∀ i, Γ(S.X₂, D U f i) := fun i => t i + S.f.app _ (v i)

  have hlt : ∀ a b : Fin n, a < b →
      S.X₂.presheaf.map (homOfLE (inf_le_left : D2 U f a b ≤ D U f a)).op (t' a)
        = S.X₂.presheaf.map (homOfLE (inf_le_right : D2 U f a b ≤ D U f b)).op (t' b) := by
    intro a b hab
    have h1 := hu a b
    rw [huv a b hab, map_sub, ← app_naturality, ← app_naturality] at h1

    simp only [t', map_add]
    rw [sub_eq_sub_iff_add_eq_add] at h1
    exact h1.symm.trans (add_comm _ _)
  let X2sh : TopCat.Sheaf Ab X := ⟨S.X₂.presheaf, S.X₂.isSheaf⟩
  let X3sh : TopCat.Sheaf Ab X := ⟨S.X₃.presheaf, S.X₃.isSheaf⟩
  let ι : Type u := ULift.{u} (Fin n)
  let Dι : ι → X.Opens := fun i => D U f i.down
  have hcovι : U ≤ iSup Dι := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hx)
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hcompat : TopCat.Presheaf.IsCompatible X2sh.1 Dι (fun i => t' i.down) := by
    rintro ⟨a⟩ ⟨b⟩
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact hlt a b hab
    · rfl
    · have := congrArg (S.X₂.presheaf.map (homOfLE (le_of_eq (inf_comm (D U f a) (D U f b)))).op) (hlt b a hba)
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] at this
      exact this.symm
  obtain ⟨tU, htU, -⟩ := X2sh.existsUnique_gluing' Dι U (fun i => homOfLE (X.basicOpen_le (f i.down))) hcovι
    (fun i => t' i.down) hcompat
  refine ⟨tU, ?_⟩
  apply X3sh.eq_of_locally_eq' Dι U (fun i => homOfLE (X.basicOpen_le (f i.down))) hcovι
  rintro ⟨i⟩
  change S.X₃.presheaf.map _ (S.g.app U tU) = S.X₃.presheaf.map _ s
  rw [app_naturality]
  change S.g.app _ (S.X₂.presheaf.map (homOfLE (X.basicOpen_le (f i))).op tU) = _
  rw [show S.X₂.presheaf.map (homOfLE (X.basicOpen_le (f i))).op tU = t' i from htU ⟨i⟩]
  simp only [t', map_add, ht]
  rw [← comp_app_apply, S.zero, zero_app_apply, add_zero]

end Glue

theorem surjective_app (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (S.g.app U) := by
  intro s
  obtain ⟨n, f, t, hcov, ht⟩ := exists_lifts S U hS hU s
  have hg := g_c S U f t s ht
  choose u hu using exists_u S U f t hS hg
  have hcoc := cocycle S U f t hS u hu

  haveI : IsAffine (U : Scheme.{u}) := hU
  have hF := isQuasicoherent_F S U htriv
  have hd : (F S U).d (cover U hU f hcov) 1 (u' S U hU f hcov u) = 0 := d_u' S U hU f hcov u hcoc
  obtain ⟨v', hv'⟩ := OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent (F S U) hF (cover U hU f hcov) 0
    (LinearMap.mem_ker.mpr hd)
  obtain ⟨v, huv⟩ := exists_v S U hU f hcov u v' hv'
  exact surjective_aux S U f t v s hcov ht u hu huv

end AlgebraicGeometry.Scheme.Modules.SesAffine

end

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial.AlgebraicGeometry in
theorem solution
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (S.g.app U) :=
  Scheme.Modules.SesAffine.surjective_app S hS htriv U hU

end S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial (solution)
