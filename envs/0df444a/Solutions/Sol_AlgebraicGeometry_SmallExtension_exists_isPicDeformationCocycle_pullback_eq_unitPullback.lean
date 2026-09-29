-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/bd4484c4-2c57-5432-b8d4-482c91847061

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE
import Theorems.Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_isUnit_transition_and_transition_face_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
p2m_open "AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace T3D4

variable {k : Type u} [Field k] {Xk Xk' : Scheme.{u}}
  {fk : Xk ⟶ Spec (CommRingCat.of k)} {fk' : Xk' ⟶ Spec (CommRingCat.of k)}

theorem unitPullback_add (hk : Xk' ⟶ Xk) (𝒲 : Xk'.OrderedAffineCover) (𝒦 : Xk.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z z' : (OModulePresheaf.unit fk).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n (z + z') =
      OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n z +
        OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n z' := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · simp only [OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj, Pi.add_apply]
    change ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom ((show ↑Γ(Xk, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z _) + (show ↑Γ(Xk, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z' _)) =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) • (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom (z _) +
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) • (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom (z' _)
    rw [map_add, smul_add]
  · simp only [OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, Pi.add_apply, add_zero]

theorem unitPullback_smul (hk : Xk' ⟶ Xk) (hfk : hk ≫ fk = fk') (𝒲 : Xk'.OrderedAffineCover) (𝒦 : Xk.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (c : k)
    (z : (OModulePresheaf.unit fk).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n (c • z) =
      c • OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n z := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · simp only [OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj, Pi.smul_apply]
    letI := algebraOfHom fk (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))
    letI := algebraOfHom fk' (𝒲.inter s)
    have hcomp : (hk.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom
        (algebraMap k _ c) = algebraMap k _ c := by
      show (hk.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom
          ((fk.appLE ⊤ _ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) =
        (fk'.appLE ⊤ _ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
      have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
        (Scheme.Hom.appLE_comp_appLE hk fk ⊤ (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) le_top
          (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [this]; subst hfk; rfl
    change ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom (algebraMap k _ c * (show ↑Γ(Xk, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z _)) =
      algebraMap k _ c * (((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (hk.appLE _ _ (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom (z _))
    rw [map_mul, hcomp, mul_smul_comm]
  · simp only [OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, Pi.smul_apply, smul_zero]

noncomputable def unitPullbackLin (hk : Xk' ⟶ Xk) (hfk : hk ≫ fk = fk') (𝒲 : Xk'.OrderedAffineCover)
    (𝒦 : Xk.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    (OModulePresheaf.unit fk).cochain 𝒦 n →ₗ[k] (OModulePresheaf.unit fk').cochain 𝒲 n where
  toFun := OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam n
  map_add' := unitPullback_add hk 𝒲 𝒦 lam hlam n
  map_smul' := unitPullback_smul hk hfk 𝒲 𝒦 lam hlam n

theorem sort_pair_eq_swap {ι : Type u} [LinearOrder ι] (f : Fin 2 → ι) (h : f 1 < f 0) : Tuple.sort f = Equiv.swap 0 1 := by
  symm
  rw [Tuple.eq_sort_iff]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · exact le_rfl
    · simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]; exact h.le
    · exact absurd hxy (by decide)
    · exact le_rfl
  · intro x y hxy hfe
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hfe; exact absurd hfe h.ne
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)

theorem injective_pair {ι : Type u} (f : Fin 2 → ι) (h : f 0 ≠ f 1) : Function.Injective f := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  · rfl
  · exact absurd hxy h
  · exact absurd hxy.symm h
  · rfl

theorem monotone_pair {ι : Type u} [Preorder ι] (f : Fin 2 → ι) (h : f 0 ≤ f 1) : Monotone f := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  · exact le_rfl
  · exact h
  · exact absurd hxy (by decide)
  · exact le_rfl

theorem unitPullback_one_of_lt (hk : Xk' ⟶ Xk) (𝒲 : Xk'.OrderedAffineCover) (𝒦 : Xk.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (z : (OModulePresheaf.unit fk).cochain 𝒦 1) (s : 𝒲.Idx 1)
    (hinj : Function.Injective (lam ∘ s.1)) (hlt : lam (s.1 0) < lam (s.1 1)) :
    OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam 1 z s =
      (hk.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom
        (z (𝒲.sortIdx 𝒦 lam s hinj)) := by
  have hsort : Tuple.sort (lam ∘ s.1) = Equiv.refl _ := Tuple.sort_eq_refl_iff_monotone.mpr (monotone_pair _ hlt.le)
  rw [OModulePresheaf.unitPullback_apply_of_injective hk 𝒲 𝒦 lam hlam 1 z s hinj, hsort, Equiv.Perm.sign_refl, Units.val_one,
    one_smul]
  rfl

theorem unitPullback_one_of_gt (hk : Xk' ⟶ Xk) (𝒲 : Xk'.OrderedAffineCover) (𝒦 : Xk.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ hk ⁻¹ᵁ 𝒦.U (lam w)) (z : (OModulePresheaf.unit fk).cochain 𝒦 1) (s : 𝒲.Idx 1)
    (hinj : Function.Injective (lam ∘ s.1)) (hgt : lam (s.1 1) < lam (s.1 0)) :
    OModulePresheaf.unitPullback (πX := fk') hk 𝒲 𝒦 lam hlam 1 z s =
      -(hk.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx hk 𝒦 lam hlam s hinj)).hom
        (z (𝒲.sortIdx 𝒦 lam s hinj)) := by
  have hsort : Tuple.sort (lam ∘ s.1) = Equiv.swap 0 1 := sort_pair_eq_swap _ hgt
  rw [OModulePresheaf.unitPullback_apply_of_injective hk 𝒲 𝒦 lam hlam 1 z s hinj, hsort,
    Equiv.Perm.sign_swap (by decide), Units.val_neg, Units.val_one, neg_smul, one_smul]
  rfl

theorem mul_self_eq_zero_of_isFibreReading {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁) (hJ : ∀ v w : V, ι v * ι w = 0)
    {X Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X)
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ : Γ(X, U))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W) (hw : IsFibreReading V ι f fk i U W hW δ w) :
    δ * δ = 0 := by
  letI := algebraOfHom f U
  obtain ⟨n, v, s, hδ, -⟩ := hw
  rw [← hδ, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
  rw [mul_mul_mul_comm, ← map_mul, hJ, map_zero, zero_mul]

end T3D4

open T3D4 in
theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    (hJ : ∀ v w : V, ι v * ι w = 0)
    {X X' X₀ X₀' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (g : X₀ ⟶ X) [IsAffineHom g] (g' : X₀' ⟶ X') [IsAffineHom g']
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) [IsAffineHom i] (i' : Xk' ⟶ X') [IsAffineHom i']
    (h : X' ⟶ X) (hh : h ≫ f = f')
    (h₀ : X₀' ⟶ X₀) (hh₀ : h₀ ≫ g = g' ≫ h)
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')
    (𝒰 : X.OrderedAffineCover) (𝒲 : X'.OrderedAffineCover) (lam : 𝒲.ι → 𝒰.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒰.U (lam w))
    (hlamk : ∀ w, (𝒲.comap i').U w ≤ hk ⁻¹ᵁ (𝒰.comap i).U (lam w))
    (M : X.Modules) (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    ∃ w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').cochain (𝒲.comap i') 1,
      (∀ ξ : Module.Dual k V,
        w' ξ = OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ)) ∧
      IsPicDeformationCocycle V ι f' fk' i' g' 𝒲 ((Scheme.Modules.pullback h).obj M)
        (((Scheme.Modules.pullbackComp g' h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr hh₀.symm).app M) ≪≫
          ((Scheme.Modules.pullbackComp h₀ g).app M).symm ≪≫
          (Scheme.Modules.pullback h₀).mapIso φ₀ ≪≫
          Scheme.Modules.pullbackUnitIso h₀)
        w' := by
  classical
  obtain ⟨τ, e, e', hee', hdisc, hread⟩ := hw
  obtain ⟨τ', hτ'chart, hT0, hTplus, hTminus⟩ := AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_refinement_transition_eq h 𝒰 𝒲 lam hlam M τ

  let w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').cochain (𝒲.comap i') 1 :=
    (unitPullbackLin hk hfk (𝒲.comap i') (𝒰.comap i) lam hlamk 1).comp w
  have hw'eq : ∀ ξ, w' ξ = OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ) :=
    fun ξ => rfl
  refine ⟨w', hw'eq, ?_⟩

  let E : ∀ a : 𝒲.ι, Γ(X', 𝒲.U a) := fun a => (h.appLE (𝒰.U (lam a)) (𝒲.U a) (hlam a)).hom (e (lam a))
  let E' : ∀ a : 𝒲.ι, Γ(X', 𝒲.U a) := fun a => (h.appLE (𝒰.U (lam a)) (𝒲.U a) (hlam a)).hom (e' (lam a))
  refine ⟨τ', E, E', fun a => by simp only [E, E', ← map_mul, hee', map_one], ?_, ?_⟩
  ·
    intro a
    rw [AlgebraicGeometry.Scheme.Modules.unitAutSection_comap_refinement_eq_appLE g g' h h₀ hh₀ 𝒰 𝒲 lam hlam M τ τ' a (hτ'chart a) φ₀, ← hdisc (lam a)]
    show ((h.appLE (𝒰.U (lam a)) (𝒲.U a) (hlam a)) ≫ g'.app (𝒲.U a)).hom (e (lam a)) =
      (g.app (𝒰.U (lam a)) ≫ h₀.appLE _ _ _).hom (e (lam a))
    rw [Scheme.Hom.app_eq_appLE g', Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE g, Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (p q : X₀' ⟶ X) (hpq : p = q) (e₁ : g' ⁻¹ᵁ 𝒲.U a ≤ p ⁻¹ᵁ 𝒰.U (lam a))
        (e₂ : g' ⁻¹ᵁ 𝒲.U a ≤ q ⁻¹ᵁ 𝒰.U (lam a)),
        (p.appLE (𝒰.U (lam a)) _ e₁).hom (e (lam a)) = (q.appLE (𝒰.U (lam a)) _ e₂).hom (e (lam a)) := by
      intro p q hpq e₁ e₂; subst hpq; rfl
    exact key _ _ hh₀.symm _ _
  ·
    intro s

    have resE : ∀ (c : 𝒰.ι) (x : Γ(X, 𝒰.U c)) (j : Fin 2) (p : 𝒲.U (s.1 j) ≤ h ⁻¹ᵁ 𝒰.U c),
        (X'.presheaf.map (homOfLE (𝒲.inter_le s j)).op).hom ((h.appLE (𝒰.U c) (𝒲.U (s.1 j)) p).hom x) =
          (h.appLE (𝒰.U c) (𝒲.inter s) ((𝒲.inter_le s j).trans p)).hom x := by
      intro c x j p
      exact congrArg (fun q => q.hom x) (Scheme.Hom.appLE_map h p (homOfLE (𝒲.inter_le s j)).op)

    have keyE : ∀ (c d : 𝒰.ι) (hcd : c = d) (x : ∀ a, Γ(X, 𝒰.U a)) (p : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.U c) (q : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.U d),
        (h.appLE (𝒰.U c) (𝒲.inter s) p).hom (x c) = (h.appLE (𝒰.U d) (𝒲.inter s) q).hom (x d) := by
      intro c d hcd x p q; subst hcd; rfl
    have hs01 : s.1 0 < s.1 1 := s.2 (by decide)
    rw [resE (lam (s.1 0)) (e' (lam (s.1 0))) 0 (hlam _), resE (lam (s.1 1)) (e (lam (s.1 1))) 1 (hlam _)]
    rcases lt_trichotomy (lam (s.1 0)) (lam (s.1 1)) with hlt | heq | hgt
    ·
      have hinj : Function.Injective (lam ∘ s.1) := injective_pair _ hlt.ne
      have hsort : Tuple.sort (lam ∘ s.1) = Equiv.refl _ := Tuple.sort_eq_refl_iff_monotone.mpr (monotone_pair _ hlt.le)
      set σ := 𝒲.sortIdx 𝒰 lam s hinj with hσ
      have hσ0 : σ.1 0 = lam (s.1 0) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 0 = _; rw [hsort]; rfl
      have hσ1 : σ.1 1 = lam (s.1 1) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 1 = _; rw [hsort]; rfl
      have P : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.inter σ := 𝒲.inter_le_preimage_inter_sortIdx h 𝒰 lam hlam s hinj
      have hread' := AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq V ι f f' fk fk' i i' h hh hk hhk hfk
        (𝒰.inter σ) ((𝒰.comap i).inter σ) (𝒰.comap_inter_le i σ) (𝒲.inter s) P ((𝒲.comap i').inter s)
        (𝒲.comap_inter_le i' s) ((𝒲.comap i').inter_le_preimage_inter_sortIdx hk (𝒰.comap i) lam hlamk s hinj)
        _ ((LinearMap.proj σ).comp w) ((LinearMap.proj s).comp w')
        (fun ξ => unitPullback_one_of_lt hk (𝒲.comap i') (𝒰.comap i) lam hlamk (w ξ) s hinj hlt) (hread σ)
      convert hread' using 2
      rw [hTplus s hinj hlt, map_sub, map_one, map_mul, map_mul]
      change _ = (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom (τ.transition σ) *
        (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom ((X.presheaf.map (homOfLE (𝒰.inter_le σ 0)).op).hom (e' (σ.1 0))) *
        (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom ((X.presheaf.map (homOfLE (𝒰.inter_le σ 1)).op).hom (e (σ.1 1))) - 1
      have r0 := congrArg (fun q => q.hom (e' (σ.1 0))) (Scheme.Hom.map_appLE h P (homOfLE (𝒰.inter_le σ 0)).op)
      have r1 := congrArg (fun q => q.hom (e (σ.1 1))) (Scheme.Hom.map_appLE h P (homOfLE (𝒰.inter_le σ 1)).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at r0 r1
      rw [r0, r1, keyE _ _ hσ0 e' _ ((𝒲.inter_le s 0).trans (hlam _)), keyE _ _ hσ1 e _ ((𝒲.inter_le s 1).trans (hlam _))]
      rfl
    ·
      have hninj : ¬ Function.Injective (lam ∘ s.1) := fun hinj => absurd (hinj heq) (by decide)
      have hzero : (LinearMap.proj s).comp w' = 0 := by
        ext ξ
        show OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ) s = 0
        exact OModulePresheaf.unitPullback_apply_of_not_injective hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ) s hninj
      rw [hzero, hT0 s heq, one_mul]
      have hone : (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
          (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) = 1 := by
        rw [keyE _ _ heq.symm e ((𝒲.inter_le s 1).trans (hlam _)) ((𝒲.inter_le s 0).trans (hlam _)), ← map_mul,
          mul_comm, hee', map_one]
      rw [hone, sub_self]
      exact (AlgebraicGeometry.SmallExtension.isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading V ι f' fk' i' (𝒲.inter s) ((𝒲.comap i').inter s) (𝒲.comap_inter_le i' s)).1
    ·
      have hinj : Function.Injective (lam ∘ s.1) := injective_pair _ hgt.ne'
      have hsort : Tuple.sort (lam ∘ s.1) = Equiv.swap 0 1 := sort_pair_eq_swap _ hgt
      set σ := 𝒲.sortIdx 𝒰 lam s hinj with hσ
      have hσ0 : σ.1 0 = lam (s.1 1) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 0 = _; rw [hsort]; rfl
      have hσ1 : σ.1 1 = lam (s.1 0) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 1 = _; rw [hsort]; rfl
      have P : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.inter σ := 𝒲.inter_le_preimage_inter_sortIdx h 𝒰 lam hlam s hinj

      have hread' := AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq V ι f f' fk fk' i i' h hh hk hhk hfk
        (𝒰.inter σ) ((𝒰.comap i).inter σ) (𝒰.comap_inter_le i σ) (𝒲.inter s) P ((𝒲.comap i').inter s)
        (𝒲.comap_inter_le i' s) ((𝒲.comap i').inter_le_preimage_inter_sortIdx hk (𝒰.comap i) lam hlamk s hinj)
        _ ((LinearMap.proj σ).comp w) (-((LinearMap.proj s).comp w'))
        (fun ξ => by
          show -(OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ) s) = _
          rw [unitPullback_one_of_gt hk (𝒲.comap i') (𝒰.comap i) lam hlamk (w ξ) s hinj hgt]
          exact neg_neg _) (hread σ)
      have hneg := ((AlgebraicGeometry.SmallExtension.isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading V ι f' fk' i' (𝒲.inter s) ((𝒲.comap i').inter s)
        (𝒲.comap_inter_le i' s)).2.2.2.1 _ _ hread')
      rw [neg_neg] at hneg

      have hD2 := mul_self_eq_zero_of_isFibreReading V ι hJ f' fk' i' _ _ _ _ _ hread'
      set D : Γ(X', 𝒲.inter s) := ((h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom
        (τ.transition σ * (X.presheaf.map (homOfLE (𝒰.inter_le σ 0)).op).hom (e' (σ.1 0)) *
          (X.presheaf.map (homOfLE (𝒰.inter_le σ 1)).op).hom (e (σ.1 1)) - 1)) with hD
      have r0 := congrArg (fun q => q.hom (e' (σ.1 0))) (Scheme.Hom.map_appLE h P (homOfLE (𝒰.inter_le σ 0)).op)
      have r1 := congrArg (fun q => q.hom (e (σ.1 1))) (Scheme.Hom.map_appLE h P (homOfLE (𝒰.inter_le σ 1)).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at r0 r1
      have hD' : 1 + D = (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom (τ.transition σ) *
          (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e' (lam (s.1 1))) *
          (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e (lam (s.1 0))) := by
        rw [hD, map_sub, map_one, map_mul, map_mul, r0, r1,
          keyE _ _ hσ0 e' _ ((𝒲.inter_le s 1).trans (hlam _)), keyE _ _ hσ1 e _ ((𝒲.inter_le s 0).trans (hlam _))]
        abel
      have hprod : (1 + (τ'.transition s *
            (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
            (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) - 1)) *
          (1 + D) = 1 := by
        rw [hD']
        have hT := hTminus s hinj hgt
        have h0 : (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
            (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e (lam (s.1 0))) = 1 := by
          rw [← map_mul, mul_comm, hee', map_one]
        have h1 : (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) *
            (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e' (lam (s.1 1))) = 1 := by
          rw [← map_mul, hee', map_one]
        have hT' : τ'.transition s * (h.appLE (𝒰.inter σ) (𝒲.inter s) P).hom (τ.transition σ) = 1 := hT
        linear_combination ((h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) * (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) * (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e' (lam (s.1 1))) * (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e (lam (s.1 0)))) * hT' +
          ((h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) * (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e (lam (s.1 0)))) * h1 + h0
      have hinv : (1 + D) * (1 - D) = 1 := by linear_combination (-1 : _) * hD2
      have hδ' : τ'.transition s *
            (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
            (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) - 1 = -D := by
        linear_combination (1 - D) * hprod + (1 + (τ'.transition s *
            (h.appLE (𝒰.U (lam (s.1 0))) (𝒲.inter s) ((𝒲.inter_le s 0).trans (hlam _))).hom (e' (lam (s.1 0))) *
            (h.appLE (𝒰.U (lam (s.1 1))) (𝒲.inter s) ((𝒲.inter_le s 1).trans (hlam _))).hom (e (lam (s.1 1))) - 1)) * hD2
      rw [hδ']
      exact hneg

end S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback (solution)
