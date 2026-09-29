-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_isPicObstructionCocycle_pullback_eq_unitPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d6ff2a4c-5e03-56fb-9458-a6a464443339

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
import Theorems.Thm_P2mOS_defect_transport_cases
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_pullback_eq_unitPullback
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace P4Crib

open Opposite TopologicalSpace

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

end P4Crib

noncomputable section

namespace P4Aux

open Opposite TopologicalSpace

section Transport

variable {X X' : Scheme.{u}} (h : X' ⟶ X) (𝒰 : X.OrderedAffineCover)

def pairIdx (p q : 𝒰.ι) (hpq : p < q) : 𝒰.Idx 1 :=
  ⟨![p, q], Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; simpa using hpq)⟩

@[scoped simp] theorem pairIdx_zero (p q : 𝒰.ι) (hpq : p < q) : (pairIdx 𝒰 p q hpq).1 0 = p := rfl
@[scoped simp] theorem pairIdx_one (p q : 𝒰.ι) (hpq : p < q) : (pairIdx 𝒰 p q hpq).1 1 = q := rfl

theorem eq_pairIdx (t : 𝒰.Idx 1) (p q : 𝒰.ι) (hpq : p < q) (h0 : t.1 0 = p) (h1 : t.1 1 = q) :
    t = pairIdx 𝒰 p q hpq := by
  apply Subtype.ext
  funext j
  fin_cases j
  · simpa using h0
  · simpa using h1

theorem le_preimage_inter_pairIdx (p q : 𝒰.ι) (hpq : p < q) (W : X'.Opens)
    (hp : W ≤ h ⁻¹ᵁ 𝒰.U p) (hq : W ≤ h ⁻¹ᵁ 𝒰.U q) : W ≤ h ⁻¹ᵁ 𝒰.inter (pairIdx 𝒰 p q hpq) := by
  change W ≤ h ⁻¹ᵁ (⨅ j, 𝒰.U ((pairIdx 𝒰 p q hpq).1 j))
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  refine le_iInf fun j => ?_
  fin_cases j
  · exact hp
  · exact hq

variable (u : ∀ s : 𝒰.Idx 1, Γ(X, 𝒰.inter s))

open Classical in

def Ugen (W : X'.Opens) (p q : 𝒰.ι) : Γ(X', W) :=
  if hpq : p < q then
    if hle : W ≤ h ⁻¹ᵁ 𝒰.inter (pairIdx 𝒰 p q hpq) then
      (h.appLE (𝒰.inter (pairIdx 𝒰 p q hpq)) W hle).hom (u (pairIdx 𝒰 p q hpq))
    else 1
  else 1

theorem Ugen_of_le (W : X'.Opens) (p q : 𝒰.ι) (hpq : p < q) (hle : W ≤ h ⁻¹ᵁ 𝒰.inter (pairIdx 𝒰 p q hpq)) :
    Ugen h 𝒰 u W p q = (h.appLE (𝒰.inter (pairIdx 𝒰 p q hpq)) W hle).hom (u (pairIdx 𝒰 p q hpq)) := by
  simp only [Ugen, dif_pos hpq, dif_pos hle]

theorem Ugen_res {W W' : X'.Opens} (hW : W ≤ W') (p q : 𝒰.ι)
    (hle : ∀ hpq : p < q, W' ≤ h ⁻¹ᵁ 𝒰.inter (pairIdx 𝒰 p q hpq)) :
    (X'.presheaf.map (homOfLE hW).op).hom (Ugen h 𝒰 u W' p q) = Ugen h 𝒰 u W p q := by
  by_cases hpq : p < q
  · rw [Ugen_of_le h 𝒰 u W' p q hpq (hle hpq), Ugen_of_le h 𝒰 u W p q hpq (hW.trans (hle hpq)),
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  · simp only [Ugen, dif_neg hpq, map_one]

variable (u' : ∀ s : 𝒰.Idx 1, Γ(X, 𝒰.inter s))

def Tgen (W : X'.Opens) (x y : 𝒰.ι) : Γ(X', W) :=
  if x < y then Ugen h 𝒰 u W x y else if x = y then 1 else Ugen h 𝒰 u' W y x

theorem Tgen_res {W W' : X'.Opens} (hW : W ≤ W') (x y : 𝒰.ι)
    (hx : W' ≤ h ⁻¹ᵁ 𝒰.U x) (hy : W' ≤ h ⁻¹ᵁ 𝒰.U y) :
    (X'.presheaf.map (homOfLE hW).op).hom (Tgen h 𝒰 u u' W' x y) = Tgen h 𝒰 u u' W x y := by
  unfold Tgen
  split_ifs with h1 h2
  · exact Ugen_res h 𝒰 u hW x y (fun hpq => le_preimage_inter_pairIdx h 𝒰 x y hpq W' hx hy)
  · exact map_one _
  · exact Ugen_res h 𝒰 u' hW y x (fun hpq => le_preimage_inter_pairIdx h 𝒰 y x hpq W' hy hx)

theorem Ugen_mul_Ugen (huu' : ∀ s : 𝒰.Idx 1, u s * u' s = 1) (W : X'.Opens) (p q : 𝒰.ι) (hpq : p < q) :
    Ugen h 𝒰 u W p q * Ugen h 𝒰 u' W p q = 1 := by
  by_cases hle : W ≤ h ⁻¹ᵁ 𝒰.inter (pairIdx 𝒰 p q hpq)
  · rw [Ugen_of_le h 𝒰 u W p q hpq hle, Ugen_of_le h 𝒰 u' W p q hpq hle, ← map_mul, huu', map_one]
  · simp only [Ugen, dif_pos hpq, dif_neg hle, mul_one]

theorem Tgen_mul_Tgen (huu' : ∀ s : 𝒰.Idx 1, u s * u' s = 1) (W : X'.Opens) (x y : 𝒰.ι) :
    Tgen h 𝒰 u u' W x y * Tgen h 𝒰 u' u W x y = 1 := by
  unfold Tgen
  split_ifs with h1 h2
  · exact Ugen_mul_Ugen h 𝒰 u u' huu' W x y h1
  · exact mul_one 1
  · rw [mul_comm]; exact Ugen_mul_Ugen h 𝒰 u u' huu' W y x (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))

end Transport

end P4Aux
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_pullback_eq_unitPullback.P4Aux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_pullback_eq_unitPullback.P4Aux"

open P4Aux P4Crib Opposite TopologicalSpace in
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
    (𝓛₀ : X₀.Modules) (c : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c) :
    ∃ c' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').cochain (𝒲.comap i') 2,
      (∀ ξ : Module.Dual k V,
        c' ξ = OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 2 (c ξ)) ∧
      IsPicObstructionCocycle V ι f' fk' i' g' 𝒲 ((Scheme.Modules.pullback h₀).obj 𝓛₀) c' := by
  classical
  obtain ⟨τ, u, u', hu, huu', hread⟩ := hc

  have hlam₀ : ∀ w, (𝒲.comap g').U w ≤ h₀ ⁻¹ᵁ (𝒰.comap g).U (lam w) := fun w => by
    show g' ⁻¹ᵁ 𝒲.U w ≤ h₀ ⁻¹ᵁ g ⁻¹ᵁ 𝒰.U (lam w)
    rw [← Scheme.Hom.comp_preimage, hh₀, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono g' (hlam w)
  obtain ⟨τ', -, hT0, hTplus, hTminus⟩ :=
    AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_refinement_transition_eq h₀ (𝒰.comap g) (𝒲.comap g')
      lam hlam₀ 𝓛₀ τ

  let c' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').cochain (𝒲.comap i') 2 :=
    (unitPullbackLin hk hfk (𝒲.comap i') (𝒰.comap i) lam hlamk 2).comp c
  have hc'eq : ∀ ξ, c' ξ = OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 2 (c ξ) :=
    fun ξ => rfl
  refine ⟨c', hc'eq, ?_⟩

  let ut : ∀ s : 𝒲.Idx 1, Γ(X', 𝒲.inter s) := fun s => Tgen h 𝒰 u u' (𝒲.inter s) (lam (s.1 0)) (lam (s.1 1))
  let ut' : ∀ s : 𝒲.Idx 1, Γ(X', 𝒲.inter s) := fun s => Tgen h 𝒰 u' u (𝒲.inter s) (lam (s.1 0)) (lam (s.1 1))

  have key : ∀ {Z : Scheme.{u}} (p q : Z ⟶ X) (hpq : p = q) (t₁ t₂ : 𝒰.Idx 1) (ht : t₁ = t₂) (W : Z.Opens)
      (x : ∀ t : 𝒰.Idx 1, Γ(X, 𝒰.inter t))
      (e₁ : W ≤ p ⁻¹ᵁ 𝒰.inter t₁) (e₂ : W ≤ q ⁻¹ᵁ 𝒰.inter t₂),
      (p.appLE (𝒰.inter t₁) W e₁).hom (x t₁) = (q.appLE (𝒰.inter t₂) W e₂).hom (x t₂) := by
    intro Z p q hpq t₁ t₂ ht W x e₁ e₂; subst hpq ht; rfl
  refine ⟨τ', ut, ut', ?_, fun s => Tgen_mul_Tgen h 𝒰 u u' huu' _ _ _, ?_⟩
  ·
    intro s
    have hs01 : s.1 0 < s.1 1 := s.2 (by decide)
    have hle0 : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.U (lam (s.1 0)) := (𝒲.inter_le s 0).trans (hlam _)
    have hle1 : 𝒲.inter s ≤ h ⁻¹ᵁ 𝒰.U (lam (s.1 1)) := (𝒲.inter_le s 1).trans (hlam _)
    change (g'.appLE (𝒲.inter s) ((𝒲.comap g').inter s) (𝒲.comap_inter_le g' s)).hom (ut s) = τ'.transition s
    rcases lt_trichotomy (lam (s.1 0)) (lam (s.1 1)) with hlt | heq | hgt
    ·
      have hinj : Function.Injective (lam ∘ s.1) := injective_pair _ hlt.ne
      have hsort : Tuple.sort (lam ∘ s.1) = Equiv.refl _ := Tuple.sort_eq_refl_iff_monotone.mpr (monotone_pair _ hlt.le)
      set σ := (𝒲.comap g').sortIdx (𝒰.comap g) lam s hinj with hσ
      have hσ0 : σ.1 0 = lam (s.1 0) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 0 = _; rw [hsort]; rfl
      have hσ1 : σ.1 1 = lam (s.1 1) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 1 = _; rw [hsort]; rfl
      have hσp : σ = pairIdx 𝒰 _ _ hlt := eq_pairIdx 𝒰 σ _ _ hlt hσ0 hσ1
      have hut : ut s = (h.appLE _ (𝒲.inter s) (le_preimage_inter_pairIdx h 𝒰 _ _ hlt _ hle0 hle1)).hom
          (u (pairIdx 𝒰 _ _ hlt)) := by
        show Tgen h 𝒰 u u' (𝒲.inter s) (lam (s.1 0)) (lam (s.1 1)) = _
        rw [Tgen, if_pos hlt, Ugen_of_le]
      rw [hut, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hTplus s hinj hlt, ← hu σ]
      change _ = (g.appLE (𝒰.inter σ) ((𝒰.comap g).inter σ) (𝒰.comap_inter_le g σ) ≫
        h₀.appLE ((𝒰.comap g).inter σ) ((𝒲.comap g').inter s)
          ((𝒲.comap g').inter_le_preimage_inter_sortIdx h₀ (𝒰.comap g) lam hlam₀ s hinj)).hom (u σ)
      rw [Scheme.Hom.appLE_comp_appLE]
      exact key _ _ hh₀.symm _ _ hσp.symm _ u _ _
    ·
      have hut : ut s = 1 := by
        show Tgen h 𝒰 u u' (𝒲.inter s) (lam (s.1 0)) (lam (s.1 1)) = 1
        rw [Tgen, if_neg (heq ▸ lt_irrefl _), if_pos heq]
      rw [hut, map_one, hT0 s heq]
    ·
      have hinj : Function.Injective (lam ∘ s.1) := injective_pair _ hgt.ne'
      have hsort : Tuple.sort (lam ∘ s.1) = Equiv.swap 0 1 := sort_pair_eq_swap _ hgt
      set σ := (𝒲.comap g').sortIdx (𝒰.comap g) lam s hinj with hσ
      have hσ0 : σ.1 0 = lam (s.1 1) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 0 = _; rw [hsort]; rfl
      have hσ1 : σ.1 1 = lam (s.1 0) := by
        show ((lam ∘ s.1) ∘ ⇑(Tuple.sort (lam ∘ s.1))) 1 = _; rw [hsort]; rfl
      have hσp : σ = pairIdx 𝒰 _ _ hgt := eq_pairIdx 𝒰 σ _ _ hgt hσ0 hσ1
      have hleP := le_preimage_inter_pairIdx h 𝒰 _ _ hgt _ hle1 hle0
      have hut : ut s = (h.appLE _ (𝒲.inter s) hleP).hom (u' (pairIdx 𝒰 _ _ hgt)) := by
        show Tgen h 𝒰 u u' (𝒲.inter s) (lam (s.1 0)) (lam (s.1 1)) = _
        rw [Tgen, if_neg (not_lt.mpr hgt.le), if_neg (ne_of_gt hgt), Ugen_of_le]

      have hB : (X₀'.presheaf.map (homOfLE ((𝒲.comap g').inter_le_preimage_inter_sortIdx h₀ (𝒰.comap g) lam hlam₀ s hinj)).op).hom
            ((h₀.app ((𝒰.comap g).inter σ)).hom (τ.transition σ)) =
          (g'.appLE (𝒲.inter s) ((𝒲.comap g').inter s) (𝒲.comap_inter_le g' s)).hom
            ((h.appLE _ (𝒲.inter s) hleP).hom (u (pairIdx 𝒰 _ _ hgt))) := by
        rw [← hu σ]
        change (g.appLE (𝒰.inter σ) ((𝒰.comap g).inter σ) (𝒰.comap_inter_le g σ) ≫
          h₀.appLE ((𝒰.comap g).inter σ) ((𝒲.comap g').inter s)
            ((𝒲.comap g').inter_le_preimage_inter_sortIdx h₀ (𝒰.comap g) lam hlam₀ s hinj)).hom (u σ) =
          (h.appLE _ (𝒲.inter s) hleP ≫ g'.appLE (𝒲.inter s) ((𝒲.comap g').inter s) (𝒲.comap_inter_le g' s)).hom
            (u (pairIdx 𝒰 _ _ hgt))
        rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact key _ _ hh₀ _ _ hσp _ u _ _
      have hT := hTminus s hinj hgt
      rw [hB] at hT
      have hAB : (g'.appLE (𝒲.inter s) ((𝒲.comap g').inter s) (𝒲.comap_inter_le g' s)).hom
            ((h.appLE _ (𝒲.inter s) hleP).hom (u' (pairIdx 𝒰 _ _ hgt))) *
          (g'.appLE (𝒲.inter s) ((𝒲.comap g').inter s) (𝒲.comap_inter_le g' s)).hom
            ((h.appLE _ (𝒲.inter s) hleP).hom (u (pairIdx 𝒰 _ _ hgt))) = 1 := by
        rw [← map_mul, ← map_mul, mul_comm, huu', map_one, map_one]
      rw [hut]
      set A := (g'.appLE (𝒲.inter s) ((𝒲.comap g').inter s) (𝒲.comap_inter_le g' s)).hom
            ((h.appLE _ (𝒲.inter s) hleP).hom (u' (pairIdx 𝒰 _ _ hgt))) with hA
      set B := (g'.appLE (𝒲.inter s) ((𝒲.comap g').inter s) (𝒲.comap_inter_le g' s)).hom
            ((h.appLE _ (𝒲.inter s) hleP).hom (u (pairIdx 𝒰 _ _ hgt))) with hB'
      calc A = A * (τ'.transition s * B) := by rw [hT, mul_one]
        _ = τ'.transition s * (A * B) := by ring
        _ = τ'.transition s := by rw [hAB, mul_one]
  ·
    intro r
    set W := 𝒲.inter r with hW

    have hleU : ∀ j : Fin 3, W ≤ h ⁻¹ᵁ 𝒰.U (lam (r.1 j)) := fun j => (𝒲.inter_le r j).trans (hlam _)
    have e2 : (X'.presheaf.map (homOfLE (𝒲.inter_le_inter_face r 2)).op).hom (ut (𝒲.face r 2)) =
        Tgen h 𝒰 u u' W (lam (r.1 0)) (lam (r.1 1)) :=
      Tgen_res h 𝒰 u u' _ _ _ ((𝒲.inter_le _ 0).trans (hlam _)) ((𝒲.inter_le _ 1).trans (hlam _))
    have e0 : (X'.presheaf.map (homOfLE (𝒲.inter_le_inter_face r 0)).op).hom (ut (𝒲.face r 0)) =
        Tgen h 𝒰 u u' W (lam (r.1 1)) (lam (r.1 2)) :=
      Tgen_res h 𝒰 u u' _ _ _ ((𝒲.inter_le _ 0).trans (hlam _)) ((𝒲.inter_le _ 1).trans (hlam _))
    have e1 : (X'.presheaf.map (homOfLE (𝒲.inter_le_inter_face r 1)).op).hom (ut' (𝒲.face r 1)) =
        Tgen h 𝒰 u' u W (lam (r.1 0)) (lam (r.1 2)) :=
      Tgen_res h 𝒰 u' u _ _ _ ((𝒲.inter_le _ 0).trans (hlam _)) ((𝒲.inter_le _ 1).trans (hlam _))
    rw [e2, e0, e1]
    have DEF := P2mOS.defect_transport_cases (Ugen h 𝒰 u W) (Ugen h 𝒰 u' W)
      (fun p q hpq => Ugen_mul_Ugen h 𝒰 u u' huu' W p q hpq) (lam ∘ r.1)
    have READ := AlgebraicGeometry.SmallExtension.isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
      V ι f' fk' i' W ((𝒲.comap i').inter r) (𝒲.comap_inter_le i' r)
    by_cases hinj : Function.Injective (lam ∘ r.1)
    ·
      set σ := Tuple.sort (lam ∘ r.1) with hσ
      set t : 𝒰.Idx 2 := 𝒲.sortIdx 𝒰 lam r hinj with ht
      have P : W ≤ h ⁻¹ᵁ 𝒰.inter t := 𝒲.inter_le_preimage_inter_sortIdx h 𝒰 lam hlam r hinj
      have ht01 : t.1 0 < t.1 1 := t.2 (by decide)
      have ht12 : t.1 1 < t.1 2 := t.2 (by decide)
      have ht02 : t.1 0 < t.1 2 := t.2 (by decide)
      have hf2 : 𝒰.face t 2 = pairIdx 𝒰 _ _ ht01 := eq_pairIdx 𝒰 _ _ _ ht01 rfl rfl
      have hf0 : 𝒰.face t 0 = pairIdx 𝒰 _ _ ht12 := eq_pairIdx 𝒰 _ _ _ ht12 rfl rfl
      have hf1 : 𝒰.face t 1 = pairIdx 𝒰 _ _ ht02 := eq_pairIdx 𝒰 _ _ _ ht02 rfl rfl
      have hPU : ∀ j : Fin 3, W ≤ h ⁻¹ᵁ 𝒰.U (t.1 j) := fun j => P.trans (Scheme.Hom.preimage_mono h (𝒰.inter_le t j))

      have hU01 : Ugen h 𝒰 u W (t.1 0) (t.1 1) =
          (h.appLE (𝒰.inter t) W P).hom ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 2)).op).hom (u (𝒰.face t 2))) := by
        rw [Ugen_of_le h 𝒰 u W _ _ ht01 (le_preimage_inter_pairIdx h 𝒰 _ _ ht01 W (hPU 0) (hPU 1)),
          ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
        exact key h h rfl _ _ hf2.symm W u _ _
      have hU12 : Ugen h 𝒰 u W (t.1 1) (t.1 2) =
          (h.appLE (𝒰.inter t) W P).hom ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 0)).op).hom (u (𝒰.face t 0))) := by
        rw [Ugen_of_le h 𝒰 u W _ _ ht12 (le_preimage_inter_pairIdx h 𝒰 _ _ ht12 W (hPU 1) (hPU 2)),
          ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
        exact key h h rfl _ _ hf0.symm W u _ _
      have hU02 : Ugen h 𝒰 u' W (t.1 0) (t.1 2) =
          (h.appLE (𝒰.inter t) W P).hom ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 1)).op).hom (u' (𝒰.face t 1))) := by
        rw [Ugen_of_le h 𝒰 u' W _ _ ht02 (le_preimage_inter_pairIdx h 𝒰 _ _ ht02 W (hPU 0) (hPU 2)),
          ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
        exact key h h rfl _ _ hf1.symm W u' _ _
      set δt : Γ(X, 𝒰.inter t) :=
        (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 2)).op).hom (u (𝒰.face t 2)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 0)).op).hom (u (𝒰.face t 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 1)).op).hom (u' (𝒰.face t 1)) - 1 with hδt
      have hD : Ugen h 𝒰 u W ((lam ∘ r.1) (σ 0)) ((lam ∘ r.1) (σ 1)) * Ugen h 𝒰 u W ((lam ∘ r.1) (σ 1)) ((lam ∘ r.1) (σ 2)) *
            Ugen h 𝒰 u' W ((lam ∘ r.1) (σ 0)) ((lam ∘ r.1) (σ 2)) - 1 = (h.appLE (𝒰.inter t) W P).hom δt := by
        change Ugen h 𝒰 u W (t.1 0) (t.1 1) * Ugen h 𝒰 u W (t.1 1) (t.1 2) * Ugen h 𝒰 u' W (t.1 0) (t.1 2) - 1 = _
        rw [hU01, hU12, hU02, hδt, map_sub, map_one, map_mul, map_mul]
      have hreadt := hread t
      have hδt2 : δt * δt = 0 := mul_self_eq_zero_of_isFibreReading V ι hJ f fk i _ _ _ _ _ hreadt
      have hD2 : (h.appLE (𝒰.inter t) W P).hom δt * (h.appLE (𝒰.inter t) W P).hom δt = 0 := by
        rw [← map_mul, hδt2, map_zero]
      have hD2' := hD2
      rw [← hD] at hD2'
      have DEF2 := DEF.2 σ t.2 hD2'
      rw [hD] at DEF2

      have hWk : (𝒲.comap i').inter r ≤ hk ⁻¹ᵁ (𝒰.comap i).inter t :=
        (𝒲.comap i').inter_le_preimage_inter_sortIdx hk (𝒰.comap i) lam hlamk r hinj
      have hsign2 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) * (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) = 1 := by
        rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
      have hread' := AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq V ι f f' fk fk' i i' h hh hk hhk hfk
        (𝒰.inter t) ((𝒰.comap i).inter t) (𝒰.comap_inter_le i t) W P ((𝒲.comap i').inter r)
        (𝒲.comap_inter_le i' r) hWk δt ((LinearMap.proj t).comp c)
        ((((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • (LinearMap.proj r).comp c')
        (fun ξ => by
          show (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) •
              OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 2 (c ξ) r = _
          rw [OModulePresheaf.unitPullback_apply_of_injective hk (𝒲.comap i') (𝒰.comap i) lam hlamk 2 (c ξ) r hinj]
          change (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • ((((Equiv.Perm.sign σ : ℤˣ) : ℤ)) •
              (hk.appLE ((𝒰.comap i).inter t) ((𝒲.comap i').inter r) hWk).hom (c ξ t)) =
            (hk.appLE ((𝒰.comap i).inter t) ((𝒲.comap i').inter r) hWk).hom (c ξ t)
          rw [smul_smul, hsign2, one_smul])
        hreadt

      have hE : Tgen h 𝒰 u u' W (lam (r.1 0)) (lam (r.1 1)) * Tgen h 𝒰 u u' W (lam (r.1 1)) (lam (r.1 2)) *
            Tgen h 𝒰 u' u W (lam (r.1 0)) (lam (r.1 2)) - 1 =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • (h.appLE (𝒰.inter t) W P).hom δt := DEF2
      have hc'r : (LinearMap.proj r).comp c' =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • ((((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • (LinearMap.proj r).comp c') := by
        rw [smul_smul, hsign2, one_smul]
      rw [hE, hc'r]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · simp only [h1, Units.val_one, one_smul] at hread' ⊢
        exact hread'
      · simp only [h1, Units.val_neg, Units.val_one, neg_smul, one_smul] at hread' ⊢
        have hn := READ.2.2.2.1 _ _ hread'
        simpa only [neg_neg] using hn
    ·
      have hE : Tgen h 𝒰 u u' W (lam (r.1 0)) (lam (r.1 1)) * Tgen h 𝒰 u u' W (lam (r.1 1)) (lam (r.1 2)) *
            Tgen h 𝒰 u' u W (lam (r.1 0)) (lam (r.1 2)) - 1 = 0 := DEF.1 hinj
      have hzero : (LinearMap.proj r).comp c' = 0 := by
        ext ξ
        show OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 2 (c ξ) r = 0
        exact OModulePresheaf.unitPullback_apply_of_not_injective hk (𝒲.comap i') (𝒰.comap i) lam hlamk 2 (c ξ) r hinj
      rw [hE, hzero]
      exact READ.1

end S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_pullback_eq_unitPullback
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_pullback_eq_unitPullback (solution)
