-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCharacters
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaCharacters
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:51:23.427621+00:00
-- url     : https://prove2.me/theorems/d940da09-45c9-59fd-8045-8a464c76d5e3
-- title:
--   Geometric Lemma Characters
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Characters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_leviProj
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRep_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_permGL_mem_blockUpper_iff
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_of_mem_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_sqrtModular_leviIncl_of_mem
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_mem_indSpace
import Theorems.Thm_GroundTheory_Automorphic_mul_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_permGL_mul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
section Diagonal
variable {γ δ : Fin n → ℕ}
theorem diagPow_mem_levi_inf_blockUpper (μ : Fin n → ℤ) :
    Cartan.diagPow F n μ ∈ levi F n γ ⊓ blockUpper F n δ :=
  ⟨diagPow_mem_levi μ, levi_le_blockUpper (diagPow_mem_levi (β := δ) μ)⟩
end Diagonal
section PermConjUnipotent
variable {γ : Fin n → ℕ}
theorem permGL_conj_apply (w : Equiv.Perm (Fin n)) (g : GL (Fin n) F) (r c : Fin n) :
    ((permGL F w * g * (permGL F w)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c =
      (g : Matrix (Fin n) (Fin n) F) (w⁻¹ r) (w⁻¹ c) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, mul_permGL_apply, permGL_mul_apply]
theorem conj_permGL_mem_unipotentRadical_iff (w : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permGL F w * g * (permGL F w)⁻¹ ∈ unipotentRadical F n (γ ∘ ⇑w⁻¹) ↔
      g ∈ unipotentRadical F n γ := by
  have hγ : (γ ∘ ⇑w⁻¹) ∘ ⇑w = γ := by
    funext i
    simp
  rw [mem_unipotentRadical, mem_unipotentRadical, conj_permGL_mem_blockUpper_iff, hγ]
  refine and_congr_right fun _ => ⟨fun h i j hij => ?_, fun h r c hrc => ?_⟩
  · have := h (w i) (w j) (by simpa using hij)
    rw [permGL_conj_apply] at this
    simpa [Matrix.one_apply] using this
  · rw [permGL_conj_apply, h _ _ hrc]
    simp [Matrix.one_apply]
end PermConjUnipotent
section CellCoinv
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
theorem leviProj_permConj_mem_unipotentRadical (a : cellUnipotent F β γ w) :
    ((leviProj F n β (permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper a)) :
      levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n (γ ∘ ⇑w⁻¹) := by
  have hx : permGL F w * (a : GL (Fin n) F) * (permGL F w)⁻¹ ∈ unipotentRadical F n (γ ∘ ⇑w⁻¹) :=
    (conj_permGL_mem_unipotentRadical_iff w).2 a.2.1
  obtain ⟨hxP, hx1⟩ := mem_unipotentRadical.1 hx
  refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · show ((leviProj F n β _ : levi F n β) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs
    · exact hxP hij
    · rfl
  · rw [leviProj_apply]
    split_ifs with hβ
    · exact hx1 i j hij
    · have hne : i ≠ j := fun e => hβ (e ▸ rfl)
      rw [Matrix.one_apply_ne hne]
theorem cellRepA_apply_eq (a : cellUnipotent F β γ w) (v : W) :
    cellRepA β γ w σ a v =
      σ (leviProj F n β (permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper a))) v := by
  rw [cellRepA, MonoidHom.coe_comp, Function.comp_apply, cellRep_apply, inflateTwist_apply]
  set p := permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper a)
  have h1 : sqrtModular F n β p = 1 := by
    rw [← sqrtModular_leviProj p]
    exact sqrtModular_leviIncl_of_mem _ (leviProj_permConj_mem_unipotentRadical a)
  rw [h1, one_smul]
variable (β γ w) in

abbrev innerJacquetSpace : Type _ :=
  Representation.Coinvariants (σ.comp (leviUnipotent F n β (γ ∘ ⇑w⁻¹)).subtype)
theorem exists_cellUnipotent_of_leviUnipotent (x : leviUnipotent F n β (γ ∘ ⇑w⁻¹)) :
    ∃ a : cellUnipotent F β γ w,
      leviProj F n β (permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper a)) = x := by
  have hxN : ((x : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n (γ ∘ ⇑w⁻¹) :=
    Subgroup.mem_subgroupOf.1 x.2
  set a := (permGL F w)⁻¹ * ((x : levi F n β) : GL (Fin n) F) * permGL F w
  have hconj : permGL F w * a * (permGL F w)⁻¹ = ((x : levi F n β) : GL (Fin n) F) := by
    simp only [a]
    group
  have haN : a ∈ unipotentRadical F n γ := by
    rw [← conj_permGL_mem_unipotentRadical_iff w, hconj]
    exact hxN
  have haP : a ∈ blockUpper F n (β ∘ w) := by
    rw [← conj_permGL_mem_blockUpper_iff w, hconj]
    exact levi_le_blockUpper (x : levi F n β).2
  refine ⟨⟨a, haN, haP⟩, ?_⟩
  apply Subtype.ext
  have : ((permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper ⟨a, haN, haP⟩) :
      blockUpper F n β) : GL (Fin n) F) = ((x : levi F n β) : GL (Fin n) F) := hconj
  have hp : permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper ⟨a, haN, haP⟩) =
      ⟨((x : levi F n β) : GL (Fin n) F), levi_le_blockUpper (x : levi F n β).2⟩ :=
    Subtype.ext this
  rw [hp, leviProj_of_mem_levi (x : levi F n β).2]
variable (β γ w) in

def cellCoinvEquiv : Representation.Coinvariants (cellRepA β γ w σ) ≃ₗ[ℂ]
    innerJacquetSpace β γ w σ where
  toFun := Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _) fun a => by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [cellRepA_apply_eq]
    exact Representation.Coinvariants.mk_self_apply
      (σ.comp (leviUnipotent F n β (γ ∘ ⇑w⁻¹)).subtype)
      ⟨_, Subgroup.mem_subgroupOf.2 (leviProj_permConj_mem_unipotentRadical a)⟩ v
  invFun := Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _) fun x => by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
      Subgroup.coe_subtype]
    obtain ⟨a, ha⟩ := exists_cellUnipotent_of_leviUnipotent (β := β) (γ := γ) (w := w) x
    rw [← ha, ← cellRepA_apply_eq]
    exact Representation.Coinvariants.mk_self_apply _ a v
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    rfl
  right_inv x := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    rfl
end CellCoinv
section InnerAction
variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
variable (β) in

def leviInfIncl (δ : Fin n → ℕ) : (levi F n β ⊓ blockUpper F n δ : Subgroup (GL (Fin n) F)) →* levi F n β where
  toFun x := ⟨x, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
theorem leviInfIncl_conj_mem {δ : Fin n → ℕ} (x : (levi F n β ⊓ blockUpper F n δ : Subgroup (GL (Fin n) F)))
    (u : leviUnipotent F n β δ) :
    leviInfIncl β δ x * (u : levi F n β) * (leviInfIncl β δ x)⁻¹ ∈ leviUnipotent F n β δ := by
  refine Subgroup.mem_subgroupOf.2 ?_
  show (x : GL (Fin n) F) * (((u : levi F n β)) : GL (Fin n) F) * (x : GL (Fin n) F)⁻¹ ∈ _
  exact conj_mem_unipotentRadical x.2.2 (Subgroup.mem_subgroupOf.1 u.2)
variable (β) in

def levJacquetAction (δ : Fin n → ℕ) :
    Representation ℂ (levi F n β ⊓ blockUpper F n δ : Subgroup (GL (Fin n) F))
      (Representation.Coinvariants (σ.comp (leviUnipotent F n β δ).subtype)) where
  toFun x := Representation.Coinvariants.lift _
    ((Representation.Coinvariants.mk _) ∘ₗ σ (leviInfIncl β δ x)) fun u => by
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp, Subgroup.coe_subtype]
      have h : σ (leviInfIncl β δ x) (σ (u : levi F n β) v) =
          σ (leviInfIncl β δ x * (u : levi F n β) * (leviInfIncl β δ x)⁻¹)
            (σ (leviInfIncl β δ x) v) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        group
      rw [h]
      exact Representation.Coinvariants.mk_self_apply
        (σ.comp (leviUnipotent F n β δ).subtype) ⟨_, leviInfIncl_conj_mem x u⟩ _
  map_one' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by simp)
  map_mul' x y := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
    simp [Module.End.mul_apply])
end InnerAction
section Compat
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
theorem leviProj_permConj_mem (b : cellLeviParabolic F β γ w) :
    ((leviProj F n β (permConj F β w (Subgroup.inclusion cellLeviParabolic_le_blockUpper b)) :
      levi F n β) : GL (Fin n) F) ∈ levi F n β ⊓ blockUpper F n (γ ∘ ⇑w⁻¹) := by
  refine ⟨(leviProj F n β _).2, fun i j hij => ?_⟩
  show ((leviProj F n β _ : levi F n β) : GL (Fin n) F) i j = 0
  rw [leviProj_apply]
  split_ifs
  · show ((permGL F w * (b : GL (Fin n) F) * (permGL F w)⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i j = 0
    rw [permGL_conj_apply]
    exact (mem_levi.1 b.2.1) _ _ fun e => (ne_of_lt hij) (by simpa using e.symm)
  · rfl
variable (β γ w) in

def cellInnerHom : cellLeviParabolic F β γ w →*
    (levi F n β ⊓ blockUpper F n (γ ∘ ⇑w⁻¹) : Subgroup (GL (Fin n) F)) where
  toFun b := ⟨_, leviProj_permConj_mem b⟩
  map_one' := Subtype.ext (by simp)
  map_mul' b b' := Subtype.ext (by simp)
end Compat
section Induced
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {ρ₁ : Representation ℂ H V₁} {ρ₂ : Representation ℂ H V₂}
def indCongr (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ h v, e (ρ₁ h v) = ρ₂ h (e v)) :
    indSpace H ρ₁ ≃ₗ[ℂ] indSpace H ρ₂ where
  toFun φ := ⟨fun g => e ((φ : G → V₁) g), by
    obtain ⟨h1, K, hK, hKφ⟩ := (mem_indSpace).1 φ.2
    exact (mem_indSpace).2 ⟨fun h g => by rw [h1 h g, he], K, hK, fun k hk g => by rw [hKφ k hk g]⟩⟩
  invFun ψ := ⟨fun g => e.symm ((ψ : G → V₂) g), by
    obtain ⟨h1, K, hK, hKψ⟩ := (mem_indSpace).1 ψ.2
    refine (mem_indSpace).2 ⟨fun h g => ?_, K, hK, fun k hk g => by rw [hKψ k hk g]⟩
    rw [h1 h g]
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩
  map_add' φ φ' := Subtype.ext (funext fun g => by simp)
  map_smul' c φ := Subtype.ext (funext fun g => by simp)
  left_inv φ := Subtype.ext (funext fun g => by simp)
  right_inv ψ := Subtype.ext (funext fun g => by simp)
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
def indTwist (χ : G →* ℂ) (hχ : ∀ g, χ g ≠ 0)
    (hχo : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, χ u = 1) :
    indSpace H ρ ≃ₗ[ℂ] indSpace H (twist (χ.comp H.subtype) ρ) where
  toFun φ := ⟨fun g => χ g • (φ : G → V) g, by
    obtain ⟨h1, K, hK, hKφ⟩ := (mem_indSpace).1 φ.2
    obtain ⟨U, hU, hUχ⟩ := hχo
    refine (mem_indSpace).2 ⟨fun h g => ?_, K ⊓ U, ?_, fun k hk g => ?_⟩
    · rw [map_mul, h1 h g, twist_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, map_smul,
        smul_smul]
    · rw [Subgroup.coe_inf]
      exact hK.inter hU
    · rw [map_mul, hUχ k hk.2, mul_one, hKφ k hk.1 g]⟩
  invFun ψ := ⟨fun g => (χ g)⁻¹ • (ψ : G → V) g, by
    obtain ⟨h1, K, hK, hKψ⟩ := (mem_indSpace).1 ψ.2
    obtain ⟨U, hU, hUχ⟩ := hχo
    refine (mem_indSpace).2 ⟨fun h g => ?_, K ⊓ U, ?_, fun k hk g => ?_⟩
    · rw [h1 h g, twist_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, smul_smul,
        map_smul]
      congr 1
      have h₁ := hχ h
      have h₂ := hχ g
      field_simp
    · rw [Subgroup.coe_inf]
      exact hK.inter hU
    · rw [map_mul, hUχ k hk.2, mul_one, hKψ k hk.1 g]⟩
  map_add' φ φ' := Subtype.ext (funext fun g => by simp)
  map_smul' c φ := Subtype.ext (funext fun g => by simp [smul_comm (χ g) c])
  left_inv φ := Subtype.ext (funext fun g => by simp [smul_smul, inv_mul_cancel₀ (hχ g)])
  right_inv ψ := Subtype.ext (funext fun g => by simp [smul_smul, mul_inv_cancel₀ (hχ g)])
end Induced
end Parabolic
end GroundTheory.Automorphic


