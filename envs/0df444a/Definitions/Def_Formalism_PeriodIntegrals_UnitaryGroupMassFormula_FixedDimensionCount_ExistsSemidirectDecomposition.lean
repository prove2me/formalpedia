-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:01.556516+00:00
-- url     : https://prove2.me/theorems/f64710d6-9577-4863-a18e-1ce8ac571b14
-- title:
--   Exists Semidirect Decomposition
-- statement:
--   Definitions and structural lemmas for Exists Semidirect Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FixedDimensionCount/ExistsSemidirectDecomposition.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Theorems.Thm_Formalism_L2_SG_ClassAct_Normalises_inv_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.DiaFixDim.Main
open Formalism.UG Formalism.L2.SG.ClassAct Module
def dk {G : Type} [Group G] (K D : Subgroup G) (hN : Normalises D K) : Subgroup G where
  carrier := {g | ∃ δ ∈ D, ∃ κ ∈ K, g = δ * κ}
  one_mem' := ⟨1, D.one_mem, 1, K.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨δ, hδ, κ, hκ, rfl⟩ ⟨δ', hδ', κ', hκ', rfl⟩
    exact ⟨δ * δ', D.mul_mem hδ hδ', (δ'⁻¹ * κ * δ') * κ',
      K.mul_mem (hN.inv_conj hδ' hκ) hκ', by group⟩
  inv_mem' := by
    rintro _ ⟨δ, hδ, κ, hκ, rfl⟩
    exact ⟨δ⁻¹, D.inv_mem hδ, δ * κ⁻¹ * δ⁻¹, hN δ hδ _ (K.inv_mem hκ), by group⟩
theorem mem_dk {G : Type} [Group G] (K D : Subgroup G) (hN : Normalises D K) {g : G} :
    g ∈ dk K D hN ↔ ∃ δ ∈ D, ∃ κ ∈ K, g = δ * κ := Iff.rfl
theorem exists_semidirect_decomposition {G : Type} [Group G] {K D : Subgroup G} {hN : Normalises D K}
    (g : dk K D hN) : ∃ p : D × K, (g : G) = (p.1 : G) * (p.2 : G) := by
  obtain ⟨δ, hδ, κ, hκ, e⟩ := (mem_dk K D hN).1 g.2
  exact ⟨(⟨δ, hδ⟩, ⟨κ, hκ⟩), e⟩
theorem chi_wd {G : Type} [Group G] {K D : Subgroup G} (k : Type) [Field k] (χ : K →* kˣ)
    (htriv : ∀ κ : K, (κ : G) ∈ D → χ κ = 1) {δ δ' : G} (hδ : δ ∈ D) (hδ' : δ' ∈ D)
    (κ κ' : K) (e : δ * (κ : G) = δ' * κ') : χ κ = χ κ' := by
  have hm : ((κ' * κ⁻¹ : K) : G) ∈ D := by
    have h2 : ((κ' * κ⁻¹ : K) : G) = δ'⁻¹ * δ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (κ' : G) * (κ : G)⁻¹ = δ'⁻¹ * (δ' * κ') * (κ : G)⁻¹ := by group
        _ = δ'⁻¹ * (δ * κ) * (κ : G)⁻¹ := by rw [← e]
        _ = δ'⁻¹ * δ := by group
    rw [h2]
    exact D.mul_mem (D.inv_mem hδ') hδ
  have h1 := htriv _ hm
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1.symm
def extendedCharacterOnQuotient {G : Type} [Group G] {K D : Subgroup G} {hN : Normalises D K} {k : Type} [Field k]
    (χ : K →* kˣ) (g : dk K D hN) : kˣ :=
  χ (Classical.choose (exists_semidirect_decomposition g)).2
theorem chi1Fun_eq {G : Type} [Group G] {K D : Subgroup G} {hN : Normalises D K} (k : Type)
    [Field k] (χ : K →* kˣ) (htriv : ∀ κ : K, (κ : G) ∈ D → χ κ = 1) (g : dk K D hN) {δ : G}
    (hδ : δ ∈ D) (κ : K) (e : (g : G) = δ * κ) : extendedCharacterOnQuotient χ g = χ κ := by
  have spec := Classical.choose_spec (exists_semidirect_decomposition g)
  exact chi_wd k χ htriv (Classical.choose (exists_semidirect_decomposition g)).1.2 hδ _ _ (spec.symm.trans e)
def chi1 {G : Type} [Group G] {K D : Subgroup G} (hN : Normalises D K) (k : Type) [Field k]
    (χ : K →* kˣ) (hinv : ∀ δ ∈ D, ∀ κ κ' : K, (κ' : G) = δ * κ * δ⁻¹ → χ κ' = χ κ)
    (htriv : ∀ κ : K, (κ : G) ∈ D → χ κ = 1) : dk K D hN →* kˣ where
  toFun := extendedCharacterOnQuotient χ
  map_one' := by
    show extendedCharacterOnQuotient χ (1 : dk K D hN) = 1
    rw [chi1Fun_eq k χ htriv 1 D.one_mem 1 (by simp), map_one]
  map_mul' g g' := by
    show extendedCharacterOnQuotient χ (g * g') = extendedCharacterOnQuotient χ g * extendedCharacterOnQuotient χ g'
    obtain ⟨δ, hδ, κ, hκ, e⟩ := (mem_dk K D hN).1 g.2
    obtain ⟨δ', hδ', κ', hκ', e'⟩ := (mem_dk K D hN).1 g'.2
    let κc : K := ⟨δ'⁻¹ * κ * δ', hN.inv_conj hδ' hκ⟩
    have hg : ((g * g' : dk K D hN) : G) = (δ * δ') * ((κc * ⟨κ', hκ'⟩ : K) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, e, e']
      show δ * κ * (δ' * κ') = δ * δ' * ((δ'⁻¹ * κ * δ') * κ')
      group
    rw [chi1Fun_eq k χ htriv _ (D.mul_mem hδ hδ') _ hg, chi1Fun_eq k χ htriv g hδ ⟨κ, hκ⟩ e,
      chi1Fun_eq k χ htriv g' hδ' ⟨κ', hκ'⟩ e', map_mul]
    congr 1
    exact hinv δ'⁻¹ (D.inv_mem hδ') ⟨κ, hκ⟩ κc
      (by show δ'⁻¹ * κ * δ' = δ'⁻¹ * κ * δ'⁻¹⁻¹; rw [inv_inv])
def phiMap {G : Type} [Group G] (Γ K D : Subgroup G) (hN : Normalises D K)
    (p : ClassSet Γ (dk K D hN) × (D ⧸ K.subgroupOf D)) : ClassSet Γ K :=
  DoubleCoset.mk Γ K (Quotient.out p.1 * ((Quotient.out p.2 : D) : G))
end PI.UnitaryGroupMassFormula.DiaFixDim.Main


