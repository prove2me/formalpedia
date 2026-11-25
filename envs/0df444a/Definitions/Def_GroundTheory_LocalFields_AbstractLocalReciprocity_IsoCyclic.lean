-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:39.391348+00:00
-- url     : https://prove2.me/theorems/79546090-3dcb-54aa-8747-573bfc4868f2
-- title:
--   Iso Cyclic
-- statement:
--   Definitions and structural lemmas for Iso Cyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoCyclic.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_field_eq
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_deg_eq
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_frobeniusLift_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_mk_eq_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relInertiaDegree_ne_zero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_smul_prod_pow_div
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_tateZeroVal_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_toAdd_deg_mem_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_eq_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm_prime
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_of_mem
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_pow
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_dvd_of_intCast_eq_nsmul
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_eq_of_mul_eq
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_eq_prod_smul_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti
import Theorems.Thm_GroundTheory_LocalField_Abstract_inertiaDegree_eq_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_norm_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule_of_normal
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_norm_of_map_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk


set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
open ProfiniteInteger
section Augmentation
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
theorem exists_eq_smul_div_of_mem_augmentation_of_generator {K L : Subgroup G} (hLK : L ≤ K)
    [(L.subgroupOf K).Normal] {τ : G} (hτ : τ ∈ K) (hgen : ∀ g ∈ K, ∃ m : ℕ, (τ ^ m)⁻¹ * g ∈ L)
    {x : A} (hx : x ∈ augmentation A K L) : ∃ b ∈ fixedModule A L, x = τ • b / b := by

  let S : Subgroup A :=
    { carrier := {y | ∃ b ∈ fixedModule A L, y = τ • b / b}
      one_mem' := ⟨1, Subgroup.one_mem _, by rw [smul_one, div_one]⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b * c, Subgroup.mul_mem _ hb hc, by rw [smul_mul', mul_div_mul_comm]⟩
      inv_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b⁻¹, Subgroup.inv_mem _ hb, by rw [smul_inv', inv_div_inv, inv_div]⟩ }

  let T : Subgroup K :=
    { carrier := {g | ∀ a ∈ fixedModule A L, (g : G) • a / a ∈ S}
      one_mem' := fun a _ => by
        rw [OneMemClass.coe_one, one_smul, div_self']
        exact S.one_mem
      mul_mem' := by
        intro g h hg hh a ha
        have hha : (h : G) • a ∈ fixedModule A L := smul_mem_fixedModule_of_normal hLK h.2 ha
        have e : ((g * h : K) : G) • a / a = ((g : G) • ((h : G) • a) / ((h : G) • a)) * ((h : G) • a / a) := by
          rw [Subgroup.coe_mul, mul_smul]
          simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact S.mul_mem (hg _ hha) (hh a ha)
      inv_mem' := by
        intro g hg a ha
        have hga : ((g⁻¹ : K) : G) • a ∈ fixedModule A L :=
          smul_mem_fixedModule_of_normal hLK (g⁻¹).2 ha
        have e : ((g⁻¹ : K) : G) • a / a =
            ((g : G) • (((g⁻¹ : K) : G) • a) / (((g⁻¹ : K) : G) • a))⁻¹ := by
          rw [smul_smul, InvMemClass.coe_inv, mul_inv_cancel, one_smul, inv_div]
        rw [e]
        exact S.inv_mem (hg _ hga) }
  have hτT : (⟨τ, hτ⟩ : K) ∈ T := fun a ha => ⟨a, ha, rfl⟩
  have hLT : ∀ ρ : K, (ρ : G) ∈ L → ρ ∈ T := fun ρ hρ a ha => by
    rw [ha ρ hρ, div_self']
    exact S.one_mem
  have hTop : ∀ g : K, g ∈ T := by
    intro g
    obtain ⟨m, hm⟩ := hgen g g.2
    have hg : g = (⟨τ, hτ⟩ : K) ^ m * (((⟨τ, hτ⟩ : K) ^ m)⁻¹ * g) := by group
    rw [hg]
    exact T.mul_mem (T.pow_mem hτT m) (hLT _ (by simpa using hm))
  have hle : augmentation A K L ≤ S := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, a, ha, rfl⟩
    exact hTop ⟨g, hg⟩ a ha
  exact hle hx
end Augmentation
theorem exists_pow_eq_of_exists_zpow_eq {α : Type*} [Group α] [Finite α] {g x : α}
    (h : ∃ n : ℤ, g ^ n = x) : ∃ k : ℕ, g ^ k = x := by
  have hx : x ∈ Subgroup.zpowers g := Subgroup.mem_zpowers_iff.2 h
  rw [← mem_powers_iff_mem_zpowers] at hx
  exact (Submonoid.mem_powers_iff _ _).1 hx
namespace ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}
section Galois
omit [TotallyDisconnectedSpace G] in

theorem valuation_smul_of_map_eq (S : OpenSubgroup G) {g : G}
    (hg : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = S) (a : fixedModule A (S : Subgroup G))
    (hga : g • (a : A) ∈ fixedModule A (S : Subgroup G)) :
    D.valuation S ⟨g • (a : A), hga⟩ = D.valuation S a := by
  rw [valuation_eq_iff, valuation_pow]
  congr 1
  ext
  have htop : (⊤ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  have h := smul_norm_of_map_eq (A := A) g htop hg a
  refine h.symm.trans ?_
  exact (norm A ⊤ (S : Subgroup G) a).2 g trivial
variable {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G] in

theorem commutator_mem_of_isCyclic [((L : Subgroup G).subgroupOf K).Normal]
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) {a b : G}
    (ha : a ∈ (K : Subgroup G)) (hb : b ∈ (K : Subgroup G)) :
    a⁻¹ * b⁻¹ * a * b ∈ (L : Subgroup G) ⊓ D.deg.ker := by
  refine Subgroup.mem_inf.2 ⟨?_, MonoidHom.mem_ker.2 ?_⟩
  · have := hcyc
    have hc : ((⟨b, hb⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) *
        ((⟨a, ha⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        ((⟨a, ha⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) *
        ((⟨b, hb⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
      IsCyclic.commGroup.mul_comm _ _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hc
    simpa [mul_assoc] using hc
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_right_comm (D.deg a)⁻¹, inv_mul_cancel, one_mul, inv_mul_cancel]
omit [TotallyDisconnectedSpace G] in

theorem conj_mem_of_isCyclic [((L : Subgroup G).subgroupOf K).Normal]
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) {H : Subgroup G}
    (hH : (L : Subgroup G) ⊓ D.deg.ker ≤ H) {g h : G} (hg : g ∈ (K : Subgroup G))
    (hh : h ∈ (K : Subgroup G)) (hhH : h ∈ H) : g * h * g⁻¹ ∈ H := by
  have hc := commutator_mem_of_isCyclic (D := D) hcyc hh (K.inv_mem hg)
  have e : g * h * g⁻¹ = h * (h⁻¹ * g⁻¹⁻¹ * h * g⁻¹) := by group
  rw [e]
  exact H.mul_mem hhH (hH hc)
end Galois
section Hull
variable (D) in

def maxUnramified (K L : OpenSubgroup G) : OpenSubgroup G where
  toSubgroup := (K : Subgroup G) ⊓ ((L : Subgroup G).map D.deg).comap D.deg
  isOpen' := Subgroup.isOpen_mono (H₁ := ((K ⊓ L : OpenSubgroup G) : Subgroup G))
    (fun x hx => ⟨hx.1, x, hx.2, rfl⟩) (K ⊓ L).isOpen
variable {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G] in
theorem mem_maxUnramified {g : G} :
    g ∈ (D.maxUnramified K L : Subgroup G) ↔
      g ∈ (K : Subgroup G) ∧ ∃ l ∈ (L : Subgroup G), D.deg l = D.deg g :=
  Iff.rfl
omit [TotallyDisconnectedSpace G] in
theorem maxUnramified_le : D.maxUnramified K L ≤ K := fun _ hx => hx.1
omit [TotallyDisconnectedSpace G] in
theorem le_maxUnramified (hLK : L ≤ K) : L ≤ D.maxUnramified K L :=
  fun x hx => ⟨hLK hx, x, hx, rfl⟩
omit [TotallyDisconnectedSpace G] in

theorem inf_ker_le_maxUnramified :
    (K : Subgroup G) ⊓ D.deg.ker ≤ (D.maxUnramified K L : Subgroup G) :=
  fun x hx => ⟨hx.1, 1, (L : Subgroup G).one_mem, by rw [map_one, (MonoidHom.mem_ker.1 hx.2)]⟩
omit [TotallyDisconnectedSpace G] in

theorem relInertiaDegree_maxUnramified :
    relInertiaDegree D.deg (D.maxUnramified K L) L = 1 := by
  rw [relInertiaDegree, Subgroup.relIndex_eq_one]
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨l, hl, e⟩ := hg.2
  exact ⟨l, hl, e⟩
end Hull
section Unramified
variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
end Unramified
section TotallyRamified
variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
theorem reciprocity_injective_of_totallyRamified
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
    (htot : relInertiaDegree D.deg K L = 1) : Function.Injective (D.reciprocity hLK hax) := by

  have hdeg : ∀ k ∈ (K : Subgroup G), ∃ l ∈ (L : Subgroup G), D.deg l = D.deg k := by
    intro k hk
    obtain ⟨l, hl, e⟩ := (Subgroup.relIndex_eq_one.1 htot) ⟨k, hk, rfl⟩
    exact ⟨l, hl, e⟩

  obtain ⟨φ0, hφ0K, hdφ0⟩ := D.exists_deg_eq K
  obtain ⟨φ, hφL, hdφ⟩ := hdeg φ0 hφ0K

  have := hcyc
  obtain ⟨γ, hγ⟩ := exists_zpow_surjective ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective γ
  obtain ⟨l0, hl0L, hl0⟩ := hdeg g0 g0.2
  obtain ⟨τ, hτdef⟩ : ∃ τ : G, τ = (g0 : G) * l0⁻¹ := ⟨_, rfl⟩
  have hτK : τ ∈ (K : Subgroup G) := hτdef ▸ K.mul_mem g0.2 (K.inv_mem (hLK hl0L))
  have hτker : D.deg τ = 1 := by rw [hτdef, map_mul, map_inv, hl0, mul_inv_cancel]
  have hτγ : (((⟨τ, hτK⟩ : (K : Subgroup G))) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (g0 : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hτdef, mul_assoc] using hl0L
  have hpow : ∀ q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K, ∃ m : ℕ,
      (((⟨τ, hτK⟩ : (K : Subgroup G))) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ m = q := by
    intro q
    rw [hτγ]
    exact exists_pow_eq_of_exists_zpow_eq (hγ q)
  have hgen : ∀ k ∈ (K : Subgroup G), ∃ m : ℕ, (τ ^ m)⁻¹ * k ∈ (L : Subgroup G) := by
    intro k hk
    obtain ⟨m, hm⟩ := hpow (⟨k, hk⟩ : (K : Subgroup G))
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hm
    simpa using hm
  rw [injective_iff_map_eq_one]
  intro σ hσ
  obtain ⟨k, rfl⟩ := hpow σ
  rw [← QuotientGroup.mk_pow] at hσ ⊢

  obtain ⟨s, hs_elt, hs_deg⟩ : ∃ s : D.FrobeniusLift K, s.elt = τ ^ k * φ ∧ s.deg = 1 :=
    ⟨{ elt := τ ^ k * φ
       mem := K.mul_mem (K.pow_mem hτK k) (hLK hφL)
       deg := 1
       deg_pos := one_pos
       deg_eq := by rw [map_mul, map_pow, hτker, one_pow, one_mul, hdφ, hdφ0, one_mul] }, rfl, rfl⟩
  have hs : ((((⟨τ, hτK⟩ : (K : Subgroup G)) ^ k : (K : Subgroup G))) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hs_elt] using hφL
  rw [hs] at hσ
  obtain ⟨π0, hπ0⟩ := D.exists_prime (s.field L hLK)
  rw [reciprocity_mk_eq_norm hLK hax s hπ0, QuotientGroup.eq_one_iff] at hσ
  obtain ⟨b, hb⟩ := hσ

  have hvb : D.valuation L b = Multiplicative.ofAdd 1 := by
    have h1 := D.valuation_norm hLK b
    rw [htot, pow_one, hb, valuation_norm_prime hLK s hπ0, hs_deg, Nat.cast_one] at h1
    exact h1.symm

  obtain ⟨L1, hL1L, hL1S, hIL⟩ : ∃ L1 : OpenSubgroup G, L1 ≤ L ∧ L1 ≤ s.field L hLK ∧
      (L : Subgroup G) ⊓ D.deg.ker ≤ L1 :=
    ⟨L ⊓ s.field L hLK, inf_le_left, inf_le_right, fun x hx => ⟨hx.1, le_frobeniusClosure hx⟩⟩
  have hL1K : L1 ≤ K := hL1L.trans hLK
  obtain ⟨K1, hL1K1, hK1K, hIK1, hK1deg⟩ : ∃ K1 : OpenSubgroup G, L1 ≤ K1 ∧ K1 ≤ K ∧
      (K : Subgroup G) ⊓ D.deg.ker ≤ K1 ∧
      ∀ g ∈ (K1 : Subgroup G), ∃ l ∈ (L1 : Subgroup G), D.deg l = D.deg g :=
    ⟨D.maxUnramified K L1, le_maxUnramified hL1K, maxUnramified_le, inf_ker_le_maxUnramified,
      fun g hg => (mem_maxUnramified.1 hg).2⟩

  have hconj : ∀ g ∈ (K : Subgroup G), ∀ h ∈ (L1 : Subgroup G), g * h * g⁻¹ ∈ (L1 : Subgroup G) :=
    fun g hg h hh => conj_mem_of_isCyclic (D := D) hcyc hIL hg (hL1K hh) hh
  have hmapL1 : ∀ g ∈ (K : Subgroup G),
      (L1 : Subgroup G).map (MulAut.conj g).toMonoidHom = L1 := by
    intro g hg
    refine le_antisymm ?_ fun h hh => ⟨g⁻¹ * h * g, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩
      exact hconj g hg h hh
    · simpa using hconj g⁻¹ (K.inv_mem hg) h hh
    · simp [MulAut.conj_apply, mul_assoc]
  have hsmulL1 : ∀ g ∈ (K : Subgroup G), ∀ a ∈ fixedModule A (L1 : Subgroup G),
      g • a ∈ fixedModule A (L1 : Subgroup G) := by
    intro g hg a ha h hh
    have hc : g⁻¹ * h * g ∈ (L1 : Subgroup G) := by simpa using hconj g⁻¹ (K.inv_mem hg) h hh
    calc h • g • a = g • (g⁻¹ * h * g) • a := by
          rw [smul_smul, smul_smul]
          congr 1
          group
      _ = g • a := by rw [ha _ hc]
  have hN1 : ((L1 : Subgroup G).subgroupOf K1).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hconj g (hK1K g.2) n hn⟩

  have hτK1 : τ ∈ (K1 : Subgroup G) := hIK1 (Subgroup.mem_inf.2 ⟨hτK, MonoidHom.mem_ker.2 hτker⟩)
  have hgen1 : ∀ g ∈ (K1 : Subgroup G), ∃ m : ℕ, (τ ^ m)⁻¹ * g ∈ (L1 : Subgroup G) := by
    intro g hg
    obtain ⟨l, hl, hdl⟩ := hK1deg g hg
    obtain ⟨m, hm⟩ := hgen (g * l⁻¹) (K.mul_mem (hK1K hg) (K.inv_mem (hL1K hl)))
    refine ⟨m, ?_⟩
    have hker : (τ ^ m)⁻¹ * (g * l⁻¹) ∈ D.deg.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hτker, one_pow, inv_one, one_mul, map_mul,
        map_inv, hdl, mul_inv_cancel]
    have h := (L1 : Subgroup G).mul_mem (hIL (Subgroup.mem_inf.2 ⟨hm, hker⟩)) hl
    simpa [mul_assoc] using h
  have hcyc1 : IsCyclic ((K1 : Subgroup G) ⧸ (L1 : Subgroup G).subgroupOf K1) := by
    refine ⟨⟨((⟨τ, hτK1⟩ : (K1 : Subgroup G)) : (K1 : Subgroup G) ⧸ (L1 : Subgroup G).subgroupOf K1),
      fun q => ?_⟩⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨m, hm⟩ := hgen1 g g.2
      refine ⟨m, ?_⟩
      show _ ^ ((m : ℕ) : ℤ) = _
      rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hm

  have hNS : (norm A (K : Subgroup G) (s.field L hLK : Subgroup G) π0 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨π0, fixedModule_anti le_frobeniusClosure π0.2⟩ : A) := by
    rw [coe_norm_field_eq hLK s hφ0K hdφ0 π0, Fintype.prod_eq_single
      (⟨0, by rw [hs_deg]; exact one_pos⟩ : Fin s.deg) (fun ν hν => absurd (Fin.ext (by
        have := ν.2
        omega)) hν), Fin.val_mk, pow_zero, one_smul]
  have hNL : (norm A (K : Subgroup G) (L : Subgroup G) b : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨b, fixedModule_anti inf_le_left b.2⟩ : A) := by
    have h := coe_norm_eq_prod_smul_norm (A := A) D.deg (n := 1) one_pos
      (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K)) (fun x hx => hLK hx)
      (fun x hx => by rw [one_mul]; exact toAdd_deg_mem_multiples (D := D) K (hLK hx))
      (fun k hk _ => hdeg k hk)
      (fun k hk => toAdd_deg_mem_multiples (D := D) K hk)
      (fun q hq => ⟨fun h => Subgroup.mem_inf.2 ⟨h, (Subgroup.mem_inf.1 hq).2⟩,
        fun h => (Subgroup.mem_inf.1 h).1⟩) hφ0K hdφ0 b (fixedModule_anti inf_le_left b.2)
    rw [h]
    simp
  have hNK1 : ∀ a : fixedModule A (L1 : Subgroup G),
      (norm A (K1 : Subgroup G) (L1 : Subgroup G) a : A) =
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨a, fixedModule_anti hIL a.2⟩ : A) := fun a =>
    coe_norm_eq_of_mul_eq (fun x hx => hIK1 hx)
      (fun k hk => by
        obtain ⟨l, hl, hdl⟩ := hK1deg k hk
        refine ⟨k * l⁻¹, Subgroup.mem_inf.2 ⟨K.mul_mem (hK1K hk) (K.inv_mem (hL1K hl)), ?_⟩, ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hdl, mul_inv_cancel]
        · simpa using hl)
      (fun q hq => ⟨fun h => Subgroup.mem_inf.2 ⟨hL1L h, (Subgroup.mem_inf.1 hq).2⟩,
        fun h => hIL h⟩) a _

  have hπ0L1 : (π0 : A) ∈ fixedModule A (L1 : Subgroup G) := fixedModule_anti hL1S π0.2
  have hbL1 : (b : A) ∈ fixedModule A (L1 : Subgroup G) := fixedModule_anti hL1L b.2
  have hy : norm A (K1 : Subgroup G) (L1 : Subgroup G)
      ((⟨π0, hπ0L1⟩ : fixedModule A (L1 : Subgroup G)) / ⟨b, hbL1⟩) = 1 := by
    rw [map_div, div_eq_one]
    ext
    rw [hNK1, hNK1]
    exact (hNS.symm.trans (congrArg Subtype.val hb).symm).trans hNL
  obtain ⟨-, hH1⟩ := hax K1 L1 hL1K1 hcyc1
  have hsub := (Nat.card_eq_one_iff_unique.1 hH1).1
  have haug : (((⟨π0, hπ0L1⟩ : fixedModule A (L1 : Subgroup G)) / ⟨b, hbL1⟩ :
      fixedModule A (L1 : Subgroup G)) : A) ∈ augmentation A (K1 : Subgroup G) (L1 : Subgroup G) :=
    (QuotientGroup.eq_one_iff (N := (augmentation A (K1 : Subgroup G) (L1 : Subgroup G)).comap
        ((fixedModule A (L1 : Subgroup G)).subtype.comp
          (norm A (K1 : Subgroup G) (L1 : Subgroup G)).ker.subtype))
      (⟨_, hy⟩ : (norm A (K1 : Subgroup G) (L1 : Subgroup G)).ker)).1 (Subsingleton.elim _ _)
  obtain ⟨x, hxL1, hxy⟩ := exists_eq_smul_div_of_mem_augmentation_of_generator
    (fun z hz => hL1K1 hz) hτK1 hgen1 haug
  have hπ0x : (π0 : A) = τ • x / x * b := by
    rw [← hxy, Subgroup.coe_div, div_mul_cancel]

  have hσπ : s.elt • (π0 : A) = π0 := π0.2 s.elt (s.elt_mem_field hLK)
  have hσb : s.elt • (b : A) = τ ^ k • (b : A) := by rw [hs_elt, mul_smul, b.2 φ hφL]
  have hcomm : s.elt • τ • x = τ • s.elt • x := by
    have hc : s.elt⁻¹ * τ⁻¹ * s.elt * τ ∈ (L1 : Subgroup G) :=
      hIL (commutator_mem_of_isCyclic (D := D) hcyc s.mem hτK)
    calc s.elt • τ • x = (τ * s.elt) • (s.elt⁻¹ * τ⁻¹ * s.elt * τ) • x := by
          rw [smul_smul, smul_smul]
          congr 1
          group
      _ = τ • s.elt • x := by rw [hxL1 _ hc, mul_smul]
  have e1 : τ • (s.elt • x) / s.elt • x * τ ^ k • (b : A) = τ • x / x * b := by
    have h := hσπ
    rw [hπ0x, smul_mul', smul_div', hcomm, hσb] at h
    exact h

  obtain ⟨c, hcdef⟩ : ∃ c : A, c = ∏ ν : Fin k, τ ^ (ν : ℕ) • (b : A) := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : A, z = x / s.elt • x := ⟨_, rfl⟩
  have hτc : τ • c / c = τ ^ k • (b : A) / b := by rw [hcdef]; exact smul_prod_pow_div τ (b : A) k
  have hkb : τ ^ k • (b : A) / b = τ • x / x / (τ • (s.elt • x) / s.elt • x) := by
    rw [div_eq_div_iff_mul_eq_mul, mul_comm (τ ^ k • (b : A))]
    exact e1
  have hτz : τ • z / z = τ • x / x / (τ • (s.elt • x) / s.elt • x) := by
    rw [hzdef, smul_div', div_div_div_comm]
  have hτw : τ • (c / z) = c / z := by
    have h : τ • (c / z) / (c / z) = 1 := by
      rw [smul_div', div_div_div_comm, hτc, hτz, hkb, div_self']
    exact div_eq_one.1 h
  have hcL1 : c ∈ fixedModule A (L1 : Subgroup G) := by
    rw [hcdef]
    exact Subgroup.prod_mem _ fun ν _ => hsmulL1 _ (K.pow_mem hτK _) _ hbL1
  have hσxL1 : s.elt • x ∈ fixedModule A (L1 : Subgroup G) := hsmulL1 _ s.mem x hxL1
  have hzL1 : z ∈ fixedModule A (L1 : Subgroup G) := by
    rw [hzdef]
    exact Subgroup.div_mem _ hxL1 hσxL1
  have hwL1 : c / z ∈ fixedModule A (L1 : Subgroup G) := Subgroup.div_mem _ hcL1 hzL1
  have hpw : ∀ m : ℕ, τ ^ m • (c / z) = c / z := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_smul]
    | succ m ih => rw [pow_succ, mul_smul, hτw, ih]
  have hwK1 : c / z ∈ fixedModule A (K1 : Subgroup G) := by
    intro g hg
    obtain ⟨m, hm⟩ := hgen1 g hg
    have e : g = τ ^ m * ((τ ^ m)⁻¹ * g) := by group
    rw [e, mul_smul, hwL1 _ hm, hpw]

  have he1L : relRamificationIndex D.deg L L1 = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro y hy
    exact hIL (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hy).2, (Subgroup.mem_inf.1 hy).1⟩)
  have hvb1 : D.valuation L1 ⟨(b : A), hbL1⟩ = Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hL1L b.2, he1L, pow_one]
    exact hvb
  have hvτb : ∀ ν : ℕ, D.valuation L1 ⟨τ ^ ν • (b : A), hsmulL1 _ (K.pow_mem hτK ν) _ hbL1⟩ =
      Multiplicative.ofAdd 1 :=
    fun ν => (valuation_smul_of_map_eq L1 (hmapL1 _ (K.pow_mem hτK ν)) ⟨(b : A), hbL1⟩ _).trans hvb1
  have hvσx : D.valuation L1 ⟨s.elt • x, hσxL1⟩ = D.valuation L1 ⟨x, hxL1⟩ :=
    valuation_smul_of_map_eq L1 (hmapL1 _ s.mem) ⟨x, hxL1⟩ _
  have hweq : (⟨c / z, hwL1⟩ : fixedModule A (L1 : Subgroup G)) =
      (∏ ν : Fin k, (⟨τ ^ (ν : ℕ) • (b : A), hsmulL1 _ (K.pow_mem hτK _) _ hbL1⟩ :
        fixedModule A (L1 : Subgroup G))) /
        ((⟨x, hxL1⟩ : fixedModule A (L1 : Subgroup G)) / ⟨s.elt • x, hσxL1⟩) := by
    ext
    simp [hcdef, hzdef]
  have hvw : D.valuation L1 ⟨c / z, hwL1⟩ = Multiplicative.ofAdd (k : ℤ̂) := by
    rw [hweq, map_div, map_div, map_prod, hvσx, div_self', div_one]
    simp only [hvτb, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ofAdd_nsmul, nsmul_one]

  have hval := D.valuation_of_mem hL1K1 hwK1
  rw [hvw] at hval
  have he1 : 0 < relRamificationIndex D.deg K1 L1 :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hk : ((k : ℤ) : ℤ̂) =
      relRamificationIndex D.deg K1 L1 • Multiplicative.toAdd (D.valuation K1 ⟨c / z, hwK1⟩) := by
    have h := congrArg Multiplicative.toAdd hval
    rw [toAdd_ofAdd, toAdd_pow] at h
    rw [Int.cast_natCast]
    exact h
  have hdvd : relRamificationIndex D.deg K1 L1 ∣ k :=
    Int.natCast_dvd_natCast.1 (dvd_of_intCast_eq_nsmul he1 hk)

  have hNker : ((L1 : Subgroup G).subgroupOf (D.deg.ker ⊓ (K1 : Subgroup G))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hconj g (hK1K (Subgroup.mem_inf.1 g.2).2) n hn⟩
  have hτe : τ ^ relRamificationIndex D.deg K1 L1 ∈ (L1 : Subgroup G) := by
    have h := Subgroup.pow_index_mem ((L1 : Subgroup G).subgroupOf (D.deg.ker ⊓ (K1 : Subgroup G)))
      (⟨τ, Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 hτker, hτK1⟩⟩ :
        (D.deg.ker ⊓ (K1 : Subgroup G) : Subgroup G))
    rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow] at h
    exact h
  obtain ⟨j, hj⟩ := hdvd
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, SubgroupClass.coe_pow, hj, pow_mul]
  exact hL1L (Subgroup.pow_mem _ hτe j)
theorem reciprocity_bijective_of_totallyRamified
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
    (htot : relInertiaDegree D.deg K L = 1) : Function.Bijective (D.reciprocity hLK hax) := by
  have hcard := (hax K L hLK hcyc).1
  have : Finite (tateZero A (K : Subgroup G) (L : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Subgroup.FiniteIndex.index_ne_zero)
  refine (reciprocity_injective_of_totallyRamified hLK hax hcyc htot).bijective_of_nat_card_le ?_
  rw [hcard]
  exact le_rfl
end TotallyRamified
section Cyclic
variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
theorem reciprocity_surjective_of_isCyclic
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    Function.Surjective (D.reciprocity hLK hax) := by

  obtain ⟨M, hLM, hMK, huM, htotM⟩ : ∃ M : OpenSubgroup G, L ≤ M ∧ M ≤ K ∧
      (K : Subgroup G) ⊓ D.deg.ker ≤ M ∧ relInertiaDegree D.deg M L = 1 :=
    ⟨D.maxUnramified K L, le_maxUnramified hLK, maxUnramified_le, inf_ker_le_maxUnramified,
      relInertiaDegree_maxUnramified⟩
  have hNM : ((L : Subgroup G).subgroupOf M).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h := (inferInstance : ((L : Subgroup G).subgroupOf K).Normal).conj_mem ⟨n, hMK n.2⟩
        (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hMK g.2⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h⟩

  have hcycM : IsCyclic ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) := by
    have := hcyc
    refine isCyclic_of_injective
      (QuotientGroup.map ((L : Subgroup G).subgroupOf M) ((L : Subgroup G).subgroupOf K)
        (Subgroup.inclusion (fun x hx => hMK hx)) ?_) ?_
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf] at hx
      exact hx
    · rw [injective_iff_map_eq_one]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hq
  have hbijLM := reciprocity_bijective_of_totallyRamified hLM hax hcycM htotM

  obtain ⟨φ0, hφ0K, hdφ0⟩ := D.exists_deg_eq K
  obtain ⟨s1, hs1⟩ : ∃ s1 : D.FrobeniusLift K, s1.deg = 1 :=
    ⟨FrobeniusLift.ofDegOne hφ0K hdφ0, rfl⟩
  obtain ⟨π1, hπ1⟩ := D.exists_prime (s1.field L hLK)
  have hr1 := reciprocity_mk_eq_norm hLK hax s1 hπ1
  have hvc : D.valuation K (norm A (K : Subgroup G) (s1.field L hLK : Subgroup G) π1) =
      Multiplicative.ofAdd 1 := by
    rw [valuation_norm_prime hLK s1 hπ1, hs1, Nat.cast_one]
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>

    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ZMod (D.relInertiaDegreePNat hMK)) =
        proj (D.relInertiaDegreePNat hMK) (Multiplicative.toAdd (D.valuation K a)) :=
      ⟨_, ZMod.natCast_zmod_val _⟩
    have hker : D.tateZeroVal hMK ((a / norm A (K : Subgroup G) (s1.field L hLK : Subgroup G) π1 ^ j :
        fixedModule A (K : Subgroup G)) : tateZero A (K : Subgroup G) (M : Subgroup G)) = 1 := by
      rw [tateZeroVal_mk, valuationMod_apply, map_div, map_pow, hvc, toAdd_div, toAdd_pow,
        toAdd_ofAdd, nsmul_one, map_sub, map_natCast, hj, sub_self, ofAdd_zero]
    have h0 : ((a / norm A (K : Subgroup G) (s1.field L hLK : Subgroup G) π1 ^ j :
        fixedModule A (K : Subgroup G)) : tateZero A (K : Subgroup G) (M : Subgroup G)) = 1 :=
      (D.tateZeroVal_bijective hax hMK huM).1 (by rw [hker, map_one])
    obtain ⟨a0, ha0⟩ := (QuotientGroup.eq_one_iff _).1 h0

    obtain ⟨q, hq⟩ := hbijLM.2 (a0 : tateZero A (M : Subgroup G) (L : Subgroup G))
    obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLM q
    obtain ⟨π2, hπ2⟩ := D.exists_prime (s.field L hLM)
    rw [reciprocity_mk_eq_norm hLM hax s hπ2, QuotientGroup.eq] at hq
    obtain ⟨b, hb⟩ := hq

    let s' : D.FrobeniusLift K :=
      { elt := s.elt
        mem := hMK s.mem
        deg := s.deg * relInertiaDegree D.deg K M
        deg_pos := Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hMK))
        deg_eq := by
          rw [s.deg_eq, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
            (L := (M : Subgroup G)) (fun x hx => hMK hx), mul_assoc] }
    have hr' := reciprocity_mk_eq_norm hLK hax s' (π := π2) hπ2
    have hnn : norm A (K : Subgroup G) (M : Subgroup G)
        (norm A (M : Subgroup G) (s.field L hLM : Subgroup G) π2) =
          norm A (K : Subgroup G) (s.field L hLM : Subgroup G) π2 :=
      norm_norm (fun x hx => s.field_le hLM hx) (fun x hx => hMK hx) π2
    refine ⟨((⟨s'.elt, s'.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) *
      ((⟨s1.elt, s1.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ j, ?_⟩
    rw [map_mul, map_pow, hr', hr1, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine ⟨b, ?_⟩
    have h1 := congrArg (norm A (K : Subgroup G) (M : Subgroup G)) hb
    rw [norm_norm (fun x hx => hLM hx) (fun x hx => hMK hx), map_mul, map_inv, hnn, ha0] at h1
    rw [h1, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
theorem reciprocity_bijective_of_isCyclic
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    Function.Bijective (D.reciprocity hLK hax) := by
  have hcard := (hax K L hLK hcyc).1
  refine (reciprocity_surjective_of_isCyclic hLK hax hcyc).bijective_of_nat_card_le ?_
  rw [hcard]
  exact le_rfl
variable (D) in

noncomputable def reciprocityEquiv
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K ≃* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  MulEquiv.ofBijective _ (reciprocity_bijective_of_isCyclic (D := D) hLK hax hcyc)
end Cyclic
end ClassFieldData
end GroundTheory.LocalField.Abstract


