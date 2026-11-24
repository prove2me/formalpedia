-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:07.190786+00:00
-- url     : https://prove2.me/theorems/18b25ed8-bdfe-4f02-a0d4-9b0e6a7850ab
-- title:
--   Norm Le One Of Integer
-- statement:
--   Definitions and structural lemmas for Norm Le One Of Integer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/NormLeOneOfInteger.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
namespace PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
theorem norm_natCast_lt_one (l : ℕ) [hl : Fact l.Prime] : ‖((l : ℕ) : Om l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)
theorem norm_le_one_of_integer {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) (x : 𝓞 E) : ‖φ (x : E)‖ ≤ 1 := by
  have hv := Valuation.integer.integers (Valued.v : Valuation (Om l) NNReal)
  have h1 : IsIntegral ℤ (φ (x : E)) := (RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom
  have h2 : IsIntegral (Valued.v : Valuation (Om l) NNReal).integer (φ (x : E)) := h1.tower_top
  have h3 := (hv.isIntegral_iff_v_le_one).1 h2
  rw [PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3
def plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l) :
    Ideal (𝓞 E) where
  carrier := {x | ‖φ (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change ‖φ (algebraMap (𝓞 E) E (a + b))‖ < 1
    change ‖φ (algebraMap (𝓞 E) E a)‖ < 1 at ha
    change ‖φ (algebraMap (𝓞 E) E b)‖ < 1 at hb
    rw [map_add, map_add]
    exact lt_of_le_of_lt (PadicAlgCl.isNonarchimedean l _ _) (max_lt ha hb)
  smul_mem' c {a} ha := by
    change ‖φ (algebraMap (𝓞 E) E (c * a))‖ < 1
    change ‖φ (algebraMap (𝓞 E) E a)‖ < 1 at ha
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_integer φ c)) ha
theorem mem_plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l)
    (x : 𝓞 E) : x ∈ plIdeal φ ↔ ‖φ (x : E)‖ < 1 := Iff.rfl
theorem natCast_mem_plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : ((l : ℕ) : 𝓞 E) ∈ plIdeal φ := by
  rw [mem_plIdeal]
  simpa using norm_natCast_lt_one l
theorem plIdeal_isPrime {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : (plIdeal φ).IsPrime where
  ne_top' h := by
    have : (1 : 𝓞 E) ∈ plIdeal φ := h ▸ Submodule.mem_top
    rw [mem_plIdeal] at this
    simp at this
  mem_or_mem' {a b} hab := by
    simp only [mem_plIdeal, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at *
    by_contra h
    push Not at h
    have := mul_le_mul h.1 h.2 zero_le_one (norm_nonneg _)
    linarith
theorem plIdeal_ne_bot {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : plIdeal φ ≠ ⊥ := by
  intro h
  have h1 := natCast_mem_plIdeal (E := E) φ
  rw [h, Ideal.mem_bot] at h1
  have : ((l : ℕ) : E) = 0 := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1
  exact hl.out.ne_zero (by exact_mod_cast this)
def plOf {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l) :
    HeightOneSpectrum (𝓞 E) :=
  ⟨plIdeal φ, plIdeal_isPrime φ, plIdeal_ne_bot φ⟩
end PI.CompDegEF


