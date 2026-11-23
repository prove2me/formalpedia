-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_LocBasis
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_LocBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:46.106811+00:00
-- url     : https://prove2.me/theorems/e9168110-77f5-45ae-85e7-3806b57ce4fa
-- title:
--   Loc Basis
-- statement:
--   Definitions and structural lemmas for Loc Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/LocBasis.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Lemmata_PaddedFamilies_PadFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
namespace PI.SelfDualLoc.W.LB
open PI.SelfDualLoc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
abbrev Sv : Submonoid (𝓞 E) := Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl
lemma Sv_le : Sv (E := E) v ≤ (𝓞 E)⁰ := by
  intro s hs
  obtain ⟨u, hu, rfl⟩ := hs
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (zero_mem _)
  apply hu0
  exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h)
abbrev Sp : Subalgebra (𝓞 E) E := Localization.subalgebra.ofField E (Sv (E := E) v) (Sv_le v)
lemma coe_algebraMap_OF (u : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = algebraMap F E (u : F) := rfl
lemma smul_OE (c : 𝓞 E) (w : Fin n → E) : c • w = (c : E) • w := by
  ext j; simp [Algebra.smul_def]
lemma one_nm : (1 : 𝓞 F) ∉ v.asIdeal := (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
lemma mul_nm {u t : 𝓞 F} (hu : u ∉ v.asIdeal) (ht : t ∉ v.asIdeal) : u * t ∉ v.asIdeal :=
  fun h => (v.isPrime.mem_or_mem h).elim hu ht
lemma algF_ne_zero {u : 𝓞 F} (hu : u ∉ v.asIdeal) : algebraMap F E (u : F) ≠ 0 := by
  have hu0 : (u : F) ≠ 0 := by
    intro h
    apply hu
    have : u = 0 := RingOfIntegers.ext (by simpa using h)
    rw [this]; exact zero_mem _
  exact (map_ne_zero_iff _ (algebraMap F E).injective).2 hu0
lemma smulF_mem (L : Submodule (𝓞 E) (Fin n → E)) (u : 𝓞 F) {w : Fin n → E} (hw : w ∈ L) :
    algebraMap F E (u : F) • w ∈ L := by
  have := L.smul_mem (algebraMap (𝓞 F) (𝓞 E) u) hw
  rwa [smul_OE, coe_algebraMap_OF] at this
lemma coeF_mul (u t : 𝓞 F) :
    algebraMap F E ((u * t : 𝓞 F) : F) = algebraMap F E (u : F) * algebraMap F E (t : F) := by
  rw [← map_mul]; rfl
lemma mem_Sp' (c : E) : c ∈ Sp (E := E) v ↔
    ∃ (a : 𝓞 E) (s : 𝓞 E) (_ : s ∈ Sv (E := E) v),
      c = algebraMap (𝓞 E) E a * (algebraMap (𝓞 E) E s)⁻¹ := Iff.rfl
lemma mem_Sp_imp {c : E} (hc : c ∈ Sp (E := E) v) :
    ∃ (a : 𝓞 E) (u : 𝓞 F), u ∉ v.asIdeal ∧ c * algebraMap F E (u : F) = (a : E) := by
  obtain ⟨a, s, hs, rfl⟩ := (mem_Sp' v c).1 hc
  obtain ⟨u, hu, rfl⟩ := hs
  refine ⟨a, u, hu, ?_⟩
  have h0 := algF_ne_zero (E := E) v hu
  change (a : E) * ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E)⁻¹ * algebraMap F E (u : F) = (a : E)
  rw [coe_algebraMap_OF]
  field_simp
def satur (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (Sp (E := E) v) (Fin n → E) where
  carrier := {w | ∃ u : 𝓞 F, u ∉ v.asIdeal ∧ algebraMap F E (u : F) • w ∈ L}
  add_mem' := by
    rintro w1 w2 ⟨u1, h1, m1⟩ ⟨u2, h2, m2⟩
    refine ⟨u1 * u2, mul_nm v h1 h2, ?_⟩
    have e : algebraMap F E ((u1 * u2 : 𝓞 F) : F) • (w1 + w2) =
        algebraMap F E (u2 : F) • (algebraMap F E (u1 : F) • w1) +
          algebraMap F E (u1 : F) • (algebraMap F E (u2 : F) • w2) := by
      rw [coeF_mul, smul_add, smul_smul, smul_smul,
        mul_comm (algebraMap F E (u2 : F)) (algebraMap F E (u1 : F))]
    rw [e]
    exact add_mem (smulF_mem L _ m1) (smulF_mem L _ m2)
  zero_mem' := ⟨1, one_nm v, by simp⟩
  smul_mem' := by
    rintro c w ⟨u, hu, m⟩
    obtain ⟨a, u', hu', hc⟩ := mem_Sp_imp v c.2
    refine ⟨u' * u, mul_nm v hu' hu, ?_⟩
    have e : algebraMap F E ((u' * u : 𝓞 F) : F) • (c • w) =
        a • (algebraMap F E (u : F) • w) := by
      rw [smul_OE, coeF_mul]
      ext j
      show (algebraMap F E (u' : F) * algebraMap F E (u : F)) * ((c : E) * w j) =
        (a : E) * (algebraMap F E (u : F) * w j)
      rw [← hc]
      ring
    rw [e]
    exact L.smul_mem a m
end PI.SelfDualLoc.W.LB
namespace PI.SelfDualLoc.W
open PI.SelfDualLoc LB
end PI.SelfDualLoc.W


