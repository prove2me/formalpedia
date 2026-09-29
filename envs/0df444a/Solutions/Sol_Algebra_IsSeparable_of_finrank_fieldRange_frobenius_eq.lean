-- Prove2me | solution 1 for Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3d98fae7-eb35-5aab-9abf-45d281dfa828

import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq

set_option autoImplicit false

theorem solution
    {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hdeg : Module.finrank (frobenius F p).fieldRange F = p)
    (y : E) (hy : algebraMap E F y ∉ (frobenius F p).fieldRange) :
    Algebra.IsSeparable E F := by
  set S : Subfield F := (frobenius F p).fieldRange with hS
  haveI : IsSimpleOrder (IntermediateField S F) :=
    IntermediateField.isSimpleOrder_of_finrank_prime S F (by rw [hdeg]; exact Fact.out)

  set D := KaehlerDifferential.D E F with hD
  have hDS : ∀ s : F, s ∈ S → D s = 0 := by
    intro s hs
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.mp hs
    rw [frobenius_def, D.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  have hDy : D (algebraMap E F y) = 0 := D.map_algebraMap y

  let Z : IntermediateField S F :=
    { carrier := {z | D z = 0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [D.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      one_mem' := D.map_one_eq_zero
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, add_zero]
      zero_mem' := map_zero D
      algebraMap_mem' := fun s => hDS _ s.2
      inv_mem' := by
        intro z hz
        simp only [Set.mem_setOf_eq] at hz ⊢
        rw [D.leibniz_inv, hz, smul_zero] }
  have hyZ : IntermediateField.adjoin S {algebraMap E F y} ≤ Z :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hDy)
  have hZ : Z = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin S {algebraMap E F y})
      with h | h
    · exfalso
      apply hy
      have hmem : algebraMap E F y ∈ (⊥ : IntermediateField S F) :=
        h ▸ IntermediateField.mem_adjoin_simple_self S (algebraMap E F y)
      obtain ⟨s, hs⟩ := IntermediateField.mem_bot.mp hmem
      rw [← hs]
      exact s.2
    · rw [h] at hyZ
      exact top_le_iff.mp hyZ
  have hD0 : ∀ z : F, D z = 0 := fun z => by
    have hz : z ∈ Z := hZ ▸ IntermediateField.mem_top
    exact hz

  haveI : Subsingleton (KaehlerDifferential E F) := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    have hω : ω ∈ Submodule.span F (Set.range D) := by
      rw [hD, KaehlerDifferential.span_range_derivation]
      trivial
    have hle : Submodule.span F (Set.range D) ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, rfl⟩
      exact (Submodule.mem_bot F).mpr (hD0 z)
    exact (Submodule.mem_bot F).mp (hle hω)
  haveI : Algebra.FormallyUnramified E F := ⟨inferInstance⟩
  exact Algebra.FormallyUnramified.isSeparable E F

end S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq
end P2MW
export P2MW.S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq (solution)
