-- Prove2me | solution 1 for Algebra.IsSeparable.of_coprime_finrank_expChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8e5de907-740e-536f-8556-95b8c5dfd3ff

import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsSeparable_of_coprime_finrank_expChar

set_option autoImplicit false

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (q : ℕ) [ExpChar F q] (h : Nat.Coprime (Module.finrank F E) q) :
    Algebra.IsSeparable F E := by
  rw [← Field.finSepDegree_eq_finrank_iff]

  haveI : ExpChar (separableClosure F E) q :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective q
  haveI : IsPurelyInseparable (separableClosure F E) E := separableClosure.isPurelyInseparable F E
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (separableClosure F E) E q
  have hins : Field.finInsepDegree F E = q ^ n := hn
  have hmul := Field.finSepDegree_mul_finInsepDegree F E
  rw [hins] at hmul

  have hdvd : q ^ n ∣ Module.finrank F E := ⟨Field.finSepDegree F E, by rw [mul_comm]; exact hmul.symm⟩
  have hone : q ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n h.symm) hdvd
  rw [hone, mul_one] at hmul
  exact hmul

end S_Algebra_IsSeparable_of_coprime_finrank_expChar
end P2MW
export P2MW.S_Algebra_IsSeparable_of_coprime_finrank_expChar (solution)
