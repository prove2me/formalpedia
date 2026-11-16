-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralAdditivity
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralAdditivity
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:58:59.716325+00:00
-- url     : https://prove2.me/theorems/914df18d-b3ce-4b7f-886b-a5bea83964c2
-- title:
--   Computable analysis · IntegralAdditivity · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralPartitionAppend

set_option autoImplicit true

/-! Additivity of supplied proper integral witnesses on adjacent intervals,
proved from concatenated finite bounds and arbitrary tightness. No integral
identity is assumed in a certificate field. -/
namespace ComputableAnalysis.Integral
set_option maxHeartbeats 1000000

theorem HasIntegral.append_identity {F : FunctionOnInterval} {I J K : RealCompute}
    (b : Rat) (hb0 : F.lower≤b) (hb1 : b≤F.upper)
    (hI : HasIntegral (F.restrict F.lower b (Rat.le_refl) hb0 hb1) I)
    (hJ : HasIntegral (F.restrict b F.upper hb0 hb1 (Rat.le_refl)) J)
    (hK : HasIntegral F K) : K.Equiv (RealCompute.add I J) := by
  apply RealCompute.equiv_of_le_of_ge
  · intro n m
    change (K.compute n).lo≤(I.compute m).hi+(J.compute m).hi
    by_cases h : (K.compute n).lo≤(I.compute m).hi+(J.compute m).hi
    · exact h
    · exfalso
      let eps : QPos := ⟨((K.compute n).lo-((I.compute m).hi+(J.compute m).hi))/4,by
        rw [Rat.div_def]
        exact Rat.mul_pos (by grind only) (Rat.inv_pos.mpr (by decide +kernel))⟩
      obtain ⟨A,hA⟩ := hI.tight eps
      obtain ⟨B,hB⟩ := hJ.tight eps
      have hFull := (hK.bounds (appendBounds b hb0 hb1 A B) n).2
      rw [appendBounds_upperSum] at hFull
      have hLeft := (hI.bounds A m).1
      have hRight := (hJ.bounds B m).1
      dsimp [eps] at hA hB
      grind only
  · intro n m
    change (I.compute n).lo+(J.compute n).lo≤(K.compute m).hi
    by_cases h : (I.compute n).lo+(J.compute n).lo≤(K.compute m).hi
    · exact h
    · exfalso
      let eps : QPos := ⟨((I.compute n).lo+(J.compute n).lo-(K.compute m).hi)/4,by
        rw [Rat.div_def]
        exact Rat.mul_pos (by grind only) (Rat.inv_pos.mpr (by decide +kernel))⟩
      obtain ⟨A,hA⟩ := hI.tight eps
      obtain ⟨B,hB⟩ := hJ.tight eps
      have hFull := (hK.bounds (appendBounds b hb0 hb1 A B) m).1
      rw [appendBounds_lowerSum] at hFull
      have hLeft := (hI.bounds A n).2
      have hRight := (hJ.bounds B n).2
      dsimp [eps] at hA hB
      grind only

end ComputableAnalysis.Integral


