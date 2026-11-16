-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralLimitValueAgreement
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralLimitValueAgreement
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:00.818245+00:00
-- url     : https://prove2.me/theorems/a6cc6619-bafb-4147-914e-18ec014ae6ec
-- title:
--   Computable analysis · IntegralLimitValueAgreement · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralLimitValueAgreement.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralExtensions

set_option autoImplicit true

/-! Equality of represented values preserves the role of an actual improper
integral. This changes no exhaustion or compact witnesses; convergence is
transported by the exact order laws for valid represented values. -/
namespace ComputableAnalysis.Integral
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem Within.congr_left {I J K : RealCompute} {eps : Rat}
    (hI : I.Valid) (hJ : J.Valid) (hK : K.Valid) (he : I.Equiv J) (h : Within I K eps) : Within J K eps := by
  have hFirst : I.Le (RealCompute.add K (RealCompute.ofRat eps)) := fun i j => (h i j).1
  have hSecond : K.Le (RealCompute.add I (RealCompute.ofRat eps)) := fun i j => (h j i).2
  have hLeft := RealCompute.le_trans hI (RealCompute.le_of_equiv hJ hI (RealCompute.equiv_symm he)) hFirst
  have hAdd := RealCompute.le_add_le_add (RealCompute.le_of_equiv hI hJ he)
    (RealCompute.le_refl (RealCompute.ofRat eps) (RealCompute.ofRat_valid eps))
  have hRight := RealCompute.le_trans (RealCompute.add_valid (x := I) (y := RealCompute.ofRat eps) hI (RealCompute.ofRat_valid eps)) hSecond hAdd
  exact fun i j => ⟨hLeft i j,hRight j i⟩

/-- A proved value identity transports an already justified integral-limit
role. It does not infer an integral role from numerical validity. -/
theorem HasIntegralLimit.congr {F : Nat → FunctionOnInterval} {I J : RealCompute}
    (hI : HasIntegralLimit F I) (hJ : J.Valid) (he : I.Equiv J) : HasIntegralLimit F J := by
  refine ⟨hJ,hI.compact,?_⟩
  intro eps
  obtain ⟨N,hN⟩ := hI.converges eps
  exact ⟨N,fun n hn K hK => Within.congr_left hI.valid hJ hK.valid he (hN n hn K hK)⟩

end ComputableAnalysis.Integral


