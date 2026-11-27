-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitSubtorusLaurentPolynomialPoints
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitSubtorusLaurentPolynomialPoints
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:29:45.980939+00:00
-- url     : https://prove2.me/theorems/239cff4c-1fc3-4d4f-996a-22a192776746
-- title:
--   Split Subtorus Laurent Polynomial Points
-- statement:
--   Definitions and structural lemmas for Split Subtorus Laurent Polynomial Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitSubtorusLaurentPolynomialPoints.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
namespace GlobalTheory.RegSS.Laurent
variable {F : Type} [Field F] {s : ℕ}
def chi (t : Fin s → Fˣ) : Multiplicative (Fin s → ℤ) →* F where
  toFun a := ((∏ j, t j ^ (Multiplicative.toAdd a) j : Fˣ) : F)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, _root_.zpow_add, Finset.prod_mul_distrib, Units.val_mul]
def ev (t : Fin s → Fˣ) : AddMonoidAlgebra F (Fin s → ℤ) →ₐ[F] F :=
  AddMonoidAlgebra.lift F F (Fin s → ℤ) (chi t)
def univ (F : Type) [Field F] (s : ℕ) (j : Fin s) : (AddMonoidAlgebra F (Fin s → ℤ))ˣ where
  val := AddMonoidAlgebra.single (Pi.single j 1) 1
  inv := AddMonoidAlgebra.single (-Pi.single j 1) 1
  val_inv := by rw [AddMonoidAlgebra.single_mul_single]; simp [AddMonoidAlgebra.one_def]
  inv_val := by rw [AddMonoidAlgebra.single_mul_single]; simp [AddMonoidAlgebra.one_def]
end GlobalTheory.RegSS.Laurent
namespace GlobalTheory.RegSS
open Laurent
end GlobalTheory.RegSS


