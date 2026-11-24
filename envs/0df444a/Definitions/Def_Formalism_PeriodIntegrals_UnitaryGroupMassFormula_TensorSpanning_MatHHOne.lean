-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:21:54.641629+00:00
-- url     : https://prove2.me/theorems/c004657b-67d1-4660-a2ca-760934ac83b1
-- title:
--   Mat HHOne
-- statement:
--   Definitions and structural lemmas for Mat HHOne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorSpanning/MatHHOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace PI.KerTens.W
open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)
def blk {n : Type} {N N' : ℕ} (b : Fin N' × Fin N) : (n → ℂ) →ₗ[ℂ] (n → Fin N' → Fin N → ℂ) where
  toFun x := fun τ i j => if (i, j) = b then x τ else 0
  map_add' x y := by
    funext τ i j
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext τ i j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp
def upd {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) (t : n → ℂ) :
    n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) = b then t τ else z τ i j
def part {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) : n → ℂ :=
  fun τ => z τ b.1 b.2
def repl {n : Type} {N N' : ℕ} (t0 : n → ℂ) (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ) :
    n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) ∈ s then t0 τ else z τ i j
end PI.KerTens.W


