-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:21.728273+00:00
-- url     : https://prove2.me/theorems/17a07cba-4417-43b3-9ce5-d3a218ce423b
-- title:
--   Fourier Jacobi Unipotent Eq Prod Root Exchange
-- statement:
--   Definitions and structural lemmas for Fourier Jacobi Unipotent Eq Prod Root Exchange, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierJacobiUnipotentEqProdRootExchange.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
namespace GlobalTheory.RootEx.FJUnipotent
open GlobalTheory.RootEx.Radical
section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
def midLev (ρ : ℕ) : n ⊕ Fin c → ℕ :=
  Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1))
def midGroup (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Uni (midLev ρ) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun hx hy => Uni.mul hx hy
  inv_mem' := fun hx => Uni.inv hx
end
end GlobalTheory.RootEx.FJUnipotent


