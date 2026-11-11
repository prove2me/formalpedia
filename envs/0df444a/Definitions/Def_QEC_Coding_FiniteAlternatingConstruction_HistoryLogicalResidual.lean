-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T13:40:27.381597+00:00
-- url     : https://prove2.me/theorems/83d59464-618f-4ba6-a76f-efedbf30fbfa
-- title:
--   History Logical Residual
-- statement:
--   Definitions and structural lemmas for History Logical Residual, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
def topCoefficient (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) : BDL26Field :=
  FC.finiteH1Equiv S (n+2) (FC.classOf S (n+2) (topCocycle S n sigma e))
def lowerCoefficient (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) : BDL26Field :=
  FC.finiteH1Equiv S 2 (FC.classOf S 2 (lowerCocycle S n sigma e u hu))
def logicalError : (SuffixData S n).family.Cochain1 (TopIndex n) :=
  (FC.generator S (n+2) 1).val
theorem source_even_valid (k : Nat) (hk : 1 ≤ k)
    (sigma : (indexedFamily S (2*k)).Syndrome (TopIndex (2*k)))
    (u : (indexedFamily S (2*k)).Cochain1 (TopIndex (2*k)))
    (hu : (indexedFamily S (2*k)).coboundary1 (TopIndex (2*k)) u = sigma.val) :
    (SuffixData S (2*(k-1))).family.coboundary1 (TopIndex (2*(k-1)))
      (sourceEvenError S k hk u) = (sourceEvenInput S k hk sigma).val := by
  cases k with
  | zero => omega
  | succ k => exact hu
end QEC.Coding.BDL26HistoryLogicalResidual


