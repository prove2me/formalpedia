-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
-- name    : QEC_Coding_ExpanderCodes_LPSEffectivePrime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:45:06.3228+00:00
-- url     : https://prove2.me/theorems/27dafb1b-d93e-4619-a50c-5a64bca10914
-- title:
--   LPSEffective Prime
-- statement:
--   Definitions and structural lemmas for LPSEffective Prime, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
def lpsEffectiveResiduePrimeAt {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) : LPSResiduePrime p :=
  lpsResiduePrimeAt hp hp4 B
def lpsPrimeScan (p B : ℕ) : ℕ → Option ℕ × ℕ
  | 0 => (none, 0)
  | n + 1 =>
      let prev := lpsPrimeScan p B n
      match prev.1 with
      | some _ => prev
      | none => (if lpsPrimeCandidate p B n then some n else none, prev.2 + 1)
open scoped MatrixGroups
abbrev LPSEffectiveVertexGroup {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :=
  PSL(2, ZMod (lpsEffectiveResiduePrimeAt hp hp4 n).q)
def lpsEffectiveQuaternionFamilyLabel {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    LPSGeneratorIndex p → LPSEffectiveVertexGroup hp hp4 n :=
  fun t => lpsEffectiveQuaternionPSL (lpsEffectiveResiduePrimeAt hp hp4 n) t.1
    (norm_eq_of_mem_lpsQuaternionShell hp.pos t.2)
def lpsEffectiveQuaternionFamilyIndex {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    LPSGeneratorIndex p → Fin (lpsPSLList (lpsEffectiveResiduePrimeAt hp hp4 n).q).length :=
  fun t => lpsQuaternionVertexIndex (lpsEffectiveResiduePrimeAt hp hp4 n) t.1
    (norm_eq_of_mem_lpsQuaternionShell hp.pos t.2)
end QEC.Coding.TannerLiftedProduct


