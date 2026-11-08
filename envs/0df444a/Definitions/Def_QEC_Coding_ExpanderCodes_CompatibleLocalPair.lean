-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
-- name    : QEC_Coding_ExpanderCodes_CompatibleLocalPair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:29:17.526239+00:00
-- url     : https://prove2.me/theorems/1d52a5df-ecfc-4a28-b922-cfad4af50c74
-- title:
--   Compatible Local Pair
-- statement:
--   Definitions and structural lemmas for Compatible Local Pair, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatibleLocalPair.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
variable {F : Type}
noncomputable local instance pk22LocalPairDecidableEq : DecidableEq F :=
  Classical.decEq F
abbrev PK22Direction (q t : Nat)
    (a : CompatibleDegreePrime (pk22LocalWidth q t)) :=
  Fin (a.p + 1)
abbrev PK22Check (q t : Nat)
    (a : CompatibleDegreePrime (pk22LocalWidth q t)) :=
  Fin (pk22RowCoefficient q t * a.blocks)
end QEC.Coding.TannerLiftedProduct


