-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:17.632586+00:00
-- url     : https://prove2.me/theorems/e59c220c-e53b-4f32-9b7b-d66ffee4726a
-- title:
--   Double Coset Rel Index Inf Conj Const
-- statement:
--   Definitions and structural lemmas for Double Coset Rel Index Inf Conj Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.DoubleCosetWeight
open Subgroup
def gen {G : Type} [Group G] (T K : Subgroup G) : Subgroup G :=
  ⨆ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom
end GlobalTheory.DoubleCosetWeight


