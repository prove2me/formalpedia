-- Prove2me | Definitions.Def_KnillLaflammeLean_Basic
-- name    : KnillLaflammeLean_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:48:06.137179+00:00
-- url     : https://prove2.me/theorems/304dc6cb-9cd9-4f9a-9846-98807e347af0
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Zayn Blore's pinned Knill–Laflamme quantum error correction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/Basic.lean

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Matrix
namespace QuantumInfo
namespace Channel
variable {n m ι κ : Type*} [Fintype n] [Fintype m] [Fintype ι] [Fintype κ] [DecidableEq n]
def reindex (e : ι ≃ κ) (Φ : Channel n m ι) : Channel n m κ where
  kraus k := Φ.kraus (e.symm k)
  tp := (Equiv.sum_comp e.symm fun i => (Φ.kraus i)ᴴ * Φ.kraus i).trans Φ.tp
end Channel
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
end QuantumInfo


