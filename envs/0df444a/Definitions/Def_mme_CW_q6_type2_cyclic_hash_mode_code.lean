-- Prove2me | Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
-- name    : mme_CW_q6_type2_cyclic_hash_mode_code
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T22:20:27.229038+00:00
-- url     : https://prove2.me/theorems/75f99dab-67ce-4552-9240-c65ef4a4af88
-- title:
--   Mode coefficient code for the cyclic q=6 type-2 hash
-- statement:
--   For each of the three cyclic type-2 modes, this definition records the coefficient of every independent weight coordinate in the combined doubled hash. The three rows are respectively $(2X,4Z,-4Y)$, $(2Y,-4X,4Z)$, and $(Z,2Y,2X)$, with the q=6 third-mode code $0,2,1$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; coefficient form of the cyclic Salem--Spencer hash.

import Mathlib.Data.ZMod.Basic
import Definitions.Def_mme_CW_q6_type2_cyclic_data
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

namespace MME

set_option autoImplicit false

def cwQ6Type2CyclicHashModeCode (p N : ℕ) (i : Fin 3) (u : CWQ6Type2CyclicModeWord N) : Fin 3 → Fin (2 * N) → ZMod p :=
  match i with
  | ⟨0, _⟩ => fun
      | ⟨0, _⟩, j => 2 * ((u.1 j).val : ZMod p)
      | ⟨1, _⟩, j => 4 * (cwQ6CoupledZHashCode (u.2.1 j) : ZMod p)
      | ⟨2, _⟩, j => -4 * ((u.2.2 j).val : ZMod p)
      | ⟨r + 3, h⟩, _ => absurd h (by omega)
  | ⟨1, _⟩ => fun
      | ⟨0, _⟩, j => 2 * ((u.1 j).val : ZMod p)
      | ⟨1, _⟩, j => -4 * ((u.2.1 j).val : ZMod p)
      | ⟨2, _⟩, j => 4 * (cwQ6CoupledZHashCode (u.2.2 j) : ZMod p)
      | ⟨r + 3, h⟩, _ => absurd h (by omega)
  | ⟨2, _⟩ => fun
      | ⟨0, _⟩, j => (cwQ6CoupledZHashCode (u.1 j) : ZMod p)
      | ⟨1, _⟩, j => 2 * ((u.2.1 j).val : ZMod p)
      | ⟨2, _⟩, j => 2 * ((u.2.2 j).val : ZMod p)
      | ⟨r + 3, h⟩, _ => absurd h (by omega)
  | ⟨r + 3, h⟩ => absurd h (by omega)

end MME


