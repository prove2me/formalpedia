-- Prove2me | Definitions.Def_N4Code_TwoColumn
-- name    : N4Code_TwoColumn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:16:59.418399+00:00
-- url     : https://prove2.me/theorems/178a31df-c50c-416c-815e-cb51e166a292
-- title:
--   Two Column
-- statement:
--   Definitions and structural lemmas for Two Column, from Shenghao Yang, Yanyan Dong (shhyang/n4code_lean; see pinned Apache-2.0 LICENSE)'s pinned N4Code: optimal finite-length block codes of size four for binary symmetric channels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean

import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
namespace N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
def mInd {n : ℕ} (C : Code n) (j : Fin 4) (w : Word n) (u : Fin n) : ℕ :=
  if colBit j (C u) ≠ w u then 1 else 0
noncomputable def pickSubset {n : ℕ} (s : Finset (Fin n)) (k : ℕ) (hk : k ≤ s.card) :
    Finset (Fin n) :=
  Classical.choose (Finset.powersetCard_nonempty_of_le hk)
def tableZ (a1 a2 a3 a4 a5 a6 a7 : ℕ) (i : ℕ) : ℕ :=
  if i = 1 then a1 else if i = 2 then a2 else if i = 3 then a3
  else if i = 4 then a4 else if i = 5 then a5 else if i = 6 then a6
  else if i = 7 then a7 else 0
end N4Code


