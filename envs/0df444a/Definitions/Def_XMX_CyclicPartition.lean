-- Prove2me | Definitions.Def_XMX_CyclicPartition
-- name    : XMX_CyclicPartition
-- status  : Definition
-- author  : @visuddhi
-- created : 2026-10-08T17:02:26.555864+00:00
-- url     : https://prove2.me/theorems/ebdf830e-3b75-4319-8089-735bb77a337f
-- title:
--   Cyclic anchor-offset indexing of product samples
-- statement:
--   For residues modulo N, a tuple has first coordinate anchor and remaining coordinates anchor+offset[j]. Positive N is imposed by the theorem; the definition also has the total ZMod 0 interpretation.
-- source:
--   Yaqi Xie, Will Ma, Linwei Xin, VC Theory for Inventory Policies, arXiv:2404.11509v3 (2026-02-01), Lemma 4.12

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
namespace XMX

/-- A cyclic group of product indices, with first coordinate as anchor. -/
def cyclicTuple (N d : ℕ) (anchor : ZMod N) (offset : Fin d → ZMod N) :
    Fin (d + 1) → ZMod N :=
  Fin.cons anchor (fun j => anchor + offset j)

end XMX


