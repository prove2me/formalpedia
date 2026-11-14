-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_PottsRowChain
-- name    : ZeroFreeRRG_Hardcore_PottsRowChain
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T09:16:59.60004+00:00
-- url     : https://prove2.me/theorems/01fc82c0-0ffb-42e6-96e3-f1cc989660fc
-- title:
--   Symmetric Potts edge-row replacement
-- statement:
--   On a finite set of edges, this operation symmetrically replaces row $a$ of each interaction matrix by row $b$ of its original matrix, leaving all other entries unchanged.
-- source:
--   Auxiliary construction for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsSegment
import Mathlib
open scoped Classical
namespace ZeroFreeRRG.Hardcore

open Classical in
/-- Replace row a by old row b symmetrically on a prescribed set of edges. -/
noncomputable def pottsReplaceRows {V : Type} {q : ℕ}
    (W : Sym2 V → Fin q → Fin q → ℂ) (F : Finset (Sym2 V)) (a b : Fin q)
    (e : Sym2 V) (i j : Fin q) : ℂ :=
  if e ∈ F then if i=a then W e b j else if j=a then W e b i else W e i j else W e i j

end ZeroFreeRRG.Hardcore


