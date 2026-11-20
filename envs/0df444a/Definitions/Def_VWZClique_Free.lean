-- Prove2me | Definitions.Def_VWZClique_Free
-- name    : VWZClique_Free
-- status  : Definition
-- author  : @orz
-- created : 2026-11-20T00:59:16.055192+00:00
-- url     : https://prove2.me/theorems/f98b084a-7a17-482d-a79d-3cfb2890c42c
-- title:
--   Reconstructing two pivot pairs from the free coordinates
-- statement:
--   Two Boolean strings on the nonexceptional coordinates expand into the four full pivot words.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Lemma 3.2, proof. https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_Operators

namespace VWZClique
abbrev Free {L : ℕ} (m : Mask L) := {i : Fin L // m i = none} → Bool

def fill {L : ℕ} (m : Mask L) (slot : (Bool × Bool × Bool × Bool) → Bool)
    (p : Free m) : Bits L :=
  fun i => if h : m i = none then p ⟨i,h⟩
           else slot ((m i).get (Option.isSome_iff_ne_none.mpr h))

def expand {L : ℕ} (m : Mask L) (pq : Free m × Free m) : PairBits L × PairBits L :=
  ((fill m Prod.fst pq.1, fill m (fun r => r.2.1) pq.2),
   (fill m (fun r => r.2.2.1) pq.2, fill m (fun r => r.2.2.2) pq.1))
end VWZClique


