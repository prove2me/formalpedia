-- Prove2me | Definitions.Def_MatchVec3_reduceList
-- name    : MatchVec3_reduceList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:53.221295+00:00
-- url     : https://prove2.me/theorems/c12258a2-23ae-42dc-a4e2-3c096c77a2b5
-- title:
--   A list of vectors read modulo a divisor
-- statement:
--   For $d\mid m$ and a list $U=(u_1,\dots,u_K)$ in $\mathbb Z_m^n$, this is the same list in $\mathbb Z_d^n$, obtained by reducing every coordinate modulo $d$.
--
--   It expresses the phrase "the same lists remain a matching vector family" in the minimal-modulus reduction.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Lemma 2.3, p.9

import Mathlib

namespace MatchVec3

/-- The same list read modulo a divisor `d ∣ m`, coordinate by coordinate (Aggarwal, Obremski, STOC
2027 submission (manuscript sha256 44199413…), Lemma 2.3, p.9: "the same lists remain a matching
vector family"). -/
def reduceList {m d n K : ℕ} (hd : d ∣ m) (U : Fin K → Fin n → ZMod m) :
    Fin K → Fin n → ZMod d :=
  fun i t => ZMod.castHom hd (ZMod d) (U i t)

end MatchVec3


