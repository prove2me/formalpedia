-- Prove2me | Definitions.Def_IntMul_Kappa_R8_OppbankRankFast
-- name    : IntMul_Kappa_R8_OppbankRankFast
-- status  : Definition
-- author  : @immiq
-- created : 2026-11-25T07:21:51.946142+00:00
-- url     : https://prove2.me/theorems/e9ed212c-8f68-43dc-aaf6-cde340df29fa
-- title:
--   Star and private-coordinate rank checks for R8
-- statement:
--   This alternative rank checker uses structural certificates for supports with a common centre. A graph with a spanning star and an extra edge has full rank on its active coordinates. When every triple has a coordinate unique to it, the triple vectors are independent. Sparse elimination handles the remaining supports.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

namespace IntMul.Kappa.R8.Bit.Oppbank.RankCheck

open Module Submodule Matrix Pnd SupG Cent

def active (sup : ℕ) (c : Fin 23) : List (Fin 23) :=
  (List.finRange 23).filter fun p => (p != c) && (sup &&& starC p.val != 0)

def hub (sup : ℕ) (es : List (Fin 23)) : Option (Fin 23) :=
  es.find? fun a =>
    let incident := sup &&& starC a.val
    (incident != sup) && es.all (fun p => p == a || (incident &&& starC p.val != 0))

def hubTest (n sup : ℕ) : Bool :=
  if hc : centF n < 23 then
    let c : Fin 23 := ⟨centF n, hc⟩
    let es := active sup c
    (sup < 2^1771) && centredStar sup c.val && (es.length == dimF n) && (hub sup es).isSome
  else false

def leafPart (sup : ℕ) (p : Fin 23) : ℕ :=
  let m := sup &&& starC p.val
  if (m != 0) && ((m &&& (m-1)) == 0) then m else 0

def leafCover (sup : ℕ) : ℕ :=
  (List.finRange 23).foldr (fun p r => leafPart sup p ||| r) 0

def leafTest (n sup : ℕ) : Bool :=
  if hc : centF n < 23 then
    (sup < 2^1771) && centredStar sup (⟨centF n,hc⟩ : Fin 23).val &&
    (leafCover sup == sup) &&
    let is := bitIndices 1771 sup
    (is.length == dimF n) && decide is.Nodup
  else false


noncomputable def nodeFast (n : ℕ) : Bool :=
  let sup := densSupG n
  hubTest n sup || leafTest n sup || nodeCheck n

end IntMul.Kappa.R8.Bit.Oppbank.RankCheck


