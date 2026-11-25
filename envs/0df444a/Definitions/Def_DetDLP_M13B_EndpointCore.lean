-- Prove2me | Definitions.Def_DetDLP_M13B_EndpointCore
-- name    : DetDLP_M13B_EndpointCore
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:33:39.308989+00:00
-- url     : https://prove2.me/theorems/7b23656a-06e8-40d1-9209-b1ea0bd6d9bf
-- title:
--   DetDLP M13B EndpointCore
-- statement:
--   A finite scan recovers ordered endpoint pairs from a radix word terminated by a unit digit. A side word then orients the edges, and the ordered Cartesian square of the resulting list gives the four power-minus-one fields required for balanced labeling.

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false
namespace DetDLP.M13BEndpoint

abbrev Pair := ℕ × ℕ
abbrev State := ℕ × List Pair

def advance (b : ℕ) (s : State) : State :=
  if s.1 ≤ 1 then s else
    (s.1 / b / b, (s.1 % b, s.1 / b % b) :: s.2)

def unpack (b src : ℕ) : List Pair :=
  ((src.bits.foldl (fun s _ => advance b s) (src, [])).2).reverse

def orient (s : ℕ) (e : Pair) : Pair := if s.testBit e.1 then e.swap else e

def fields (q s : ℕ) (es : List Pair) : List ℕ :=
  let es' := es.map (orient s)
  es'.flatMap fun e => es'.flatMap fun f =>
    [(q+2)^e.1-1, (q+2)^f.1-1, (q+2)^e.2-1, (q+2)^f.2-1]

def output (q src b s D : ℕ) : List Bool :=
  (Nat.ofDigits D (fields q s (unpack b src) ++ [1])).bits

def raw (b : ℕ) (es : List Pair) : ℕ :=
  Nat.ofDigits b (es.flatMap (fun e => [e.1, e.2]) ++ [1])

def sideCode (bs : List Bool) : ℕ := Nat.ofDigits 2 (bs.map Bool.toNat ++ [1])

def graphPairs (G : BipartiteMultigraph) : List Pair :=
  (List.finRange G.nE).map (fun e => ((G.endpoints e).1.val,(G.endpoints e).2.val))

end DetDLP.M13BEndpoint


