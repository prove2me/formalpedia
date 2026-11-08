-- Prove2me | Definitions.Def_AvoidPlast_encZoS
-- name    : AvoidPlast_encZoS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:39.95769+00:00
-- url     : https://prove2.me/theorems/5beee413-6258-4421-8062-bee110d5ac7e
-- title:
--   Explicit input $(|F|,m,d,|H|)$
-- statement:
--   The explicit input of Theorem 4.5: $|F|$, $m$ and $|H|$ in binary with doubled bits, each followed by the separator $01$, and then $d$ in binary, most significant bit first. Writing $d$ last and most significant bit first lets a verifier see in time polynomial in $(m,\log|F|)$ whether $d\ge m|F|$, in which case the degree bound is void, so an astronomically large $d$ costs nothing.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.5, p.18

import Mathlib

namespace AvoidPlast

/-- The explicit input `(|F|, m, d, |H|)` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 4.5, p.18, "the integers `|F|, m, d, |H|` are
represented in binary"): `|F|`, `m` and `|H|` with doubled bits, each followed by the separator `01`,
and then `d` in binary, most significant bit first. -/
def encZoS (Q m d h : ℕ) : List Bool :=
  let dbl : ℕ → List Bool := fun k => (Nat.bits k).flatMap (fun b => [b, b]) ++ [false, true]
  dbl Q ++ dbl m ++ dbl h ++ (Nat.bits d).reverse

end AvoidPlast


