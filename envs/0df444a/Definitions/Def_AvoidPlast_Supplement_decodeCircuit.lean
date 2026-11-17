-- Prove2me | Definitions.Def_AvoidPlast_Supplement_decodeCircuit
-- name    : AvoidPlast_Supplement_decodeCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:12:10.794203+00:00
-- url     : https://prove2.me/theorems/3b1a8b08-5117-4084-84bf-1076cdc1ba68
-- title:
--   The fixed circuit encoding ("$C$ of size $n$")
-- statement:
--   A circuit of *size* $n$ is an $n$-bit description: $1^w0$, then the numbers of inputs, gates and outputs in $w$ bits each, then the gate records ($2$ operation bits and two $w$-bit argument wires each), then the $w$-bit output wires; trailing bits are padding. A description too short for its header decodes to nothing.
--
--   **Formalization Note** Fixed-width fields make descriptions parseable in linear time in the RAM model, which the proof of Theorem 7.2 needs: its distinguisher evaluates the circuit in linear time.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 7.2, p.40

import Mathlib
import Definitions.Def_UniqueOptScores_decodeNat
import Definitions.Def_AvoidPlast_Supplement_Circuit

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The fixed circuit encoding: "`C` of size `n`" is an `n`-bit description (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem
7.2, p.40). A description is `1^w 0`, then the numbers `a` (inputs), `g` (gates), `o` (outputs) in
`w` bits each, then `g` gate records of `2 + 2w` bits (two operation bits: `1·` NOT, `01` OR, `00`
AND; two `w`-bit argument wires), then `o` output wires of `w` bits; trailing bits are padding.
Numbers are read least significant bit first. A description too short for its header is `none`.

**Formalization Note** Fixed-width fields make the description parseable in linear time on the
RAM model, which the proof of Theorem 7.2 needs (its distinguisher evaluates `C` in linear time). -/
def decodeCircuit (c : List Bool) : Option Circuit :=
  let w := (c.takeWhile (· = true)).length
  let b := c.drop (w + 1)
  let field := fun (l : List Bool) (j : ℕ) => UniqueOptScores.decodeNat ((l.drop (j * w)).take w)
  let a := field b 0
  let g := field b 1
  let o := field b 2
  let rest := b.drop (3 * w)
  if w + 1 + 3 * w + g * (2 + 2 * w) + o * w ≤ c.length then
    some
      { nIn := a
        gates := (List.range g).map fun j =>
          let r := (rest.drop (j * (2 + 2 * w))).take (2 + 2 * w)
          ((if r.getD 0 false then 2 else if r.getD 1 false then 1 else 0 : Fin 3),
            UniqueOptScores.decodeNat ((r.drop 2).take w), UniqueOptScores.decodeNat (r.drop (2 + w)))
        outs := (List.range o).map fun j =>
          UniqueOptScores.decodeNat (((rest.drop (g * (2 + 2 * w))).drop (j * w)).take w) }
  else none

end AvoidPlast.Supplement


