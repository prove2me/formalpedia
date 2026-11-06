-- Prove2me | Definitions.Def_DecodablePOMDP_Code
-- name    : DecodablePOMDP_Code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:48.383669+00:00
-- url     : https://prove2.me/theorems/bfabc987-b4d8-478d-b02a-1c67111e8241
-- title:
--   Binary code of an instance (the input size)
-- statement:
--   The **code** of an instance is the binary word
--
--   $$\langle H\rangle\langle S\rangle\langle A\rangle\langle O\rangle\ \langle\mu_1\rangle\ \langle T\rangle\ \langle K\rangle\ \langle r\rangle\ \langle\varepsilon\rangle,$$
--
--   where natural numbers are written with the self-delimiting binary code $\langle n\rangle$ (unary bit-length, a separator, binary digits) and every rational entry with its sign, binary numerator and binary denominator, in index order. The **input size** $n$ of Theorem 1 is the length of this word.
--
--   Every entry of every table is written, so $n$ grows with the number of entries and with their bit sizes, as the bit model requires.
--
--   **Formalization Note** The number and rational codes are the published `ExponomialAssortment.FPTAS.encodeNat` and `encodeRat`.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Theorem 1, p.4 ("poly(input size)"); App. A.9, p.20 ("input bit complexity of K")

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_DecodablePOMDP_Instance

namespace DecodablePOMDP

open ExponomialAssortment.FPTAS

/-- Concatenation of the codes of a finite family, in index order. -/
def encVec {n : ℕ} (f : Fin n → List Bool) : List Bool :=
  (List.ofFn f).flatten

/-- **Binary code of an instance** ("input size", Theorem 1, p.4): the self-delimiting binary codes
of `H, S, A, O` (`encodeNat`), then every entry of `μ₁`, `T`, `K`, `r` in index order and finally
`ε` (`encodeRat`: sign, binary numerator, binary denominator). Its length is the input size `n`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Theorem 1, p.4 ("poly(input size)") and
App. A.9, p.20 ("the input bit complexity of K").

**Formalization Note.** The codes are the published `ExponomialAssortment.FPTAS.encodeNat` and
`encodeRat` (binary, never unary); every entry of every table is written, so the length grows with
`S²AH`, `SOH`, `OH` and the bit sizes of the entries. -/
def encodeInstance (I : Instance) : List Bool :=
  encodeNat I.H ++ encodeNat I.S ++ encodeNat I.A ++ encodeNat I.O ++
  encVec (fun s => encodeRat (I.μ₁ s)) ++
  encVec (fun i => encVec (fun s => encVec (fun a => encVec (fun s' => encodeRat (I.T i s a s'))))) ++
  encVec (fun i => encVec (fun s => encVec (fun y => encodeRat (I.K i s y)))) ++
  encVec (fun i => encVec (fun y => encodeRat (I.r i y))) ++
  encodeRat I.ε

end DecodablePOMDP


