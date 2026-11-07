-- Prove2me | Definitions.Def_EulerSparsify_joinW
-- name    : EulerSparsify_joinW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:33.760804+00:00
-- url     : https://prove2.me/theorems/ad4195ae-cbcf-4c23-863f-589f9c163f7c
-- title:
--   Joining encoding words by the separator 3 (and the length-prefixed word list of naturals)
-- statement:
--   An encoding is a list of words over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits `0`, `1`, `2` inside a rational, `3` separator). `joinW ws` joins the words `ws` by the separator `3`; `tokNatList l` is the length-prefixed list (published `ReserveLB.tokList`) of the binary words of the natural numbers in `l`. These helpers build the binary input and output encodings of the polynomial-time clauses of Theorem 1.2, Lemma 4.2, Proposition 4.3 and Lemma 5.10.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Theorem 1.2, p.2; Lemma 4.2, p.12; Proposition 4.3, p.13; Lemma 5.10, p.22

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_ReserveLB_tokList

namespace EulerSparsify

/-- **Join words by the separator symbol `3`** (encoding helper for the polynomial-time clauses of
Theorem 1.2, p.2, Lemma 4.2, p.12, Proposition 4.3, p.13, Lemma 5.10, p.22).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…).
An encoding is a list of words (each over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`)
joined by the separator `3`; lists of words are length-prefixed with the published
`ReserveLB.tokList`.
**Formalization Note.** "Polynomial time" is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `2` inside a rational, `3` separator). Numbers are binary (published
`OnlineCRS.Combine.encNat`, `encInt`, `encRat`), so the length of an encoding is the usual bit size.
Every list is preceded by its length and no word contains the separator `3`, so the encodings are
injective. -/
def joinW (ws : List (List OnlineCRS.Combine.Sym)) : List OnlineCRS.Combine.Sym :=
  [3].intercalate ws

/-- The words of a list of natural numbers (binary), length first. -/
def tokNatList (l : List ℕ) : List (List OnlineCRS.Combine.Sym) :=
  ReserveLB.tokList (fun k => [OnlineCRS.Combine.encNat k]) l

end EulerSparsify


