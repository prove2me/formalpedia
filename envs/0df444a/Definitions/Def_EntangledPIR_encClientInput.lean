-- Prove2me | Definitions.Def_EntangledPIR_encClientInput
-- name    : EntangledPIR_encClientInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:18.658181+00:00
-- url     : https://prove2.me/theorems/96f0fdfb-03b2-4651-a4bf-df0c7b923bc8
-- title:
--   Encoding of the inputs and outputs of the client
-- statement:
--   The client's input is encoded as a list of symbols, each a bit or a separator: $n,m,\lambda$ in unary, then the index, the random string, and the messages of the servers. The output is encoded likewise. Both encodings are injective, which the polynomial-time clause needs.
--
--   **Formalization Note** Injectivity is proved in the verification file. Mathlib's `TM2ComputableInPolyTime` places no condition on an encoding, and a non-injective one would trivialize the clause.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 5.4(i), p.27

import Definitions.Def_EntangledPIR_clientStep

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), Lemma 5.4(i), p.27:
the encoding of the client's inputs and outputs for the polynomial-time statement.
-/

namespace EntangledPIR

/-- The alphabet of the encodings: a bit, and a separator. -/
inductive ClientSym
  | bit (b : Bool)
  | sep
  deriving DecidableEq

/-- A list of bit strings, each followed by a separator. -/
def encodeFields (l : List (List Bool)) : List ClientSym :=
  l.flatMap fun u => u.map ClientSym.bit ++ [ClientSym.sep]

/-- **The encoding of the client's input**: `n`, `m`, `λ` in unary, then the index, the random string and
the messages. Injective (the verification file proves it). -/
def encClientInput (inp : ClientInput) : List ClientSym :=
  encodeFields
    ([List.replicate inp.n true, List.replicate inp.m true, List.replicate inp.lam true, inp.x, inp.tape] ++
      inp.srv.flatMap fun p => [p.1, p.2])

/-- **The encoding of the client's output**: its messages, then a flag and, for an output, the output.
Injective (the verification file proves it). -/
def encClientOutput (o : ClientOutput) : List ClientSym :=
  encodeFields
    ([o.toA, o.toB] ++ match o.out with
      | none => [[false]]
      | some u => [[true], u])

end EntangledPIR


