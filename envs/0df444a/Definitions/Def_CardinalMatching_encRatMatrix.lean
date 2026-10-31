-- Prove2me | Definitions.Def_CardinalMatching_encRatMatrix
-- name    : CardinalMatching_encRatMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:53.164635+00:00
-- url     : https://prove2.me/theorems/ef6974e2-a17a-4ca6-95c7-505c489c41d7
-- title:
--   Binary encoding of rational vectors and $n\times n$ rational matrices
-- statement:
--   The computational problems of the mission take rational data written in binary. A rational vector $v\in\mathbb Q^n$ is encoded as the self-delimiting binary code of $n$ followed by the codes of $v_1,\dots,v_n$; an $n\times n$ rational matrix $u$ is encoded as the code of $n$ followed by the codes of its $n^2$ entries in row-major order. A rational number is encoded by its reduced numerator (sign bit and magnitude) and denominator, using the platform's reviewed `encBin`/`encRat`.
--
--   Every code is self-delimiting, so a bit string encodes at most one vector or matrix. "The string $s$ encodes an instance" is therefore stated as the existence of a preimage, with no decoder.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, p.2 (rational, non-negative utilities); encodings of the search problems of Theorems 8, 9, p.6

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace CardinalMatching

open QAlgorithms.LocalHamiltonian

/-- **Binary encoding of a rational vector** of length `n`: `n` in self-delimiting binary
(`encBin`), followed by the entries `v 0, …, v (n−1)`, each as a rational (`encRat`: the
sign-and-magnitude binary numerator, then the binary denominator of the reduced fraction).

Used for the inputs and outputs of the search problems of Tröbst–Vazirani, *Cardinal-Utility
Matching Markets*, arXiv:2402.08851v6, §2.2 (Theorems 8, 9, p.6) and Lemma 6 (p.6), whose data
are rational (p.2: "rational, non-negative utilities").

**Formalization Note** The encoding is the platform's reviewed `encBin`/`encRat`; every code is
self-delimiting, so a string encodes at most one `(n, v)`. No decoder is needed: "the string `s`
encodes a vector" is stated as `∃ n v, s = encRatVec n v`, which is total. -/
def encRatVec (n : ℕ) (v : Fin n → ℚ) : List Bool :=
  encBin n ++ (List.finRange n).flatMap (fun j => encRat (v j))

/-- **Binary encoding of an `n × n` rational matrix**: `n` in self-delimiting binary, followed by
the `n²` entries in row-major order, each as a rational (`encRat`). Same source and conventions
as `encRatVec`. -/
def encRatMatrix (n : ℕ) (u : Fin n → Fin n → ℚ) : List Bool :=
  encBin n ++ (List.finRange n).flatMap (fun i => (List.finRange n).flatMap (fun j => encRat (u i j)))

end CardinalMatching


