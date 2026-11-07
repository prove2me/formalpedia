-- Prove2me | Definitions.Def_SubexpPrimes_PolyInstance
-- name    : SubexpPrimes_PolyInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:59:41.441511+00:00
-- url     : https://prove2.me/theorems/3a15136e-318b-44be-8b49-634b4ffff3b2
-- title:
--   An instance of the contraction over $R_{P,\ell}$
-- statement:
--   An instance consists of a network description, whose data field holds the input from which the network is produced, the scale $s$, and the parameters $P$ and $\ell$; $N$ is the length of its encoding. A machine computes the entries in $R_{P,\ell}$ if on the instance, a vertex and a local assignment, it outputs the $\ell$ coefficients of the entry.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem A.2, p.43; Lemma A.23, p.74

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_digitPoly

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- **An instance of the contraction over `R_{P,ℓ}`** — Gajulapalli, *Deterministic Construction
of Primes in Subexponential Time* (manuscript, sha256 6ad4d3de…), Theorem A.2, p.43, and
Lemma A.23, p.74: a network description (whose `data` field holds "the input from which G is
produced"), the scale `s`, and the parameters `P`, `ℓ`. -/
structure PolyInstance where
  /-- the network -/
  D : NetDesc
  /-- the scale -/
  s : ℕ
  /-- the precision `P` -/
  P : ℕ
  /-- the truncation order `ℓ` -/
  ℓ : ℕ

namespace PolyInstance

/-- The encoding of an instance; `N := I.encode.length` is the input length of Theorem A.2. -/
def encode (I : PolyInstance) : List Bool :=
  Encoding.encodeList id [I.D.encode, Encoding.encodeNat I.s, Encoding.encodeNat I.P,
    Encoding.encodeNat I.ℓ]

/-- **"Each entry `T_v(·)` can be computed in time `τ` and space `σ`"** (p.43), for entries in
`R_{P,ℓ}`: on the input (instance, vertex, local assignment) the machine `E` halts with the word of
`T v z ∈ R_{P,ℓ}` on tape `out`. -/
def EntryComputes (I : PolyInstance) (E : PrimitiveMachine) (out : Fin E.tapeCount)
    (T : I.D.Tables (TruncPoly I.P)) (τ σ : ℝ) : Prop :=
  ∀ (v : Fin I.D.n) z, RunsWithin E out
    (Encoding.encodeList id [I.encode, Encoding.encodeNat v, I.D.incidentBits v z])
    (truncWord I.ℓ (T v z)) τ σ

end PolyInstance

end SubexpPrimes


