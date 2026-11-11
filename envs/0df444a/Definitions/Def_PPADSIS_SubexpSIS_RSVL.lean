-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_RSVL
-- name    : PPADSIS_SubexpSIS_RSVL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:49:07.734191+00:00
-- url     : https://prove2.me/theorems/9f659050-4a81-4e33-bdd1-2b4862e92e4a
-- title:
--   Relaxed Sink-of-Verifiable-Line: instances, promise, solutions and hard distributions (Definition 3.1)
-- statement:
--   An instance of **Relaxed Sink-of-Verifiable-Line (RSVL)** (Definition 3.1) consists of a successor circuit $S:\{0,1\}^m\to\{0,1\}^m$, a verifier circuit $V:\{0,1\}^m\times[0,2^m-1]\to\{0,1\}$, an integer $L\in[0,2^m-1]$ and a string $v_0\in\{0,1\}^m$. **Promise:** for every $i\in[0,L]$,
--   $$V\bigl(S^i(v_0),i\bigr)=1 .$$
--   **Solutions:** a sink, i.e. a vertex $v$ with $V(v,L)=1$; or a false positive, i.e. a pair $(v,i)\in\{0,1\}^m\times[0,2^m-1]$ with $V(v,i)=1$ and $v\ne S^i(v_0)$. Solutions need not be efficiently checkable. A **hard distribution of RSVL** is a hard distribution (p. 21) of this search problem.
--
--   **Formalization Note** The verifier reads the index $i$ as $m$ bits, big-endian, after the vertex, so it has $2m$ inputs and one output; the arities and $L<2^m$ are part of the promise. A solution is output as the string $0v$ (sink) or $1\,v\,\mathrm{bin}_m(i)$ (false positive). The description of an instance is `encNat m`, the descriptions of $S$ and $V$, `encNat L` and `encStr v0`.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 20, Definition 3.1; p. 21 (hard distributions)

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Circuit
import Definitions.Def_PPADSIS_SubexpSIS_HardDistribution

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- An **instance of Relaxed Sink-of-Verifiable-Line** (Choudhuri, *PPAD Hardness from SIS*, STOC
2027 submission (manuscript sha256 17abad73…), Definition 3.1, p. 20): a successor circuit
`S : {0,1}^m → {0,1}^m`, a verifier circuit `V : {0,1}^m × [0, 2^m − 1] → {0,1}`, an integer
`L ∈ [0, 2^m − 1]` and a string `v0 ∈ {0,1}^m`. The verifier reads the index `i` as `m` bits,
big-endian, after the vertex. -/
structure RSVLInstance where
  m : ℕ
  S : Circuit
  V : Circuit
  L : ℕ
  v0 : List Bool

/-- The arities of Definition 3.1: `S` has `m` inputs and `m` outputs, `V` has `2m` inputs and one
output, `L ≤ 2^m − 1`, and `|v0| = m`. -/
def RSVLInstance.WF (I : RSVLInstance) : Prop :=
  I.S.WF ∧ I.S.nIn = I.m ∧ I.S.outs.length = I.m ∧
  I.V.WF ∧ I.V.nIn = 2 * I.m ∧ I.V.outs.length = 1 ∧
  I.L < 2 ^ I.m ∧ I.v0.length = I.m

/-- `V(v, i) = 1`. -/
def RSVLInstance.accepts (I : RSVLInstance) (v : List Bool) (i : ℕ) : Prop :=
  I.V.eval (v ++ bitsBE I.m i) = [true]

/-- `S^i(v0)`, the `i`-fold application of the successor. -/
def RSVLInstance.iter (I : RSVLInstance) (i : ℕ) : List Bool := (I.S.eval)^[i] I.v0

/-- The **promise** of Definition 3.1: `V(S^i(v0), i) = 1` for every `i ∈ [0, L]` (with the arities
`WF`). -/
def RSVLInstance.Promise (I : RSVLInstance) : Prop :=
  I.WF ∧ ∀ i ≤ I.L, I.accepts (I.iter i) i

/-- A **solution** of an RSVL instance (Definition 3.1), as an output string:
1. sink: `false :: v` for a vertex `v ∈ {0,1}^m` with `V(v, L) = 1`;
2. false positive: `true :: (v ++ bitsBE m i)` for a pair `(v, i) ∈ {0,1}^m × [0, 2^m − 1]` with
   `V(v, i) = 1` and `v ≠ S^i(v0)`. -/
def RSVLInstance.IsSolution (I : RSVLInstance) (y : List Bool) : Prop :=
  (∃ v : List Bool, y = false :: v ∧ v.length = I.m ∧ I.accepts v I.L) ∨
  (∃ (v : List Bool) (i : ℕ), y = true :: (v ++ bitsBE I.m i) ∧ v.length = I.m ∧
    i < 2 ^ I.m ∧ I.accepts v i ∧ v ≠ I.iter i)

/-- The **description** of an RSVL instance: `encNat m`, the descriptions of `S` and `V`,
`encNat L`, and `encStr v0`. -/
def RSVLInstance.enc (I : RSVLInstance) : List Bool :=
  encNat I.m ++ I.S.enc ++ I.V.enc ++ encNat I.L ++ encStr I.v0

/-- A **hard distribution of RSVL** (p. 21): a polynomial-time sampler `D(1^λ)` that, for all
sufficiently large `λ`, outputs only instances satisfying the promise, and on which every
non-uniform polynomial-size probabilistic adversary outputs a solution with negligible
probability. -/
def IsHardRSVL (D : CoinAlg unary) : Prop :=
  IsHardDistribution RSVLInstance.enc RSVLInstance.Promise RSVLInstance.IsSolution D

end PPADSIS.SubexpSIS


