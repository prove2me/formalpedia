-- Prove2me | Definitions.Def_WICanon_ProtocolProps
-- name    : WICanon_ProtocolProps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:03.487064+00:00
-- url     : https://prove2.me/theorems/c4fc4a22-b526-4013-8ba4-1a08404cf9b5
-- title:
--   Efficiency, public coin, deterministic prover, communication bounds
-- statement:
--   Properties of a protocol.
--
--   1. **PPT.** Polynomially many rounds and coins, and the next-message and decision functions are polynomial-time on their encoded inputs; the prover is given the witness.
--   2. **Deterministic prover.** The prover reads no coins.
--   3. **Public coin.** The verifier's tape splits into per-round blocks $r_{V,i}$, the message $\rho_i$ is an injective encoding of $r_{V,i}$, and the decision depends on $x$ and the whole transcript only.
--   4. **Communication bounds.** The encoded transcript length, the prover's message in each round, the prover's total, and the total of both parties.
--
--   Without the requirement on the prover, sending the lexicographically first witness would be a one-message statistical WI proof for every NP relation.
--
--   **Formalization Note** The printed definition of public coin is "$\rho_i=r_{V,i}$ and $st_{V,i}=\emptyset$". Taken with $\mathrm{Out}:=V^*(y,st_{V,k},m_k)$, this has the decision read $m_k$ alone, whereas the proof of Lemma 3.2 checks the whole interaction (p.28); the decision here is a function of $x$ and the transcript. The blocks may interleave and $\rho_i$ may be an encoding of $r_{V,i}$ so that OR-parallel repetition stays public coin. A protocol of this form becomes one with $\rho_i=r_{V,i}$ by letting the prover apply the encoding.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Definition 2.8, p.13; §2.3, p.13; Theorem 3.1, p.16; Lemma 3.2, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_WICanon_PolyBounds
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_Protocol

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QAdvFew.PoQOracle QiOPoQ

namespace Protocol

/-- **Prover and verifier are PPT** (Arnon, Mazor, Pass, Silbak, STOC 2027 submission manuscript,
sha256 3f78ec3d…, Definition 2.8, p.13: "a pair of PPT interactive machines"; the prover is given
the witness): polynomially many rounds and coins, and each of the three next-message and decision
functions is polynomial-time on its encoded input.

**Formalization Note.** A running time polynomial in the length of the input, messages included, is
the model of `PolyTimeComputable`. An honest execution has polynomially long messages (they are
outputs of the same polynomial-time maps) when `rounds` is constant, and the transcript bounds of
the statements below carry it otherwise. Without this predicate on the prover, sending the
lexicographically first witness would be a one-message statistical WI proof for every NP relation. -/
def IsEfficient (pv : Protocol) : Prop :=
  IsPolyLen pv.rounds ∧ IsPolyLen pv.coinsP ∧ IsPolyLen pv.coinsV ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ x rV ms, g (pair x (pair rV (tup ms))) = pv.verMsg x rV ms) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ x w rP ρs, g (pair x (pair w (pair rP (tup ρs)))) = pv.proverMsg x w rP ρs) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ x rV tr, g (pair x (pair rV (tup tr))) = bitStr (pv.accept x rV tr))

/-- A deterministic prover: it reads no coins (§3, Theorem 3.1, p.16; proof, p.23: "the prover is
deterministic, and as such also stateless"). -/
def IsDeterministicProver (pv : Protocol) : Prop := ∀ n, pv.coinsP n = 0

/-- The bits of the tape `rV` at the positions that `block` assigns to round `i`. -/
def coinBlock (block : ℕ → ℕ) (i : ℕ) (rV : Str) : Str :=
  ((List.zipIdx rV).filter fun p => block p.2 = i).map Prod.fst

/-- **Public coin** (§2.3, p.13: "The protocol is public-coin if for every i, ρi = rV,i and
stV,i = ∅").

**Formalization Note.** Three readings, each declared where it is used.
(1) Printed with `Out := V*(y, stV,k, mk)` the empty state would make the decision read `m_k` only.
The proof of Lemma 3.2 has the verifier check the whole interaction ("accepts if all of the replies
to challenges are accepting", p.28), so the decision is a function of `x` and the whole transcript:
`accept` does not depend on `rV`.
(2) `r_V = (r_{V,1}, …, r_{V,k})` is a partition of the tape into per-round blocks; `block` says
which positions go to which round, so that a parallel repetition, whose rounds interleave the tapes
of its copies, stays public coin.
(3) `ρ_i` is an injective encoding of `r_{V,i}` that depends on `x`, `i` and `r_{V,i}` only. The
printed case is the identity encoding. A protocol of this form becomes one with `ρ_i = r_{V,i}` by
letting the prover apply the encoding, so the class of relations with public-coin protocols does not
change. -/
def IsPublicCoin (pv : Protocol) : Prop :=
  ∃ (block : ℕ → ℕ → ℕ) (enc : Str → ℕ → Str → Str),
    (∀ x i, Set.InjOn (enc x i) {s | s.length =
      ((List.range (pv.coinsV x.length)).filter fun p => block x.length p = i).length}) ∧
    (∀ x rV ms, rV.length = pv.coinsV x.length → ms.length < pv.rounds x.length →
      pv.verMsg x rV ms = enc x ms.length (coinBlock (block x.length) ms.length rV)) ∧
    ∀ x r r' tr, pv.accept x r tr = pv.accept x r' tr

/-- `L` bounds the length of the encoded transcript of honest executions on `R` ("ℓ denote a
polynomial upper bound on the length of the transcript", Theorem 3.1, p.16). -/
def TranscriptBound (pv : Protocol) (R : Relation) (L : ℕ → ℕ) : Prop :=
  ∀ x w rP rV, R x w → rP.length = pv.coinsP x.length → rV.length = pv.coinsV x.length →
    (tup (pv.transcript x w rP rV)).length ≤ L x.length

/-- `L` bounds the prover's message in each round ("ℓP denote a polynomial upper bound on the total
communication sent by P in each round", Theorem 3.1, p.16). -/
def PerRoundProverBound (pv : Protocol) (R : Relation) (L : ℕ → ℕ) : Prop :=
  ∀ x w rP rV, R x w → rP.length = pv.coinsP x.length → rV.length = pv.coinsV x.length →
    ∀ m ∈ pv.proverReplies x w rP rV, m.length ≤ L x.length

/-- `L` bounds the total prover-to-verifier communication (Lemma 3.2, p.17; Theorem 2.11, p.14). -/
def TotalProverBound (pv : Protocol) (R : Relation) (L : ℕ → ℕ) : Prop :=
  ∀ x w rP rV, R x w → rP.length = pv.coinsP x.length → rV.length = pv.coinsV x.length →
    ((pv.proverReplies x w rP rV).map List.length).sum ≤ L x.length

/-- `L` bounds the total communication of both parties (Lemma 3.2, p.17). -/
def TotalCommBound (pv : Protocol) (R : Relation) (L : ℕ → ℕ) : Prop :=
  ∀ x w rP rV, R x w → rP.length = pv.coinsP x.length → rV.length = pv.coinsV x.length →
    ((pv.transcript x w rP rV).map List.length).sum ≤ L x.length

end Protocol

end WICanon


