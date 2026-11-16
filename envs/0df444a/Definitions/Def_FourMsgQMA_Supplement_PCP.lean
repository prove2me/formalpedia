-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_PCP
-- name    : FourMsgQMA_Supplement_PCP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:17:52.617483+00:00
-- url     : https://prove2.me/theorems/ed18e20b-f1f2-4d95-9cec-1a3001e7e068
-- title:
--   Bounded relations and nonadaptive PCPs with a full-proof decoder (Def 3.24)
-- statement:
--   A **relation** $R(u,w)$ is a fixed, uniformly computable predicate with declared polynomial bounds $n(\lambda)$ on the instance and $m(\lambda)$ on the witness.
--
--   A **nonadaptive PCP** for $R$ is a tuple $(\mathrm{Prove},\mathrm{Query},\mathrm{Decide})$ with a declared polynomial proof length $M(\lambda)$: $\pi\leftarrow\mathrm{Prove}(1^\lambda,u,w)\in\{0,1\}^M$; $(Q,\mathrm{st}):=\mathrm{Query}(1^\lambda,u,q)$ for a uniform seed $q\in\{0,1\}^r$, returning an ordered list of proof positions and a state; and $\mathrm{Decide}(1^\lambda,u,\mathrm{st},a)\in\{0,1\}$ on the bits $a=\pi|_Q$. Write
--   $$
--   \mathrm{Acc}(u,\pi)=\Pr_q\big[\mathrm{Decide}(1^\lambda,u,\mathrm{st},\pi|_Q)=1\big].
--   $$
--
--   1. **Efficiency / succinct verification**: $r$, $|Q|$ and the state length are bounded by $\mathrm{poly}(\lambda,|u|,\log M)$, Query and Decide run in that time, and Prove and the decoder run in polynomial time.
--   2. **Completeness**: for every $R(u,w)=1$ within the declared bounds, $\mathbb E_\pi[\mathrm{Acc}(u,\pi)]\ge1-\mathrm{negl}(\lambda)$.
--   3. **Full-proof knowledge** (Definition 3.24) with knowledge error $\kappa$: there is a total classical decoder $\mathrm{Decode}(1^\lambda,u,\pi)$ such that for every $u$ and every $\pi\in\{0,1\}^M$ with $\mathrm{Acc}(u,\pi)>\kappa(\lambda)$, $R(u,\mathrm{Decode}(1^\lambda,u,\pi))=1$ with probability one.
--
--   These are the PCP hypotheses of Theorem 3.26.
--
--   **Formalization Note** The decoder is a field of the PCP structure, with explicit coins; positions are $0,\dots,M-1$; "poly time" is `PolyTimeComputable` on packed inputs carrying $M$ in binary.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.11 (p.22, PDF 24) and §3.12 with Definition 3.24, pp.22–23 (PDF 24–25)

import Mathlib
import Definitions.Def_FourMsgQMA_Supplement_HashFamily

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.11 (p.22, PDF 24: "A relation is a
fixed, uniformly computable predicate `R(u, w)` with declared input, witness, and running-time
bounds") and §3.12 with Definition 3.24 (pp.22–23, PDF 24–25): bounded relations, nonadaptive PCPs
`(Prove, Query, Decide)`, their completeness and succinct verification, and full-proof knowledge
with a decoder.

Pinned-down version (operator request): "PPT"/"time" are polynomial-time computability on packed
inputs and polynomial length bounds; the declared proof length `M(λ)` is a function of `λ` (it is an
input of Kilian's setup, which precedes the instance); proof positions are `0, …, M − 1`.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- A relation `R(u, w)` with declared input and witness bounds `n(λ)`, `m(λ)` (§3.11, p.22). -/
structure Relation where
  /-- The declared instance-length bound `n(λ)`. -/
  inLen : ℕ → ℕ
  /-- The declared witness-length bound `m(λ)`. -/
  witLen : ℕ → ℕ
  /-- The predicate `R(u, w)`. -/
  rel : Bits → Bits → Bool

/-- A relation is uniformly computable with polynomial declared bounds. -/
def Relation.Efficient (R : Relation) : Prop :=
  PolyBound R.inLen ∧ PolyBound R.witLen ∧
    ∃ g : Str → Str, PolyTimeComputable g ∧ ∀ u w, g (pack [u, w]) = [R.rel u w]

/-- A nonadaptive PCP with a full-proof decoder (§3.12, p.22; Definition 3.24). -/
structure PCP where
  /-- The declared proof length `M(λ)`. -/
  proofLen : ℕ → ℕ
  /-- The seed length `r(λ, |u|)`. -/
  seedLen : ℕ → ℕ → ℕ
  /-- The prover's coin length at `(λ, |u|)`. -/
  proveCoins : ℕ → ℕ → ℕ
  /-- `π ← Prove(1^λ, u, w)`, with coins. -/
  prove : ℕ → Bits → Bits → Bits → Bits
  /-- `(Q, st) := Query(1^λ, u, q)`, deterministic: the ordered proof positions and the state. -/
  query : ℕ → Bits → Bits → List ℕ × Bits
  /-- `Decide(1^λ, u, st, a) ∈ {0,1}`, deterministic; `a` lists the bits at the positions `Q`. -/
  decision : ℕ → Bits → Bits → Bits → Bool
  /-- The decoder's coin length at `(λ, |u|)`. -/
  decodeCoins : ℕ → ℕ → ℕ
  /-- `w ← Decode(1^λ, u, π)`, with coins: the total classical extractor of Definition 3.24. -/
  decode : ℕ → Bits → Bits → Bits → Bits

/-- `π|Q`: the bits of `π` at the ordered positions `Q`. -/
def restrictTo (π : Bits) (Q : List ℕ) : Bits := Q.map fun j => π.getD j false

/-- `Acc(u, π) = Pr_q[Decide(1^λ, u, st, π|Q) = 1]`, `(Q, st) := Query(1^λ, u, q)` (Definition 3.24). -/
noncomputable def PCP.acc (P : PCP) (lam : ℕ) (u π : Bits) : ℝ :=
  avgCoins (P.seedLen lam u.length) fun q =>
    if P.decision lam u (P.query lam u q).2 (restrictTo π (P.query lam u q).1) then 1 else 0

/-- Succinct verification and efficiency (§3.12, p.22; Definition 3.24): `M` is polynomial; one
polynomial `p` bounds at `P = p(λ, |u|, ⌈log₂(M + 1)⌉)` the seed length, the number of queried
positions, and the state length, every position is below `M`; `Query` and `Decide` are polynomial
time in their inputs, which carry `M` in binary (so their time is `poly(λ, |u|, log M)`); `Prove`
and `Decode` are polynomial time ("polynomial time in the full proof and relation bounds"), with
polynomially bounded coin lengths, and `Prove` outputs `M`-bit proofs. -/
def PCP.Efficient (P : PCP) : Prop :=
  PolyBound P.proofLen ∧
  (∃ p : MvPolynomial (Fin 4) ℕ, ∀ lam (u q : Bits),
    let B := eval4 p lam u.length (clog2 (P.proofLen lam + 1)) 0
    P.seedLen lam u.length ≤ B ∧ P.proveCoins lam u.length ≤ eval4 p lam u.length (P.proofLen lam) 0 ∧
      P.decodeCoins lam u.length ≤ eval4 p lam u.length (P.proofLen lam) 0 ∧
      (q.length = P.seedLen lam u.length →
        (P.query lam u q).1.length ≤ B ∧ (P.query lam u q).2.length ≤ B ∧
          ∀ j ∈ (P.query lam u q).1, j < P.proofLen lam)) ∧
  (∀ lam (u w c : Bits), (P.prove lam u w c).length = P.proofLen lam) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam m,
    g (pack [unary lam, binNat (P.proofLen lam), unary m]) =
      pack [unary (P.seedLen lam m), unary (P.proveCoins lam m), unary (P.decodeCoins lam m)]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam u q,
    g (pack [unary lam, binNat (P.proofLen lam), u, q]) =
      pack [pack ((P.query lam u q).1.map binNat), (P.query lam u q).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam u st a,
    g (pack [unary lam, binNat (P.proofLen lam), u, st, a]) = [P.decision lam u st a]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam u w c,
    g (pack [unary lam, u, w, c]) = P.prove lam u w c) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam u π c,
    g (pack [unary lam, u, π, c]) = P.decode lam u π c)

/-- Completeness (§3.12, p.22): there is a negligible `ν` such that for every `λ` and every
`R(u, w) = 1` within the declared bounds, `Pr[Decide(1^λ, u, st, π|Q) = 1] ≥ 1 − ν(λ)` over
`π ← Prove(1^λ, u, w)` and the seed. -/
def PCP.Complete (P : PCP) (R : Relation) : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam (u w : Bits), u.length ≤ R.inLen lam → w.length ≤ R.witLen lam →
    R.rel u w = true →
      1 - ν lam ≤ avgCoins (P.proveCoins lam u.length) fun c => P.acc lam u (P.prove lam u w c)

/-- Full-proof knowledge with knowledge error `κ`, Definition 3.24 (p.22): for every `λ`, every
instance `u` and every proof `π ∈ {0,1}^M` with `Acc(u, π) > κ(λ)`, the decoder outputs a witness,
`R(u, Decode(1^λ, u, π)) = 1`, on every outcome of its coins (probability one). -/
def PCP.KnowledgeError (P : PCP) (R : Relation) (κ : ℕ → ℝ) : Prop :=
  ∀ lam (u π : Bits), π.length = P.proofLen lam → κ lam < P.acc lam u π →
    ∀ c : Bits, c.length = P.decodeCoins lam u.length → R.rel u (P.decode lam u π c) = true

end Supplement

end FourMsgQMA


