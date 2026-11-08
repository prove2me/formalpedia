-- Prove2me | Definitions.Def_DPVerify_OneRoundProtocol
-- name    : DPVerify_OneRoundProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:26.58479+00:00
-- url     : https://prove2.me/theorems/26a92176-67f4-43ee-a74b-bb67a22c024d
-- title:
--   One-round private-coin interactive proof for a distribution property
-- statement:
--   A **one-round private-coin protocol** with sample complexity $s$ is an interaction between a verifier, who has sample access to an unknown distribution $D$ on $\mathcal X$, and a prover:
--
--   1. the verifier draws a sample $S\sim D^s$ and a private seed $r\sim\mathcal R$, and sends the message $m=\mathcal A(S,r)\in\mathcal M$;
--   2. the prover replies $a\in\mathsf{Ans}$;
--   3. the verifier draws fresh randomness $r'$ and accepts if $\mathcal A'((m,a),S,r,r')=1$.
--
--   The module records the derived quantities used by the paper: the law of the transcript $(m,a,b)$ (message, reply, decision bit) against a prover strategy $f:\mathcal M\to\mathsf{Ans}$; the acceptance probability on a sample, $\mathbb E_{r\sim\mathcal R}\Pr_{r'}[\text{accept}]$; the acceptance probability under $D$, averaged over $S\sim D^s$; the communication complexity $\lceil\log_2|\mathcal M|\rceil+\lceil\log_2|\mathsf{Ans}|\rceil$; and the law $p_S$ of the message on the sample $S$.
--
--   **Formalization Note** The seeds live on any probability space $(\mathcal R,\text{law})$; a finitely supported seed law (p.11) is the case of a finite type with its discrete σ-algebra. The message space $\mathcal M$ and the reply space are finite. The fresh randomness $r'$ is folded into the acceptance probability $\Pr_{r'}[\mathcal A'((m,a),S,r,r')=1]\in[0,1]$, which is all the paper uses of it. The message and the acceptance probability are jointly measurable functions of the sample and the seed. The structure carries no privacy, completeness or soundness property; those are separate hypotheses.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Theorem 4.1, steps 1–3, p.10 (PDF p.13); p.11 (PDF p.14)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- A one-round private-coin interactive proof with sample complexity `s` (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Theorem 4.1,
steps 1–3, p.10 = PDF p.13):
1. the verifier draws a sample `S ∼ D^s` and a private seed `r ∼ R` and sends `m = msg S r`;
2. the prover replies `a ∈ Ans`;
3. the verifier accepts with probability `acc S r a` (over its fresh randomness `r′`).

**Formalization Note**
* The seeds `r ∼ R` live on any probability space `(R, seedLaw)`. A finitely supported seed law
  (p.11: "|R| is the support size of the random seeds") is the case of a finite type with its
  discrete σ-algebra. Messages `M` and replies `Ans` range over finite types (the communication
  complexity is the bit length of `(m, a)`); `M` carries its discrete σ-algebra.
* The verifier's fresh coins `r′` are folded into the acceptance probability
  `acc S r a = Pr_{r′}[A′((m, a), S, r, r′) = 1] ∈ [0, 1]`, where `m = msg S r` is determined by
  `S` and `r`; every probability in the paper depends on `r′` only through it.
* `msg` and `acc` are jointly measurable in the sample and the seed, so that probabilities over
  `S ∼ D^s` and `r ∼ R` are defined.
* The structure carries no privacy, completeness or soundness property; those are the separate
  predicates `IsDP` and the hypotheses on `accept`. -/
structure OneRoundProtocol (X : Type) [MeasurableSpace X] (s : ℕ) where
  /-- seed space -/
  R : Type
  [measR : MeasurableSpace R]
  /-- law of the private seed `r` -/
  seedLaw : Measure R
  [isProbSeedLaw : IsProbabilityMeasure seedLaw]
  /-- message space -/
  M : Type
  [fintypeM : Fintype M]
  [decEqM : DecidableEq M]
  [measM : MeasurableSpace M]
  [discM : DiscreteMeasurableSpace M]
  /-- reply space -/
  Ans : Type
  [fintypeAns : Fintype Ans]
  [decEqAns : DecidableEq Ans]
  /-- the verifier's message `m = A(S, r)` -/
  msg : (Fin s → X) → R → M
  measurable_msg : Measurable (Function.uncurry msg)
  /-- the probability, over the fresh coins `r′`, that the verifier accepts the reply `a` -/
  acc : (Fin s → X) → R → Ans → ℝ
  acc_nonneg : ∀ S r a, 0 ≤ acc S r a
  acc_le_one : ∀ S r a, acc S r a ≤ 1
  measurable_acc : ∀ a, Measurable fun q : (Fin s → X) × R => acc q.1 q.2 a

attribute [instance] OneRoundProtocol.measR OneRoundProtocol.isProbSeedLaw
  OneRoundProtocol.fintypeM OneRoundProtocol.decEqM OneRoundProtocol.measM OneRoundProtocol.discM
  OneRoundProtocol.fintypeAns OneRoundProtocol.decEqAns

namespace OneRoundProtocol

variable {X : Type} [MeasurableSpace X] {s : ℕ}

/-- The law of the transcript `(m, a, b)` (message, reply, decision bit) on the sample `S` against
the deterministic prover strategy `f : M → Ans`, as a probability mass function on the finite
transcript space: the expectation over `r ∼ R` of the conditional mass given `r`. -/
noncomputable def transcript (P : OneRoundProtocol X s) (f : P.M → P.Ans) (S : Fin s → X) :
    P.M × P.Ans × Bool → ℝ :=
  fun t => ∫ r, (if P.msg S r = t.1 ∧ f t.1 = t.2.1 then
      (if t.2.2 then P.acc S r t.2.1 else 1 - P.acc S r t.2.1) else 0) ∂P.seedLaw

/-- The acceptance probability on the sample `S` against the prover strategy `f`:
`Pr_{r, r′}[A′((A(S, r), f(A(S, r))), S, r, r′) = 1]`. -/
noncomputable def accProb (P : OneRoundProtocol X s) (f : P.M → P.Ans) (S : Fin s → X) : ℝ :=
  ∫ r, P.acc S r (f (P.msg S r)) ∂P.seedLaw

/-- The acceptance probability under the population distribution `D`: `S ∼ D^s`, `r ∼ R`, `r′`. -/
noncomputable def accept (P : OneRoundProtocol X s) (f : P.M → P.Ans) (D : ProbabilityMeasure X) :
    ℝ :=
  ∫ S, P.accProb f S ∂(Measure.pi fun _ : Fin s => (D : Measure X))

/-- Communication complexity: the bit length of the message plus that of the reply,
`⌈log₂ |M|⌉ + ⌈log₂ |Ans|⌉`. -/
def comm (P : OneRoundProtocol X s) : ℕ :=
  Nat.clog 2 (Fintype.card P.M) + Nat.clog 2 (Fintype.card P.Ans)

/-- The law `p_S` of the verifier's message `m = A(S, r)`, `r ∼ R`, on the sample `S` (p.11). -/
noncomputable def msgLaw (P : OneRoundProtocol X s) (S : Fin s → X) : Measure P.M :=
  P.seedLaw.map (P.msg S)

end OneRoundProtocol

end DPVerify


