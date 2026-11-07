-- Prove2me | Definitions.Def_KramerSaglam_PairSetup
-- name    : KramerSaglam_PairSetup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:05:05.434827+00:00
-- url     : https://prove2.me/theorems/23c3d2d6-ca49-491a-992a-42f9f8d486be
-- title:
--   The comparison setup of §3.1, the Markov chain $A-B-C'$ and the matching condition (B)
-- statement:
--   **Pair setup (§3.1).** Bits $A,B,C$ and a sub-σ-algebra $U$ form a **pair setup with channel $p$** when $A,B,C$ are measurable, $P(A)=P(B)=\tfrac12$, $P(A\,\triangle\,B)=p$, the pair $(A,B)$ is independent of $U$, and $C$ is obtained from $(B,U)$ using private randomness, that is,
--   $$
--   P[C\mid A,B,U]=P[C\mid B,U]\quad\text{a.s.}
--   $$
--   The coordinate instance of p.4 is $A=X_i$, $B=Y_i$, $U=X_{-i}$, and then $X$ is $(A,U)$.
--
--   **Chain.** Bits $A,B,C$ form a **chain with channel $p$** when $A,B$ are unbiased, $P(A\,\triangle\,B)=p$, and $A-B-C$ is a Markov chain: $P[C\mid A,B]=P[C\mid B]$ a.s. The mean of $C$ is free.
--
--   **Matching condition (B).** For a pair setup $(A,B,U,C)$ and bits $B',C'$ on a possibly different probability space,
--   $$
--   I(B':C')=\frac{I(B:C\mid U)}{\bar H(C\mid U)} .
--   $$
--
--   These are the objects of the comparison lemmas 3.4–3.8 and of the three-bit lemma 3.9: the bit $C$, which depends on $B$ and on $U$, is compared with an unbiased bit $C'$ obtained from $B$ alone.
--
--   **Formalization Note** The paper's standing assumption $\bar H(C\mid U)>0$ (p.4) is not a field of the setup, because Lemma 3.3 does not assume it; the lemmas that need it state it. The comparison bit $C'$ is placed with a copy $(A',B')$ of $(A,B)$ (same channel $p$) on any probability space, since only the joint law of $(A,B,C')$ matters.
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), §3.1 p.4 (setup and (B)), §3.3 p.7 and App. A p.13 (the chain A − B − C)

import Mathlib
import Definitions.Def_KramerSaglam_Conditional

open MeasureTheory

namespace KramerSaglam

/-- The setup of §3.1 (D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.4): `A`, `B` are unbiased bits with `P(A ≠ B) = p`, jointly
independent of the variable `U`, and `C` is a bit obtained from `(B, U)` using private randomness.

**Formalization Note.** "Obtained from `(B, U)`" is the conditional independence of `C` and `A` given
`(B, U)`. The coordinate instance of p.4 is `A = X_i`, `B = Y_i`, `U = X_{−i}`, and there `X` is
`sigma A ⊔ U`. The paper's standing `H̄(C | U) > 0` is not a field, because Lemma 3.3 does not assume it;
the lemmas that need it take it as a hypothesis. -/
structure IsPairSetup {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) (p : ℝ) (A B : Set Ω)
    (U : MeasurableSpace Ω) (C : Set Ω) : Prop where
  measurableSet_A : MeasurableSet[m₀] A
  measurableSet_B : MeasurableSet[m₀] B
  measurableSet_C : MeasurableSet[m₀] C
  U_le : U ≤ m₀
  unbiased_A : P.real A = 1 / 2
  unbiased_B : P.real B = 1 / 2
  channel : P.real (symmDiff A B) = p
  indep : ProbabilityTheory.Indep (sigma A ⊔ sigma B) U P
  obtained : condMean P C (sigma A ⊔ sigma B ⊔ U) =ᵐ[P] condMean P C (sigma B ⊔ U)

/-- A binary Markov chain `A − B − C` (pp.4, 7, 13): `A`, `B` are unbiased bits with `P(A ≠ B) = p`, and
`C` is obtained from `B` alone using private randomness.

**Formalization Note.** The mean of `C` is free here, since Lemma A.2 allows a biased `C`; the comparison
bit `C′` of §3 adds `P(C) = 1/2`. It may live on another probability space than the setup it is compared
with, because only the law of the chain matters. -/
structure IsChain {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) (p : ℝ) (A B C : Set Ω) : Prop where
  measurableSet_A : MeasurableSet A
  measurableSet_B : MeasurableSet B
  measurableSet_C : MeasurableSet C
  unbiased_A : P.real A = 1 / 2
  unbiased_B : P.real B = 1 / 2
  channel : P.real (symmDiff A B) = p
  markov : condMean P C (sigma A ⊔ sigma B) =ᵐ[P] condMean P C (sigma B)

/-- The matching condition (B), p.4: `I(B′ : C′) = I(B : C | U) / H̄(C | U)`. -/
def MatchingB {Ω Ω' : Type*} {m₀ : MeasurableSpace Ω} {m₀' : MeasurableSpace Ω'} (P : Measure Ω) (B : Set Ω)
    (U : MeasurableSpace Ω) (C : Set Ω) (P' : Measure Ω') (B' C' : Set Ω') : Prop :=
  info P' B' (sigma C') ⊥ = info P B (sigma C) U / tsGiven P C U

end KramerSaglam


