-- Prove2me | Definitions.Def_PrivOptTest_Protocol
-- name    : PrivOptTest_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:07.249076+00:00
-- url     : https://prove2.me/theorems/97382c10-0d94-44f4-a1bd-d82e28b02334
-- title:
--   Two-party interactive protocols, their runs, views and transcripts; two-party differential privacy (Definition 2.1)
-- statement:
--   An **interactive two-party protocol** with inputs in $\mathcal I$ and common output in $\mathcal O$ consists of private coin spaces $\Omega_A,\Omega_B$ with laws $\mu_A,\mu_B$, a public coin space $\Omega_P$ with law $\mu_P$, a message space $\mathcal M$, next-message maps for Alice (even rounds) and Bob (odd rounds), and a public stopping rule. Round $r$'s message is a function of the speaker's own input and private coins, the public coins and the $r$ earlier messages; the stopping rule sees only the public coins and the messages, and when it fires it fixes the common output.
--
--   The run on inputs $(S_A,S_B)$ and coins $\omega$ gives the trace of messages (padded after the stop) and the output. **Alice's view** is $(\omega_A,\omega_P,\text{messages},\text{output})$, Bob's likewise, and the **public transcript** is $(\omega_P,\text{messages},\text{output})$; their laws are pushforwards of $\mu_A\otimes\mu_B\otimes\mu_P$.
--
--   A protocol is **well formed** if all its maps are measurable, the three coin laws are probability measures and it stops almost surely on every pair of inputs. On datasets $S\in\mathcal X^n$ it is **$\varepsilon$-differentially private** (Definition 2.1) if for every fixed $S_A$ Alice's view is $\varepsilon$-DP in $S_B$, and for every fixed $S_B$ Bob's view is $\varepsilon$-DP in $S_A$, on the full input domain.
--
--   **Formalization Note** A party's input enters only through its own next-message map, so the model has no trusted curator. Strict alternation loses no generality, since a party with nothing to say sends a fixed message. The structure carries no proofs: measurability, probability and termination are the conjuncts of `IsWellFormed`. Alice's own input is left out of her view, since it is fixed in every comparison.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Definition 1.2, pp.3–4; §2.2 and Definition 2.1, pp.13–14; Lemma 2.2, p.14

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

open MeasureTheory

namespace PrivOptTest

/-- The common output of a tester (Definition 1.2, arXiv:2611.03599, manuscript sha256 4ac94dcf…, p.4). -/
inductive Outcome
  | matched
  | far
  deriving DecidableEq

instance : MeasurableSpace Outcome := ⊤

/-- **An interactive two-party protocol** (Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine
Our Data?*, arXiv:2611.03599, manuscript sha256 4ac94dcf…, Definition 1.2, pp.3–4; §2.2, pp.13–14).

`In` is the type of a party's input and `Out` the type of the common output. Alice has private coins
`ΩA`, Bob `ΩB`, and both see the public coins `ΩP`. Round `r` is spoken by Alice for even `r` and by
Bob for odd `r`, as a function of the speaker's input and private coins, the public coins and the
`r` earlier messages. `stop r` decides, from public information only, whether the run ends before
round `r`: `Sum.inl o` ends it with common output `o`, `Sum.inr ()` continues.

**Formalization Note.** A party's input enters only through that party's next-message map and `stop`
sees no input, so there is no trusted curator. The structure carries no proofs: measurability,
probability and almost-sure termination are the conjuncts of `Protocol.IsWellFormed`. A party that
has nothing to say sends a fixed message, so strict alternation loses no generality. -/
structure Protocol (In Out : Type) where
  ΩA : Type
  ΩB : Type
  ΩP : Type
  Msg : Type
  [mA : MeasurableSpace ΩA]
  [mB : MeasurableSpace ΩB]
  [mP : MeasurableSpace ΩP]
  [mM : MeasurableSpace Msg]
  μA : Measure ΩA
  μB : Measure ΩB
  μP : Measure ΩP
  nextA : (r : ℕ) → In → ΩA → ΩP → (Fin r → Msg) → Msg
  nextB : (r : ℕ) → In → ΩB → ΩP → (Fin r → Msg) → Msg
  stop : (r : ℕ) → ΩP → (Fin r → Msg) → Out ⊕ Unit

attribute [instance] Protocol.mA Protocol.mB Protocol.mP Protocol.mM

namespace Protocol

variable {In Out : Type} (Pr : Protocol In Out)

/-- All the coins of a run: Alice's, Bob's and the public ones. -/
abbrev Coins : Type := Pr.ΩA × Pr.ΩB × Pr.ΩP

/-- The product law of the coins. -/
noncomputable def coinLaw : Measure Pr.Coins := Pr.μA.prod (Pr.μB.prod Pr.μP)

/-- The first `r` messages on inputs `sA`, `sB` and coins `ω`. -/
def hist (sA sB : In) (ω : Pr.Coins) : (r : ℕ) → Fin r → Pr.Msg
  | 0 => Fin.elim0
  | r + 1 => Fin.snoc (α := fun _ => Pr.Msg) (hist sA sB ω r)
      (if r % 2 = 0 then Pr.nextA r sA ω.1 ω.2.2 (hist sA sB ω r)
        else Pr.nextB r sB ω.2.1 ω.2.2 (hist sA sB ω r))

/-- The message spoken in round `r`, whether or not the run has already stopped. -/
def msg (sA sB : In) (ω : Pr.Coins) (r : ℕ) : Pr.Msg :=
  if r % 2 = 0 then Pr.nextA r sA ω.1 ω.2.2 (Pr.hist sA sB ω r)
    else Pr.nextB r sB ω.2.1 ω.2.2 (Pr.hist sA sB ω r)

/-- The run has stopped before round `r`, or exactly at it. -/
def StoppedBy (sA sB : In) (ω : Pr.Coins) (r : ℕ) : Prop :=
  ∃ r' ≤ r, ∃ o, Pr.stop r' ω.2.2 (Pr.hist sA sB ω r') = Sum.inl o

open Classical in
/-- The infinite trace of the exchanged messages: round `r`'s message while the run has not stopped,
`Sum.inr ()` afterwards. -/
noncomputable def trace (sA sB : In) (ω : Pr.Coins) (r : ℕ) : Pr.Msg ⊕ Unit :=
  if Pr.StoppedBy sA sB ω r then Sum.inr () else Sum.inl (Pr.msg sA sB ω r)

open Classical in
/-- The common output, `Sum.inr ()` if the run never stops. -/
noncomputable def output (sA sB : In) (ω : Pr.Coins) : Out ⊕ Unit :=
  if h : ∃ r, ∃ o, Pr.stop r ω.2.2 (Pr.hist sA sB ω r) = Sum.inl o then
    Pr.stop (Nat.find h) ω.2.2 (Pr.hist sA sB ω (Nat.find h))
  else Sum.inr ()

/-- Alice's view (§2.2, p.13): her private coins, the public coins, all messages, the output.
Her input is left out since it is the fixed `S_A` in every comparison of Definition 2.1. -/
noncomputable def viewA (sA sB : In) (ω : Pr.Coins) :
    Pr.ΩA × Pr.ΩP × (ℕ → Pr.Msg ⊕ Unit) × (Out ⊕ Unit) :=
  (ω.1, ω.2.2, Pr.trace sA sB ω, Pr.output sA sB ω)

/-- Bob's view (§2.2, p.13). -/
noncomputable def viewB (sA sB : In) (ω : Pr.Coins) :
    Pr.ΩB × Pr.ΩP × (ℕ → Pr.Msg ⊕ Unit) × (Out ⊕ Unit) :=
  (ω.2.1, ω.2.2, Pr.trace sA sB ω, Pr.output sA sB ω)

/-- The public transcript `T` of Lemma 2.2 (p.14): public coins, all messages, the output. -/
noncomputable def transcript (sA sB : In) (ω : Pr.Coins) :
    Pr.ΩP × (ℕ → Pr.Msg ⊕ Unit) × (Out ⊕ Unit) :=
  (ω.2.2, Pr.trace sA sB ω, Pr.output sA sB ω)

variable [MeasurableSpace Out]

/-- The law of Alice's view. -/
noncomputable def viewALaw (sA sB : In) : Measure (Pr.ΩA × Pr.ΩP × (ℕ → Pr.Msg ⊕ Unit) × (Out ⊕ Unit)) :=
  Pr.coinLaw.map (Pr.viewA sA sB)

/-- The law of Bob's view. -/
noncomputable def viewBLaw (sA sB : In) : Measure (Pr.ΩB × Pr.ΩP × (ℕ → Pr.Msg ⊕ Unit) × (Out ⊕ Unit)) :=
  Pr.coinLaw.map (Pr.viewB sA sB)

/-- The law of the public transcript. -/
noncomputable def transcriptLaw (sA sB : In) : Measure (Pr.ΩP × (ℕ → Pr.Msg ⊕ Unit) × (Out ⊕ Unit)) :=
  Pr.coinLaw.map (Pr.transcript sA sB)

/-- The law of the common output. -/
noncomputable def outputLaw (sA sB : In) : Measure (Out ⊕ Unit) :=
  Pr.coinLaw.map (Pr.output sA sB)

/-- **Well-formedness** of a protocol, the implicit conventions of Definition 1.2: every field is
measurable, the coin laws are probability measures, and the protocol is almost surely terminating on
every pair of inputs. Without these, `Measure.map` would return the zero measure and privacy would
hold vacuously. -/
structure IsWellFormed : Prop where
  measurable_nextA : ∀ (r : ℕ) (s : In), Measurable fun x : Pr.ΩA × Pr.ΩP × (Fin r → Pr.Msg) =>
    Pr.nextA r s x.1 x.2.1 x.2.2
  measurable_nextB : ∀ (r : ℕ) (s : In), Measurable fun x : Pr.ΩB × Pr.ΩP × (Fin r → Pr.Msg) =>
    Pr.nextB r s x.1 x.2.1 x.2.2
  measurable_stop : ∀ r : ℕ, Measurable fun x : Pr.ΩP × (Fin r → Pr.Msg) => Pr.stop r x.1 x.2
  prob_A : IsProbabilityMeasure Pr.μA
  prob_B : IsProbabilityMeasure Pr.μB
  prob_P : IsProbabilityMeasure Pr.μP
  terminates : ∀ sA sB : In, ∀ᵐ ω ∂Pr.coinLaw, ∃ r, ∃ o, Pr.stop r ω.2.2 (Pr.hist sA sB ω r) = Sum.inl o

/-- **Definition 2.1 (pp.13–14), two-party differential privacy on the full input domain**: for every
fixed input of one party, that party's view is ε-differentially private in the other party's dataset.

**Formalization Note.** Datasets are sequences `Fin n → D`, with the neighbouring relation
`PrivLearn.Generic.Neighbors` (one record replaced, position by position). -/
def IsPrivate {D : Type} {n : ℕ} (Pr : Protocol (Fin n → D) Out) (ε : ℝ) : Prop :=
  (∀ sA, PrivLearn.Generic.IsDP (fun sB => Pr.viewALaw sA sB) ε) ∧
  (∀ sB, PrivLearn.Generic.IsDP (fun sA => Pr.viewBLaw sA sB) ε)

end Protocol

/-- Run `Pr` on inputs encoded by `fA` for Alice and by `fB` for Bob. Each party applies its own map
to its own input, so the encoding is local. -/
def Protocol.precomp {In In' Out : Type} (Pr : Protocol In Out) (fA fB : In' → In) : Protocol In' Out where
  ΩA := Pr.ΩA
  ΩB := Pr.ΩB
  ΩP := Pr.ΩP
  Msg := Pr.Msg
  μA := Pr.μA
  μB := Pr.μB
  μP := Pr.μP
  nextA r s := Pr.nextA r (fA s)
  nextB r s := Pr.nextB r (fB s)
  stop := Pr.stop

end PrivOptTest


