-- Prove2me | Definitions.Def_GrossmanInevitable_Intersection_LasVegas
-- name    : GrossmanInevitable_Intersection_LasVegas
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:04:32.636005+00:00
-- url     : https://prove2.me/theorems/214ea254-10c9-4959-873f-b409592606f8
-- title:
--   Las Vegas protocols with shared advice: private coins, almost-sure termination, expected communication
-- statement:
--   A **zero-error protocol using private randomness** (a **Las Vegas protocol**) with shared advice $\sigma\in\{0,1\}^*$ is defined as follows. Each player has a private random string. Alice's string $\omega_A$ and Bob's string $\omega_B$ are independent infinite sequences of fair coin flips (`coins`, the product of uniform measures on $\{0,1\}^{\mathbb N}$). The protocol consists of:
--
--   - a rule `next σ h` that depends only on the advice $\sigma$ and the bits $h$ exchanged so far. It says either that the protocol stops with output $o$, or that Alice sends the next bit, or that Bob does. So the output is a function of the advice and the transcript, and both players know it;
--   - Alice's bit `aliceBit σ h a ωA`, a function of the advice, the bits so far, her input and her own random string. Bob's bit `bobBit σ h b ωB` is defined symmetrically. Each bit is a measurable function of the sender's random string. There are no public coins.
--
--   A run may be infinite. `hist σ a b ωA ωB k` is the sequence of bits sent in the first $k$ steps; it stops growing once the protocol has stopped. The **number of bits sent**, `bitsSent`, is the first step at which the protocol stops, and $\infty$ if it never stops. The **expected communication** on $(a,b)$ with advice $\sigma$ is
--   $$\mathrm{expCost}(\sigma,a,b)=\mathbb E_{\omega_A,\omega_B}\big[\mathrm{bitsSent}(\sigma,a,b,\omega_A,\omega_B)\big]\in[0,\infty].$$
--
--   For a relation $R$, the protocol has **zero error** on $(a,b)$ with advice $\sigma$ (`ZeroErrorOn`) if, with probability $1$ over $(\omega_A,\omega_B)$, it stops and its output $o\in W\cup\{\bot\}$ is correct. Correct means a witness of $(a,b)$ if one exists, and $\bot$ otherwise.
--
--   Formalization note: the source says only "private randomness". Each player's randomness is modelled as an infinite sequence of fair coins, independent of the other player's. Runs are unbounded and terminate only almost surely, so the protocol is not a finite tree. A non-terminating run counts $\infty$ bits.
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), §2.1 'Las Vegas protocols', p. 14 (PDF 16); Definition 1.2, p. 3 (PDF 5)

import Mathlib
import Definitions.Def_GrossmanInevitable_Intersection_Relation

namespace GrossmanInevitable.Intersection

open MeasureTheory

/-- A player's **private random string**: an infinite sequence of independent fair coin flips,
`ω : ℕ → Bool` distributed as the product of uniform measures on `Bool`. -/
noncomputable def coins : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- What happens next in a protocol after a given transcript prefix: the protocol stops with an
output `o`, or Alice sends the next bit, or Bob does. -/
inductive Turn (O : Type) : Type
  | output (o : O) : Turn O
  | alice : Turn O
  | bob : Turn O

/-- A **Las Vegas protocol with shared advice** (zero-error protocol using private randomness;
§2.1, printed p. 14 / PDF 16, and Definition 1.2, printed p. 3 / PDF 5), before its zero-error
requirement, which `ZeroErrorOn` states.

* The advice `σ : List Bool` is known to both players.
* `next σ h` says, from the advice and the bits `h` exchanged so far, whether the protocol stops
  and with which output, or who sends the next bit. It depends on nothing else, so the output is
  determined by the advice and the transcript and is known to both players.
* When Alice speaks, her bit `aliceBit σ h a ωA` is a function of the advice, the bits so far, her
  input `a` and her own private random string `ωA`; likewise Bob's bit uses only `σ`, `h`, `b`
  and `ωB`. There are no public coins; the two random strings are independent (`coins.prod coins`).
* Each bit is a measurable function of the sender's random string.

Runs are not bounded: the protocol may run forever on some random strings. -/
structure LVProtocol (A B O : Type) where
  next : List Bool → List Bool → Turn O
  aliceBit : List Bool → List Bool → A → (ℕ → Bool) → Bool
  bobBit : List Bool → List Bool → B → (ℕ → Bool) → Bool
  aliceBit_measurable : ∀ σ h a, Measurable (aliceBit σ h a)
  bobBit_measurable : ∀ σ h b, Measurable (bobBit σ h b)

namespace LVProtocol

variable {A B O : Type}

/-- The bits exchanged during the first `k` steps of the run with advice `σ`, inputs `a`, `b` and
private random strings `ωA`, `ωB`. Once the protocol has stopped, the transcript no longer
changes. -/
def hist (P : LVProtocol A B O) (σ : List Bool) (a : A) (b : B) (ωA ωB : ℕ → Bool) :
    ℕ → List Bool
  | 0 => []
  | k + 1 =>
    match P.next σ (hist P σ a b ωA ωB k) with
    | .output _ => hist P σ a b ωA ωB k
    | .alice => hist P σ a b ωA ωB k ++ [P.aliceBit σ (hist P σ a b ωA ωB k) a ωA]
    | .bob => hist P σ a b ωA ωB k ++ [P.bobBit σ (hist P σ a b ωA ωB k) b ωB]

/-- The **number of bits communicated** in the run: the first step `k` at which the protocol
stops (each earlier step sends exactly one bit), and `∞` if it never stops. -/
noncomputable def bitsSent (P : LVProtocol A B O) (σ : List Bool) (a : A) (b : B)
    (ωA ωB : ℕ → Bool) : ENNReal :=
  ⨅ (k : ℕ) (_ : ∃ o, P.next σ (P.hist σ a b ωA ωB k) = .output o), (k : ENNReal)

/-- The **expected communication** `E|π(a, b, σ)|` of the protocol on inputs `(a, b)` with advice
`σ`, over the two independent private random strings; `∞` if the protocol fails to stop with
positive probability. -/
noncomputable def expCost (P : LVProtocol A B O) (σ : List Bool) (a : A) (b : B) : ENNReal :=
  ∫⁻ ω, P.bitsSent σ a b ω.1 ω.2 ∂(coins.prod coins)

/-- **Zero error** on the input `(a, b)` with advice `σ` for the search problem of `R`: with
probability 1 the protocol stops, and its output `o ∈ W ∪ {⊥}` is correct (`CorrectOut`): a
witness of `(a, b)` if one exists and `⊥` otherwise. -/
def ZeroErrorOn {W : Type} (P : LVProtocol A B (Option W)) (R : A → B → W → Prop)
    (σ : List Bool) (a : A) (b : B) : Prop :=
  ∀ᵐ ω ∂(coins.prod coins), ∃ k : ℕ, ∃ o : Option W,
    P.next σ (P.hist σ a b ω.1 ω.2 k) = .output o ∧ CorrectOut R a b o

end LVProtocol

end GrossmanInevitable.Intersection


