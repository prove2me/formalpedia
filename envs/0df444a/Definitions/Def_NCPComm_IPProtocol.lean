-- Prove2me | Definitions.Def_NCPComm_IPProtocol
-- name    : NCPComm_IPProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:01:43.203368+00:00
-- url     : https://prove2.me/theorems/5a2d95ae-4c14-4ccf-8052-5862d7b38441
-- title:
--   Interactive proofs for a promise problem on distributions, with a Poissonized verifier
-- statement:
--   An **interactive proof** over the domain $[N]$ with a Poissonized verifier consists of a number $c$ of communicated bits, a speaker function saying from the transcript so far whether the verifier or the prover sends the next bit, and a randomized verifier behaviour given its sample. A deterministic verifier behaviour is a next-bit function together with a verdict function of the transcript; a deterministic prover behaviour is a next-bit function of the transcript. The prover sees nothing of the verifier's sample or coins except through the transcript.
--
--   The acceptance probability $\Pr[V\text{ accepts}]$ is over the Poissonized sample of mean $s$ from $D$, the verifier's behaviour and an independent prover behaviour. The protocol is a **proof system with error $\varepsilon$** for a promise problem $(\mathrm{Yes},\mathrm{No})$ if
--
--   1. for every $D\in\mathrm{Yes}$ there is a prover strategy with acceptance probability at least $1-\varepsilon$, and
--   2. for every $D\in\mathrm{No}$ and every cheating prover strategy, the acceptance probability is at most $\varepsilon$.
--
--   The definition also fixes the round complexity (the worst-case number of same-speaker blocks) and the joint law of transcript and verdict when the prover's retained information and the verifier's data are drawn from a joint law.
--
--   **Formalization Note** No efficiency bound is placed on the verifier, the verifier's coins stay secret, the speaker may depend on the transcript, and rounds are not limited. The verifier holds its whole sample before the interaction, which loses nothing since a Poissonized verifier "may use at most $s'$ samples" (Claim 3.8, p.15). A prover strategy is chosen after $D$. For completeness this is easier than sample access. For soundness on a finite family it is equivalent, since a sample-access prover can identify $D$ with error tending to $0$. Deterministic cheating provers suffice because acceptance is linear in mixtures. Worst-case communication at most $c$ becomes exactly $c$ after padding.
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Definition 3.4, p.14; §2.1.2, p.8; p.3 (communication); "Poissonized protocols", p.21

import Mathlib
import Definitions.Def_NCPComm_family
import Definitions.Def_NCPComm_poissonSample

open scoped NNReal ENNReal

namespace NCPComm

/-- A transcript: the bits exchanged so far, in order. -/
abbrev Transcript := List Bool

/-- A deterministic prover behaviour: the next bit as a function of the transcript. The prover
sees nothing of the verifier's sample or coins except through the transcript. -/
abbrev ProverBehaviour := Transcript → Bool

/-- A deterministic verifier behaviour: the next bit and the final verdict (`true` = accept), each
a function of the transcript. -/
abbrev VerifierBehaviour := (Transcript → Bool) × (Transcript → Bool)

/-- An interactive proof over the domain `[N]` with a Poissonized verifier (Definition 3.4, p.14,
and "Poissonized protocols", p.21, of Herman, The Communication Complexity of Verifying
Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…).
* `depth` is the communication, the worst-case total number of bits exchanged;
* `speaker τ` says whether the verifier (`true`) or the prover (`false`) sends the next bit after
  transcript `τ`;
* `verifier l` is the verifier's randomized behaviour given its sample list `l`.

**Formalization Note** The verifier holds its whole sample before the interaction, which loses
nothing: Claim 3.8, p.15, says a Poissonized verifier "may use at most `s′` samples". A randomized
verifier is a `PMF` over deterministic behaviours chosen from the sample (secret coins stay
secret). No efficiency bound is placed on the verifier, so a lower bound over this class covers the
probabilistic polynomial-time verifiers of Definition 3.4. The speaker may depend on the
transcript, and no bound on rounds is imposed. A protocol with worst-case communication at most `c`
bits is one of these after padding. -/
structure IPProtocol (N : ℕ) where
  depth : ℕ
  speaker : Transcript → Bool
  verifier : List (Fin N) → PMF VerifierBehaviour

/-- The transcript after `k` bits when the verifier's next-bit function is `vNext` and the prover's
behaviour is `pNext`. -/
def runTranscript (speaker vNext pNext : Transcript → Bool) : ℕ → Transcript
  | 0 => []
  | k + 1 =>
      let τ := runTranscript speaker vNext pNext k
      τ ++ [if speaker τ then vNext τ else pNext τ]

/-- The number of messages along a transcript: the maximal blocks of consecutive bits with the same
speaker. -/
def speakerBlocks (speaker : Transcript → Bool) (τ : Transcript) : ℕ :=
  (((List.range τ.length).map fun j => speaker (τ.take j)).destutter (· ≠ ·)).length

/-- The round complexity of Definition 3.4, p.14 ("how many messages were exchanged"), worst case
over all transcripts of length `depth`. -/
def IPProtocol.rounds {N : ℕ} (P : IPProtocol N) : ℕ :=
  Finset.univ.sup fun τ : Fin P.depth → Bool => speakerBlocks P.speaker (List.ofFn τ)

/-- The probability that the verifier of `P` accepts on a Poissonized sample of mean `s` from `D`,
against a prover whose behaviour is drawn from `prover`, independently of the sample and of the
verifier's coins. -/
noncomputable def acceptProb {N : ℕ} (P : IPProtocol N) (s : ℝ≥0) (D : PMF (Fin N))
    (prover : PMF ProverBehaviour) : ℝ≥0∞ :=
  ((poissonSample D s).bind fun l => (P.verifier l).bind fun v =>
    prover.map fun p => v.2 (runTranscript P.speaker v.1 p P.depth)) true

/-- `P` is a proof system with Poisson mean `s` and both errors at most `ε` for the promise problem
`(Yes, No)` (Definition 3.4, p.14, in the promise form of §2.1.2, p.8). Completeness: for every
`D ∈ Yes` there is a prover strategy making the verifier accept with probability at least `1 - ε`.
Soundness: for every `D ∈ No` and every cheating strategy, the verifier accepts with probability at
most `ε`.

**Formalization Note** The prover strategy is chosen after `D`, so it knows `D`. For completeness
this is easier than sample access, and it covers more protocols. For soundness on a finite family
it is equivalent, since a sample-access prover can identify `D` with error tending to `0` by drawing
more samples. Deterministic cheating strategies suffice because acceptance is linear in a mixture.
The probabilities are compared through `toReal`; they are at most `1`. -/
def IsProofFor {N : ℕ} (P : IPProtocol N) (s : ℝ≥0) (Yes No : Set (PMF (Fin N))) (ε : ℝ) : Prop :=
  (∀ D ∈ Yes, ∃ prover : PMF ProverBehaviour, 1 - ε ≤ (acceptProb P s D prover).toReal) ∧
  (∀ D ∈ No, ∀ p : ProverBehaviour, (acceptProb P s D (PMF.pure p)).toReal ≤ ε)

/-- `P` is an interactive proof for `NCP(N, K)` with Poisson mean `s` and both errors at most `ε`:
completeness over `F₀(N, K)` and soundness over `F₁(N, K)` (Definition 4.2, p.19). -/
def IsNCPProof {N : ℕ} (P : IPProtocol N) (K : ℕ) (s : ℝ≥0) (ε : ℝ) : Prop :=
  IsProofFor P s (family false N K) (family true N K) ε

/-- The joint law of the final transcript and the verdict, when the prover's retained information
and the verifier's data are drawn jointly from `J` and each side then follows its own strategy,
which reads only its own part of `J`, the transcript, and fresh independent coins (Claim 3.9,
p.16). -/
noncomputable def interactionLaw {I V : Type} (depth : ℕ) (speaker : Transcript → Bool)
    (proverStrategy : I → PMF ProverBehaviour) (verifierStrategy : V → PMF VerifierBehaviour)
    (J : PMF (I × V)) : PMF (Transcript × Bool) :=
  J.bind fun iv => (verifierStrategy iv.2).bind fun v => (proverStrategy iv.1).map fun p =>
    let τ := runTranscript speaker v.1 p depth
    (τ, v.2 τ)

end NCPComm


