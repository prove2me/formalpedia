-- Prove2me | Definitions.Def_NCPComm_Supplement_IsTolerantIdentityVerifier
-- name    : NCPComm_Supplement_IsTolerantIdentityVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:17:51.631345+00:00
-- url     : https://prove2.me/theorems/7f20d743-c3a8-4eac-b4c3-2ccf427841c4
-- title:
--   Tolerant identity verification ($\delta_c=1/16$, $\delta_f=5/64$) with a fixed-sample verifier, and the collision probability $\|D\|_2^2$
-- statement:
--   Fix a domain $[N]$ and write $\|D\|_2^2=\sum_{x}D(x)^2$ for the **collision probability** of a distribution $D$ on $[N]$.
--
--   In **tolerant identity verification** with completeness threshold $\delta_c=1/16$ and soundness threshold $\delta_f=5/64$, the verifier receives an explicit reference distribution $Q$ over $[N]$, draws $m$ independent samples from an unknown distribution $D$ over $[N]$, and interacts with an untrusted prover. A family $Q\mapsto\Pi_Q$ of interactive protocols (each with its own number of communicated bits, speaker function and randomized verifier) is a **correct tolerant identity verifier on the pairs $Q\in\mathcal R$, $D\in\mathcal B$** (a set $\mathcal R$ of reference distributions and a set $\mathcal B$ of unknown distributions) if, for every such pair:
--
--   1. (completeness) if $\delta_{\mathrm{TV}}(D,Q)\le 1/16$, some prover strategy makes the verifier accept with probability at least $2/3$;
--   2. (soundness) if $\delta_{\mathrm{TV}}(D,Q)\ge 5/64$, every cheating prover makes the verifier accept with probability at most $1/3$.
--
--   Here $\delta_{\mathrm{TV}}(D,Q)=\frac12\sum_x|D(x)-Q(x)|$, and the acceptance probability is over the $m$ i.i.d. samples, the verifier's secret coins and the prover's coins.
--
--   This is the model of Theorem 1.3, in the proof-system sense of Definition 3.4; the sets $\mathcal R,\mathcal B$ fix the collision-probability scale at which the worst-case communication is measured (footnote 4, p.5).
--
--   **Formalization Note** The protocol type and the transcript semantics are the published `NCPComm.IPProtocol` and `NCPComm.runTranscript`; the sample is the published law `OAI.ThreeState.iidList` of $m$ i.i.d. draws instead of the Poissonized sample, and $\delta_{\mathrm{TV}}$ is the published `OAI.ThreeState.tvMass`. The prover's strategy is a distribution over deterministic behaviours chosen after $(D,Q)$; it sees the verifier's sample and coins only through the transcript. No efficiency bound is placed on the verifier.
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Theorem 1.3 and the paragraph before it, p.5 (footnote 4); Definition 3.4, p.14; proof of Theorem 1.3, p.32; ‖D‖₂², p.3

import Mathlib
import Definitions.Def_NCPComm_IPProtocol
import Definitions.Def_OAI_Probability_ThreeState_Basic

open scoped NNReal ENNReal

namespace NCPComm.Supplement

/-- The collision probability `‖D‖₂² = ∑ₓ D(x)²` of a distribution on `[N]` (p.3 of Herman, The
Communication Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript
sha256 714c0353…; used in Theorem 1.3, p.5). -/
noncomputable def collisionProb {N : ℕ} (D : PMF (Fin N)) : ℝ :=
  ∑ x, (D x).toReal ^ 2

/-- The collision-probability band `{D : a·N^{−k} ≤ ‖D‖₂² ≤ b·N^{−k}}` on `[N]`: the distributions whose
collision probability is of order `N^{−k}` with the constants `a ≤ b` (Theorem 1.3, p.5, and its
proof, p.32). -/
def collisionBand (a b k : ℝ) (N : ℕ) : Set (PMF (Fin N)) :=
  {D | a * (N : ℝ) ^ (-k) ≤ collisionProb D ∧ collisionProb D ≤ b * (N : ℝ) ^ (-k)}

/-- The probability that the verifier of `P` accepts when it draws exactly `m` independent samples
from `D` before the interaction (the fixed-sample verifier of Definition 3.4, p.14), against a prover
whose behaviour is drawn from `prover`, independently of the sample and of the verifier's coins.
This is `NCPComm.acceptProb` with the i.i.d. list `OAI.ThreeState.iidList D m` in place of the
Poissonized sample.

**Formalization Note** A verifier that uses at most `m` samples is one of these: it ignores the
extra draws. -/
noncomputable def acceptProbFixed {N : ℕ} (P : NCPComm.IPProtocol N) (m : ℕ) (D : PMF (Fin N))
    (prover : PMF NCPComm.ProverBehaviour) : ℝ≥0∞ :=
  ((OAI.ThreeState.iidList D m).bind fun l => (P.verifier l).bind fun v =>
    prover.map fun p => v.2 (NCPComm.runTranscript P.speaker v.1 p P.depth)) true

/-- **Tolerant identity verification with `δ_c = 1/16`, `δ_f = 5/64`** (Theorem 1.3, p.5, with the
proof-system notion of Definition 3.4, p.14; Herman, STOC 2027 submission, manuscript sha256
714c0353…). `P Q` is the interactive protocol run when the explicit reference distribution is `Q`;
its verifier draws `m` samples from the unknown `D`. The family is a correct tolerant identity
verifier on the pairs `Q ∈ Refs` (reference distributions) and `D ∈ Band` (unknown distributions) if for
every such pair:
* (completeness) if `δ_TV(D, Q) ≤ 1/16`, some prover strategy makes the verifier accept with
  probability at least `2/3`;
* (soundness) if `δ_TV(D, Q) ≥ 5/64`, every cheating prover behaviour makes the verifier accept with
  probability at most `1/3`.

**Formalization Note** `δ_TV` is the published `OAI.ThreeState.tvMass D Q = ½ ∑ₓ |D(x) − Q(x)|`,
the total variation distance on the finite domain. The protocol (verifier, speaker function and
communication `depth`) may depend on `Q`, which both parties hold explicitly. The prover strategy is
a `PMF` over deterministic behaviours chosen after `(D, Q)`, so it knows both; it never sees the
verifier's sample or coins except through the transcript. Deterministic cheating behaviours suffice
for soundness because acceptance is linear in a mixture. No efficiency bound is placed on the
verifier. Restricting correctness to the pairs `(D, Q)` with `Q ∈ Refs`, `D ∈ Band` encodes footnote 4,
p.5: the lower bound is a worst-case bound over the input pairs at the stated collision-probability
scale. With `Refs = Set.univ` this is correctness for an arbitrary explicit reference `Q`. -/
def IsTolerantIdentityVerifier {N : ℕ} (P : PMF (Fin N) → NCPComm.IPProtocol N) (m : ℕ)
    (Refs Band : Set (PMF (Fin N))) : Prop :=
  ∀ Q ∈ Refs, ∀ D ∈ Band,
    (OAI.ThreeState.tvMass D Q ≤ 1 / 16 →
      ∃ prover : PMF NCPComm.ProverBehaviour, 2 / 3 ≤ (acceptProbFixed (P Q) m D prover).toReal) ∧
    (5 / 64 ≤ OAI.ThreeState.tvMass D Q →
      ∀ p : NCPComm.ProverBehaviour, (acceptProbFixed (P Q) m D (PMF.pure p)).toReal ≤ 1 / 3)

end NCPComm.Supplement


