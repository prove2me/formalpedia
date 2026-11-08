-- Prove2me | Definitions.Def_DPVerify_AMProtocol
-- name    : DPVerify_AMProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:27.125555+00:00
-- url     : https://prove2.me/theorems/ce6e9e78-fd4a-497a-bce4-7ea8b48316c9
-- title:
--   One-round public-coin (AM) protocol
-- statement:
--   A **one-round public-coin (Arthur–Merlin) protocol** with sample complexity $s$ is an interaction in which the verifier's only message is a string $\sigma\in\{0,1\}^{n}$ of uniformly random public bits, whose length $n$ does not depend on the sample. The prover replies $b\in\mathcal B$, and the verifier, holding its sample $S\sim D^s$, accepts with probability $\mathrm{acc}(S,\sigma,b)\in[0,1]$.
--
--   The module records the law of the transcript $(\sigma,b,d)$ (coins, reply, decision bit) against a prover strategy $g:\{0,1\}^n\to\mathcal B$; the acceptance probability on a sample, $2^{-n}\sum_\sigma\mathrm{acc}(S,\sigma,g(\sigma))$; the acceptance probability under $D$; and the communication complexity $n+\lceil\log_2|\mathcal B|\rceil$.
--
--   Since the public coins are independent of the sample, all interaction can be taken to happen before the sample is drawn; the paper's lower bound shows that, for small privacy parameters, such protocols lose nothing against private-coin ones.
--
--   **Formalization Note** The reply space is finite and fixed by the protocol; only $\mathrm{acc}$ sees the sample, measurably. The verifier's private randomness in the decision is folded into $\mathrm{acc}$.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), §2, p.4 (PDF p.7); Theorem 4.1, p.11 (PDF p.14)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- A one-round public-coin (AM) protocol with sample complexity `s` (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), §2, p.4 = PDF p.7, and
Theorem 4.1, p.11): the verifier sends `nbits` uniformly random public bits `σ`, the prover replies
`b ∈ B`, and the verifier, holding its sample `S ∼ D^s`, accepts with probability `acc S σ b`.

**Formalization Note**
* "The only messages that the verifier is allowed to send to the prover are random bits, and the
  number of bits cannot depend on the dataset" (p.4): `nbits` and the reply type `B` are fixed
  by the protocol, the public coins are uniform on `{0,1}^nbits` and independent of `S`, and only
  `acc` sees the sample.
* The verifier's private coins in the decision are folded into `acc S σ b ∈ [0, 1]`, measurable in
  the sample. Replies range over a finite type, so the communication is finite.
* The structure carries no privacy, completeness or soundness property. -/
structure AMProtocol (X : Type) [MeasurableSpace X] (s : ℕ) where
  /-- number of public random bits -/
  nbits : ℕ
  /-- reply space -/
  B : Type
  [fintypeB : Fintype B]
  [decEqB : DecidableEq B]
  /-- the acceptance probability on sample `S`, public coins `σ` and reply `b` -/
  acc : (Fin s → X) → (Fin nbits → Bool) → B → ℝ
  acc_nonneg : ∀ S σ b, 0 ≤ acc S σ b
  acc_le_one : ∀ S σ b, acc S σ b ≤ 1
  measurable_acc : ∀ σ b, Measurable fun S => acc S σ b

attribute [instance] AMProtocol.fintypeB AMProtocol.decEqB

namespace AMProtocol

variable {X : Type} [MeasurableSpace X] {s : ℕ}

/-- The law of the transcript `(σ, b, d)` (public coins, reply, decision bit) on the sample `S`
against the prover strategy `g : {0,1}^nbits → B`, as a probability mass function. -/
noncomputable def transcript (Q : AMProtocol X s) (g : (Fin Q.nbits → Bool) → Q.B)
    (S : Fin s → X) : (Fin Q.nbits → Bool) × Q.B × Bool → ℝ :=
  fun t => ((2 : ℝ) ^ Q.nbits)⁻¹ *
    (if g t.1 = t.2.1 then (if t.2.2 then Q.acc S t.1 t.2.1 else 1 - Q.acc S t.1 t.2.1) else 0)

/-- The acceptance probability on the sample `S` against the prover strategy `g`. -/
noncomputable def accProb (Q : AMProtocol X s) (g : (Fin Q.nbits → Bool) → Q.B)
    (S : Fin s → X) : ℝ :=
  ((2 : ℝ) ^ Q.nbits)⁻¹ * ∑ σ, Q.acc S σ (g σ)

/-- The acceptance probability under the population distribution `D` (`S ∼ D^s`). -/
noncomputable def accept (Q : AMProtocol X s) (g : (Fin Q.nbits → Bool) → Q.B)
    (D : ProbabilityMeasure X) : ℝ :=
  ∫ S, Q.accProb g S ∂(Measure.pi fun _ : Fin s => (D : Measure X))

/-- Communication complexity: the public bits plus the bit length of the reply,
`nbits + ⌈log₂ |B|⌉`. -/
def comm (Q : AMProtocol X s) : ℕ :=
  Q.nbits + Nat.clog 2 (Fintype.card Q.B)

end AMProtocol

end DPVerify


