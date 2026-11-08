-- Prove2me | Definitions.Def_DPVerify_OneRoundProtocol_IsDP
-- name    : DPVerify_OneRoundProtocol_IsDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:11.028302+00:00
-- url     : https://prove2.me/theorems/924a8462-412f-477a-85ed-b875bcdd619b
-- title:
--   $(\varepsilon,\delta)$-differentially private one-round protocol
-- statement:
--   A one-round protocol is **$(\varepsilon,\delta)$-differentially private** if for every pair of neighbouring samples $S,S'\in\mathcal X^s$, every prover strategy, and every set $E$ of transcripts,
--
--   $$
--   \Pr[\mathrm{Interact}(P,\mathsf A,S)\in E]\;\le\;e^{\varepsilon}\Pr[\mathrm{Interact}(P,\mathsf A,S')\in E]+\delta ,
--   $$
--
--   where $\mathrm{Interact}(P,\mathsf A,S)$ is the transcript (message, reply, decision bit) of the protocol run with the prover $\mathsf A$ and the honest verifier holding the sample $S$. Privacy protects every individual sample point against any prover, honest or not.
--
--   **Formalization Note** Neighbouring samples differ in one coordinate (the published `PrivLearn.Generic.Neighbors`). The prover ranges over deterministic strategies $f:\mathcal M\to\mathsf{Ans}$; a randomized prover is a mixture of these and the inequality is preserved under mixtures. The transcript space is finite, so events are finite sets of transcripts.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definitions 2.1–2.2, p.4 (PDF p.7)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_DPVerify_OneRoundProtocol

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

namespace OneRoundProtocol

variable {X : Type} [MeasurableSpace X] {s : ℕ}

/-- An `(ε, δ)`-differentially private one-round protocol (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definition 2.2, p.4 = PDF p.7): for
every pair of adjacent samples `S, S′`, every prover strategy, and every set `E` of transcripts,
`Pr[Interact(P, A, S) ∈ E] ≤ e^ε · Pr[Interact(P, A, S′) ∈ E] + δ`.

**Formalization Note**
* Adjacent samples are the published `PrivLearn.Generic.Neighbors` (one entry of `S ∈ X^s`
  substituted). Definition 2.1 says "addition or removal of one element"; the paper's protocols
  read a sample of fixed size `s`, and §6 (p.33) proves privacy for neighbours "which differ on
  the ith coordinate".
* A transcript is `(m, a, b)`: message, reply, decision bit. The adversary ranges over every
  deterministic prover strategy `f : M → Ans`; a randomized prover is a mixture of these, and the
  inequality is preserved under mixtures, so this is the same condition.
* The transcript space is finite, so an event is a `Finset` of transcripts and its probability
  is the finite sum of `transcript`. -/
def IsDP (P : OneRoundProtocol X s) (ε δ : ℝ) : Prop :=
  ∀ f : P.M → P.Ans, ∀ S S' : Fin s → X, PrivLearn.Generic.Neighbors S S' →
    ∀ E : Finset (P.M × P.Ans × Bool),
      ∑ t ∈ E, P.transcript f S t ≤ Real.exp ε * ∑ t ∈ E, P.transcript f S' t + δ

end OneRoundProtocol

end DPVerify


