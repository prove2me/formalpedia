-- Prove2me | Definitions.Def_DPVerify_AMProtocol_IsDP
-- name    : DPVerify_AMProtocol_IsDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:12.370047+00:00
-- url     : https://prove2.me/theorems/41662937-8b4d-4a79-a7e0-1f2b4b47e983
-- title:
--   $(\varepsilon,\delta)$-differentially private public-coin protocol
-- statement:
--   A public-coin protocol is **$(\varepsilon,\delta)$-differentially private** if for every pair of neighbouring samples $S,S'\in\mathcal X^s$, every prover strategy $g$, and every set $E$ of transcripts $(\sigma,b,d)$,
--
--   $$
--   \Pr[\mathrm{Interact}(Q,g,S)\in E]\;\le\;e^{\varepsilon}\Pr[\mathrm{Interact}(Q,g,S')\in E]+\delta .
--   $$
--
--   This is Definition 2.2 for public-coin protocols, the privacy guarantee of the protocol built by Theorem 4.1 and Corollary 4.5.
--
--   **Formalization Note** Neighbouring samples differ in one coordinate; provers are deterministic strategies; events are finite sets of transcripts.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definitions 2.1–2.2, p.4 (PDF p.7)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_DPVerify_AMProtocol

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

namespace AMProtocol

variable {X : Type} [MeasurableSpace X] {s : ℕ}

/-- An `(ε, δ)`-differentially private public-coin protocol (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definition 2.2, p.4 = PDF p.7):
for every pair of adjacent samples `S, S′`, every prover strategy `g` and every set `E` of
transcripts `(σ, b, d)`, `Pr[Interact(Q, g, S) ∈ E] ≤ e^ε · Pr[Interact(Q, g, S′) ∈ E] + δ`.

**Formalization Note** Adjacency is the published `PrivLearn.Generic.Neighbors` (one entry
substituted), as for `OneRoundProtocol.IsDP`. The adversary ranges over every deterministic
prover strategy (randomized provers are mixtures). Events are `Finset`s of the finite transcript
space; the transcript records the public coins, the reply and the decision bit. -/
def IsDP (Q : AMProtocol X s) (ε δ : ℝ) : Prop :=
  ∀ g : (Fin Q.nbits → Bool) → Q.B, ∀ S S' : Fin s → X, PrivLearn.Generic.Neighbors S S' →
    ∀ E : Finset ((Fin Q.nbits → Bool) × Q.B × Bool),
      ∑ t ∈ E, Q.transcript g S t ≤ Real.exp ε * ∑ t ∈ E, Q.transcript g S' t + δ

end AMProtocol

end DPVerify


