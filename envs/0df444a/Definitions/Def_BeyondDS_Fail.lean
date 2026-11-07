-- Prove2me | Definitions.Def_BeyondDS_Fail
-- name    : BeyondDS_Fail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:10:06.672196+00:00
-- url     : https://prove2.me/theorems/af82cde3-2748-432f-a8d0-8c1ed1ef11ed
-- title:
--   Message count $M$, round count $T$, the forgery event and broadcast failure
-- statement:
--   For an outcome $\omega$ of an execution:
--
--   1. $M(\omega)$ is the number of honest transmissions to a destination other than the sender: "every message sent while its sender is honest, including senders corrupted later and transmissions after a decision until sending stops"; a self-send is a free local delivery.
--   2. $T(\omega)$ is the number of rounds until every uncorrupted player has halted, and the public round cap if that never happens.
--   3. $\mathrm{Forge}(\omega)$: some honest player verified a signature attributed to identity $j$ on a message $m$ which was accepted while $j$ was uncorrupted and $j$ had not yet signed $m$. This is the complement of the authentication event: "any verifying data attributed to a currently uncorrupted player were signed by that player".
--   4. $\mathrm{Fail}(\omega)$, broadcast failure: not all of agreement (all forever-honest decisions coincide), validity (if the sender is forever honest, every forever-honest decision equals its input) and termination (every forever-honest player decides), a player's decision being its first.
--
--   Probabilities and expectations are taken over the discrete law of outcomes, with values in $[0,\infty]$.
--
--   **Formalization Note** "Not yet signed at the time of verification" is the event an EUF-CMA reduction controls; a signature produced before its signer signs counts as a forgery. Expectations are sums $\sum_\omega D(\omega)\,x(\omega)$ in $[0,\infty]$, so no integrability side condition can make a bound vacuous.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §4.2, p.12 (PDF p.13); §4.3, p.13 (PDF p.14), eq. (4)

import Mathlib
import Definitions.Def_BeyondDS_execFrom

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal

namespace BeyondDS

variable {n : ℕ} {Msg St σ : Type}

/-- The probability of an event under an outcome law. -/
noncomputable def prob {α : Type} (D : PMF α) (E : Set α) : ℝ≥0∞ := D.toOuterMeasure E

/-- The expectation of a nonnegative quantity under an outcome law, with values in `[0, ∞]`. -/
noncomputable def expect {α : Type} (D : PMF α) (x : α → ℕ) : ℝ≥0∞ := ∑' ω, D ω * (x ω : ℝ≥0∞)

/-- `M` of §4.3, p.13: "every message sent while its sender is honest, including senders corrupted later
and transmissions after a decision until sending stops". A self-send is a free local delivery
(§5.1, p.14). -/
def msgCount (ω : Config n Msg St σ) : ℕ :=
  (ω.log.filter fun e =>
    match e with
    | Event.obs (Obs.sent i j _) => i != j
    | _ => false).length

/-- `T` of §4.3, p.13: "the number of rounds until every currently honest player has halted"; the
public cap if that never happens. -/
def roundsUsed (Pi : Protocol Msg St) (P : Params) (ω : Config P.n Msg St σ) : ℕ :=
  ω.doneAt.getD (Pi.roundCap P)

/-- The complement of the authentication event of §4.2, p.12: "any verifying data attributed to a
currently uncorrupted player were signed by that player".

**Formalization Note.** The test is "not yet signed at the time of verification", so a signature
predicted before its signer signs is a forgery. §7.1's "never signed" is the same event for
acknowledgements on histories in which the honest signer does not sign later; the reading is `paper.md`
decision 6, and is the event EUF-CMA controls. -/
def Forge (ω : Config n Msg St σ) : Prop :=
  ∃ i j m, Event.forgery i j m ∈ ω.log

/-- The error event of §4.3, p.13 for Byzantine broadcast, §4.2, p.12: not (agreement and validity and
termination), over forever-honest players, with a player's decision its first. -/
def Fail (P : Params) (x : Bool) (ω : Config P.n Msg St σ) : Prop :=
  ¬ ((∀ i j, ω.ForeverHonest i → ω.ForeverHonest j → ∀ b b', ω.decision i = some b →
        ω.decision j = some b' → b = b') ∧
      (ω.ForeverHonest P.sender → ∀ i, ω.ForeverHonest i → ∀ b, ω.decision i = some b → b = x) ∧
      (∀ i, ω.ForeverHonest i → (ω.decision i).isSome = true))

end BeyondDS


