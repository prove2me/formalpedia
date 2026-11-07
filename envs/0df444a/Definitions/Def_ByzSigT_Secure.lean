-- Prove2me | Definitions.Def_ByzSigT_Secure
-- name    : ByzSigT_Secure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:55:13.965286+00:00
-- url     : https://prove2.me/theorems/e6e6c3b7-37fc-47bc-b0fa-536d08c8c241
-- title:
--   Byzantine agreement and $f$-security
-- statement:
--   Fix a protocol, a corrupt set $F$, inputs $u$ and an execution. A correct party **decides** $v$ when its handler emits the action "decide $v$".
--
--   1. **Agreement:** no two correct parties decide different values.
--   2. **Termination:** every correct party decides.
--   3. **Validity:** if $F=\emptyset$ and all inputs equal $c$, no party decides a value other than $c$.
--
--   The protocol is **$f$-secure** with delay bound $\Delta$ when all three hold for every corrupt set with $|F|\le f$, all inputs, every $\mathrm{GST}\ge 0$ and every execution.
--
--   These are the properties the mission's goal asks of a protocol. Validity is the printed form, which constrains only runs with no corruption; the Remark on p.6 says the stronger notion of strong unanimity is unattainable in partial synchrony for $f\ge n/3$.
--
--   **Formalization Note** Values $\{0,1\}$ are `Bool`, with $0$ = `false`. Agreement constrains every decide action of correct parties, so a party that decided twice with different values violates it.
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), §2, pp.5–6 (PDF 6–7); proof of Theorem 4.1, p.26 (PDF 27)

import Mathlib
import Definitions.Def_ByzSigT_IsExecution

namespace ByzSigT

/-!
# Byzantine agreement and f-security

Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…), §2 "Byzantine Agreement", pp.5–6: every correct party `p`
holds an input `u_p ∈ {0, 1}`;
* Agreement: No two correct processes decide different values.
* Termination: Every correct process eventually decides.
* Validity: If all parties are correct and input the same value u, then no correct party decides a
  value different from u.

A protocol is `f`-secure when it satisfies the three properties against every `f`-bounded adversary
(proof of Theorem 4.1, p.26): for every corrupt set `F` with `|F| ≤ f`, all inputs, every
`GST ≥ 0` and every execution.

**Formalization Note.** Values `{0, 1}` are `Bool` (`0 = false`). A correct party decides `v` when
its handler emits the action `decide v`; agreement constrains every such action of correct parties.
Validity is the printed one (`F = ∅`), not strong unanimity, which the Remark on p.6 says is
unattainable for `f ≥ n/3`. The delay bound `Δ` is fixed before the protocol is used, so a protocol
may depend on it; `GST` is chosen by the adversary.
-/

variable {n k : ℕ}

/-- Party `p` decides `v` in execution `E` of `P` (with inputs `u`). -/
def Decides (P : Protocol n k) (u : Fin n → Bool) (E : Execution n k) (p : Fin n) (v : Bool) :
    Prop :=
  ∃ j, Action.decide v ∈ E.actionsAt P u p j

/-- Agreement: no two correct parties decide different values. -/
def Agreement (P : Protocol n k) (F : Finset (Fin n)) (u : Fin n → Bool) (E : Execution n k) :
    Prop :=
  ∀ p ∉ F, ∀ q ∉ F, ∀ v w : Bool, Decides P u E p v → Decides P u E q w → v = w

/-- Termination: every correct party decides. -/
def Termination (P : Protocol n k) (F : Finset (Fin n)) (u : Fin n → Bool) (E : Execution n k) :
    Prop :=
  ∀ p ∉ F, ∃ v : Bool, Decides P u E p v

/-- Validity: if all parties are correct and have the same input `c`, no correct party decides a
value other than `c`. -/
def Validity (P : Protocol n k) (F : Finset (Fin n)) (u : Fin n → Bool) (E : Execution n k) :
    Prop :=
  F = ∅ → ∀ c : Bool, (∀ p, u p = c) → ∀ (p : Fin n) (v : Bool), Decides P u E p v → v = c

/-- `P` is an `f`-secure BA protocol in partial synchrony with delay bound `Δ`. -/
def Secure (P : Protocol n k) (f : ℕ) (Δ : ℝ) : Prop :=
  ∀ F : Finset (Fin n), F.card ≤ f → ∀ (u : Fin n → Bool) (GST : ℝ), 0 ≤ GST →
    ∀ E : Execution n k, IsExecution P F u GST Δ E →
      Agreement P F u E ∧ Termination P F u E ∧ Validity P F u E

end ByzSigT


