-- Prove2me | Definitions.Def_KAQROM_Attacker
-- name    : KAQROM_Attacker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:04.878331+00:00
-- url     : https://prove2.me/theorems/c059c39d-4474-434f-b954-a0e5689c8ccd
-- title:
--   Definition 3.11: online interception attackers and $\mathrm{Adv}^{\mathsf{IntKR},\mathrm{mr}}$
-- statement:
--   An **online interception attacker** $E$ against $\Pi^{\mathrm{mr}}$ starts in an oracle-independent state. After each public prefix message it is activated on the transcript so far and its retained state, and may make classical oracle queries (here: a fixed number of query steps, each an instrument chosen by Eve's classical record). After the prefix, Bob's message register $\Psi$ is transferred to Eve, who makes quantum queries and outputs a classical key guess $K^*$. Eve never sees Alice's or Bob's registers or transcripts. The **advantage** is
--   $$
--   \mathrm{Adv}^{\mathsf{IntKR},\mathrm{mr}}_{\Pi^{\mathrm{mr}},E}=\Pr\bigl[K^*=K_B\neq\bot\bigr]
--   $$
--   in the experiment with $H\leftarrow\mathcal H$ uniform. The predicate *prefix queries at most $Q$* says that Eve's ordered prefix query list has length at most $Q$ on every oracle and every branch of positive probability.
--
--   The class is the one in the security clause of Definition 3.10: computationally unbounded, classical queries during the prefix, quantum queries after receiving $\Psi$.
--
--   **Formalization Note** Eve's final stage is a $q_E$-query quantum algorithm on her register and $\Psi$, selected by the public transcript and her own query list (both part of her retained classical state). Her register, work register and Kraus index types are part of the attacker. Alice's residual register, unused after the prefix, contributes only its trace.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.11 and the security clause of Definition 3.10, p.22

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_PrefixParty
import Definitions.Def_KAQROM_Protocol

namespace KAQROM

open Matrix
open scoped Kronecker

/-- **The attacker class of Definition 3.11 (online interception).** Eve has a register `RE`,
starts in an oracle-independent state, and is activated after each public prefix message on the
transcript so far and her retained state; in each activation she makes `DE` classical query steps
(instruments chosen by her classical record: the public transcript so far, her own ordered
query–answer transcript, the step index). After the prefix she receives Bob's message register
`Ψ` and runs a `qE`-query quantum algorithm on her register and `Ψ` (chosen by the complete
public transcript and her query transcript), whose classical outcome is her key guess
`K* ∈ K ∪ {⊥}`. She never sees Alice's or Bob's registers or transcripts.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.11
and the security clause of Definition 3.10 ("restricted to classical queries during the prefix
but allowed quantum queries after receiving Ψ"), p.22.

**Formalization Note.** Eve is computationally unbounded; only her queries are counted: the
classical prefix queries are the `some` outcomes of her query steps, and `qE` bounds her quantum
queries after receiving `Ψ`. Her register, work register and Kraus index types are part of the
attacker. -/
structure Attacker {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) where
  /-- Eve's register. -/
  RE : Type
  /-- Work register of Eve's final quantum stage. -/
  WE : Type
  /-- Kraus index type of Eve's instruments. -/
  ιE : Type
  [fRE : Fintype RE] [dRE : DecidableEq RE]
  [fWE : Fintype WE] [dWE : DecidableEq WE]
  [fιE : Fintype ιE]
  /-- Eve's initial state. -/
  ρE0 : Matrix RE RE ℂ
  ρE0_density : WildeQIT.IsDensityOperator ρE0
  /-- The number of classical query steps of each activation. -/
  DE : ℕ
  /-- Eve's query instruments, chosen by the public transcript so far (ending with the message
  just sent), her own transcript so far and the step index. -/
  query : List Msg → Transcript X ℓ → Fin DE → Instrument (Option X) RE RE ιE
  /-- The number of quantum queries of Eve's final stage. -/
  qE : ℕ
  /-- Eve's final stage on her register and `Ψ`, outputting the key guess `K*`. -/
  final : (Fin P.n → Msg) → Transcript X ℓ → QAlg X ℓ (RE × P.Ψ) WE Unit (Option K) ιE qE

attribute [instance] Attacker.fRE Attacker.dRE Attacker.fWE Attacker.dWE Attacker.fιE

namespace Attacker

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype K] {P : Protocol X ℓ Msg K}

/-- The classical outcomes of Eve's prefix activations: after each of the `2r − 1` messages, the
outcomes of her `DE` query steps. -/
abbrev Outcome (E : Attacker P) := Fin P.n → Fin E.DE → Option X

/-- Eve's run through the prefix with oracle `H`, public messages `m` and outcomes `oE`: after the
`i`-th message she is activated on the first `i + 1` messages. Returns her unnormalized state and
her ordered query–answer transcript. -/
noncomputable def run (E : Attacker P) (H : Oracle X ℓ) (m : Fin P.n → Msg) (oE : E.Outcome) :
    Matrix E.RE E.RE ℂ × Transcript X ℓ :=
  (List.finRange P.n).foldl
    (fun s i => (List.finRange E.DE).foldl
      (fun t k => queryStep (E.query ((List.ofFn m).take (i.val + 1)) t.2 k) H (oE i k) t) s)
    (E.ρE0, [])

/-- **`Adv^{IntKR,mr}_{Π^{mr},E} = Pr[IntKR^{mr}_{Π^{mr},E} = 1]`** (Definition 3.11, p.22):
`H ← ℋ` uniform; the honest prefix with Eve activated after each message; Bob's final stage on
`S_B` with outcome `K_B = some k` and message `Ψ`; Eve's final stage on her register and `Ψ`
with outcome `K* = some k`. The experiment outputs 1 iff `K* = K_B ≠ ⊥`. Alice's residual
register is not used after the prefix and contributes its trace. -/
noncomputable def advantage (E : Attacker P) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ o : P.Outcome, ∑ oE : E.Outcome,
    ∑ k : K, (P.aliceRun H o).1.trace.re *
      ((E.final (P.msgs o) (E.run H (P.msgs o) oE).2).run H
        ((E.run H (P.msgs o) oE).1 ⊗ₖ (P.Bq (P.msgs o)).run H (P.bobRun H o).1 (some k))
        (some k)).trace.re

/-- Eve makes at most `Q` classical queries during the prefix, in the worst case: on every oracle
and every branch of positive probability of the prefix together with her activations. -/
def PrefixQueriesLe (E : Attacker P) (Q : ℕ) : Prop :=
  ∀ (H : Oracle X ℓ) (o : P.Outcome) (oE : E.Outcome),
    0 < P.weight H o * (E.run H (P.msgs o) oE).1.trace.re →
      (E.run H (P.msgs o) oE).2.length ≤ Q

end Attacker

end KAQROM


