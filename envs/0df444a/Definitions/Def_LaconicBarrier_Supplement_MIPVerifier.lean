-- Prove2me | Definitions.Def_LaconicBarrier_Supplement_MIPVerifier
-- name    : LaconicBarrier_Supplement_MIPVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:31:44.524274+00:00
-- url     : https://prove2.me/theorems/cb39bb45-8d98-402b-b2e3-5853b166e2ac
-- title:
--   Multiprover verifiers with one round trip per prover, and their execution
-- statement:
--   A **multiprover verifier** on common input $i$ uses $r$ private coins $\rho$. The provers $P_1, P_2, \dots$ are computationally unbounded and cannot communicate. Each prover receives at most one question and sends one reply, and its reply depends only on the common input, its identity, its own question and its coins. Given the transcript so far, a list of entries (prover $j$, question $q$, reply $a$), the verifier either asks a not-yet-contacted prover a question, chosen adaptively from all earlier replies, or stops with its decision.
--
--   The acceptance probability $\Pr[\langle P_1, \dots, P_{k'}, V \rangle(i) = 1]$ is taken over the verifier's coins and the provers' independent coins; a reply longer than $\ell_P$ bits is rejected. The protocol is **non-adaptive** if, from the input and the verifier's coins alone, the whole list of (prover, question) pairs is fixed before any reply arrives.
--
--   This is the protocol model of Theorem 8.3.
--
--   **Formalization Note** A prover is given by the distribution of its reply to each question; the verifier is run for $k' + 1$ actions (one question to each of at most $k'$ provers, then the decision). A transcript is *consistent* with the coins if each recorded question is the one the verifier asks after the earlier entries.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.2.2, p.27 (Syntax and the Remark after Definition 4.32)

import Mathlib
import Definitions.Def_LaconicBarrier_RunsWithin
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace LaconicBarrier.Supplement

/-- An action of a multiprover verifier: send the question `q` to prover `j`, or stop with the
decision `b`. -/
inductive MIPAct where
  | ask (j : ℕ) (q : List Bool)
  | stop (b : Bool)

/-- The code of a verifier action (a tagged tuple, the prover index in unary). -/
def MIPAct.code : MIPAct → List Bool
  | .ask j q => QAdvFew.PoQOracle.tup [[false], unary j, q]
  | .stop b => QAdvFew.PoQOracle.tup [[true], [b]]

/-- The code of one entry `(j, q, a)` of a multiprover transcript: prover `j` was asked `q` and
replied `a`. -/
def mipEntryCode (e : ℕ × List Bool × List Bool) : List Bool :=
  QAdvFew.PoQOracle.tup [unary e.1, e.2.1, e.2.2]

/-- A **verifier of a multiprover interactive proof** with at most one round trip per prover, on
common inputs of type `I` (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds
for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), §4.2.2, p.27,
"Syntax", and the Remark after Definition 4.32: "at most one round trip between the verifier and each
prover: one verifier message followed by one prover reply. The verifier may choose the next prover and
its question adaptively from earlier replies; each prover sees only its own question"). On input `i`
it uses `coins i` coins `ρ`; given the transcript so far (entries `(j, q, a)` in order) it asks the
next prover a question or stops with its decision. -/
structure MIPVerifier (I : Type) where
  /-- the number of verifier coins on input `i` -/
  coins : I → ℕ
  /-- the next action from the input, the coins and the transcript so far -/
  next : (i : I) → (Fin (coins i) → Bool) → List (ℕ × List Bool × List Bool) → MIPAct

/-- One execution of the verifier against the prover strategies `P` (prover `j`, question `q` ↦ the
distribution of its reply), for at most `fuel` more actions. A reply longer than `ℓ_P` bits is
rejected; running out of actions is a rejection. -/
noncomputable def MIPVerifier.exec {I : Type} (V : MIPVerifier I) (i : I)
    (ρ : Fin (V.coins i) → Bool) (ℓP : ℕ) (P : ℕ → List Bool → PMF (List Bool)) :
    ℕ → List (ℕ × List Bool × List Bool) → PMF Bool
  | 0, _ => PMF.pure false
  | f + 1, h =>
    match V.next i ρ h with
    | .stop b => PMF.pure b
    | .ask j q => (P j q).bind fun a =>
        if a.length ≤ ℓP then V.exec i ρ ℓP P f (h ++ [(j, q, a)]) else PMF.pure false

/-- `Pr[⟨P₁, …, P_{k′}, V⟩(i) = 1]`, the probability over the verifier's coins and the provers'
independent private coins, with every reply limited to `ℓ_P` bits; the verifier is run for `k′ + 1`
actions (at most one question to each of the `k′` provers, then the decision). -/
noncomputable def MIPVerifier.accProb {I : Type} (V : MIPVerifier I) (i : I) (kP ℓP : ℕ)
    (P : ℕ → List Bool → PMF (List Bool)) : ℝ :=
  (((PMF.uniformOfFintype (Fin (V.coins i) → Bool)).bind fun ρ =>
    V.exec i ρ ℓP P (kP + 1) []) true).toReal

/-- The transcript `h` is consistent with the verifier's coins `ρ` on input `i`: each entry's
prover index and question are what the verifier asks after the earlier entries (the replies are
arbitrary). -/
def MIPVerifier.Consistent {I : Type} (V : MIPVerifier I) (i : I) (ρ : Fin (V.coins i) → Bool)
    (h : List (ℕ × List Bool × List Bool)) : Prop :=
  ∀ (t : ℕ) (ht : t < h.length), V.next i ρ (h.take t) = .ask (h[t]'ht).1 (h[t]'ht).2.1

/-- The protocol is **non-adaptive** (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript
sha256 1af78662…), Remark after Definition 4.32, p.27: "We call the protocol non-adaptive if all
questions and their recipients are fixed before any replies are received"): from the input and the
coins alone there is a list of (prover, question) pairs, and the `t`-th question the verifier asks
on any consistent transcript is the `t`-th entry of the list. -/
def MIPVerifier.IsNonAdaptive {I : Type} (V : MIPVerifier I) : Prop :=
  ∃ Q : (i : I) → (Fin (V.coins i) → Bool) → List (ℕ × List Bool),
    ∀ (i : I) (ρ : Fin (V.coins i) → Bool) (h : List (ℕ × List Bool × List Bool)) (j : ℕ)
      (q : List Bool), V.Consistent i ρ h → V.next i ρ h = .ask j q →
        (Q i ρ)[h.length]? = some (j, q)

end LaconicBarrier.Supplement


