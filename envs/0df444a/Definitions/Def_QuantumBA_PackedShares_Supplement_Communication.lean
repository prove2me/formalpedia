-- Prove2me | Definitions.Def_QuantumBA_PackedShares_Supplement_Communication
-- name    : QuantumBA_PackedShares_Supplement_Communication
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:38:12.338202+00:00
-- url     : https://prove2.me/theorems/567d41de-9dcb-4d90-8776-9fdca4e07570
-- title:
--   Honest-sent event costs and worst-case expected combined communication
-- statement:
--   Fix a qubit protocol $P$, input vector $x$, adaptive adversary $A$, corruption budget $t$ and trajectory $\omega$. For every round $r$, channel kind and staged-packet index, $T$ specifies a sending boundary between staging and delivery. Only packets whose sender is honest at that boundary are charged. $C_T$ counts the actual classical message bits and quantum-header bits, and $Q_T$ counts qubits. Every classical or quantum channel use costs at least one unit even if empty; each recipient is a separate transmission. Include setup and replies to faulty recipients, in rounds through the last correct halt.
--   $$
--    C_T=\sum_r C_{T,r},\qquad Q_T=\sum_r Q_{T,r},\qquad
--    K_T(P,t)=\sup_x\sup_A\mathbb E_{x,A}[C_T+Q_T]\in[0,\infty].
--   $$
--   All sums, expectations and suprema are nonnegative extended-real operations. The supremum is outside expectation and the two communication kinds are added before taking it. In particular, an infinite expectation or unbounded collection of expectations gives infinity.
--
--   The constant last-boundary timing defines the conservative auxiliary count: a sender is charged only if honest through delivery. Permanent corruption makes this count no larger than the count for any earlier sending placement. This order relation is a proof obligation, not a field of the interface. In Section 7 every counted reference sender is correct, so every reference transmission remains counted. The imported staging counters are unchanged.
--
--   **Formalization Note** There are $n+2$ possible sending boundaries: immediately after honest staging and after each of the $n+1$ rushing adversarial steps. $T$ is accounting data, may depend on the full trajectory, and supplies no information to protocol execution. A quantum packet is a list of qubits, with one classical header per listed register.
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), p. 2, Section 1.1 and Theorem 2; pp. 34–35, Section 7 (PDF 3, 35–36)

import Definitions.Def_QuantumBA_PackedShares_Supplement_Physical

set_option autoImplicit false

open scoped ENNReal

namespace QuantumBA.PackedShares.Supplement

variable {n : ℕ} (P : Protocol n Qubit)

/-- Placement of the sending event of each prescribed transmission between staging and
delivery. Slots 0,...,n+1 are the boundaries after staging and after each of the n+1 rushing
adversarial steps. Dependence on the full execution is allowed for accounting only; this
does not give an honest algorithm any extra information. `false` selects classical packets,
`true` quantum packets. The last argument is the packet's index in the staged list. -/
abbrev SendTiming := (Fin n → Bool) → Adversary n Qubit P.M P.Hd →
  (ℕ → Outcome Qubit) → ℕ → Bool → ℕ → Fin (n + 2)

/-- The smallest counting convention: sender must stay honest through delivery. This is
an accounting auxiliary, not a replacement for the source's honest-sent convention. -/
def deliveryTiming : SendTiming P := fun _ _ _ _ _ _ => ⟨n + 1, by omega⟩

/-- Boundary after the honest computation and staging step of round r. -/
def stagedBoundary (n r : ℕ) : ℕ := r * stepsPerRound n + n + 2

/-- The sending boundary, before the corresponding delivery, with corruption tested here. -/
def sendBoundary (T : SendTiming P) (x : Fin n → Bool) (A : Adversary n Qubit P.M P.Hd)
    (ω : ℕ → Outcome Qubit) (r : ℕ) (quantum : Bool) (i : ℕ) : ℕ :=
  stagedBoundary n r + (T x A ω r quantum i).val

/-- Source C and Q in one round: classical packets have their actual bit lengths, including
the one-unit minimum; quantum packets have their qubit lengths, including the one-unit
minimum, and their headers are charged to C. Every recipient is a separate list entry.
Only events whose sender is still honest at the sending boundary are charged. -/
noncomputable def roundSource (T : SendTiming P) (x : Fin n → Bool)
    (A : Adversary n Qubit P.M P.Hd) (t : ℕ) (ω : ℕ → Outcome Qubit) (r : ℕ) : ℕ × ℕ := by
  classical
  let c := cfgAt P x A t ω (stagedBoundary n r)
  let cs := c.stagedC.mapIdx (fun i m =>
    if m.1 ∉ (cfgAt P x A t ω (sendBoundary P T x A ω r false i)).bad
    then chargeC P [(m.2.1, m.2.2)] [] else 0)
  let qcs := c.stagedQ.mapIdx (fun i m =>
    if m.1 ∉ (cfgAt P x A t ω (sendBoundary P T x A ω r true i)).bad
    then chargeC P [] [(m.2.1, m.2.2)] else 0)
  let qs := c.stagedQ.mapIdx (fun i m =>
    if m.1 ∉ (cfgAt P x A t ω (sendBoundary P T x A ω r true i)).bad
    then chargeQ P [(m.2.1, m.2.2)] else 0)
  exact (cs.sum + qcs.sum, qs.sum)

/-- Total honest-sent classical bits through the last correct halt, allowing infinity. -/
noncomputable def sourceC (T : SendTiming P) (x : Fin n → Bool)
    (A : Adversary n Qubit P.M P.Hd) (t : ℕ) (ω : ℕ → Outcome Qubit) : ℝ≥0∞ :=
  ∑' r : ℕ, if (r : ℕ∞) < roundsR P x A t ω then
    ((roundSource P T x A t ω r).1 : ℝ≥0∞) else 0

/-- Total honest-sent qubits through the last correct halt, allowing infinity. -/
noncomputable def sourceQ (T : SendTiming P) (x : Fin n → Bool)
    (A : Adversary n Qubit P.M P.Hd) (t : ℕ) (ω : ℕ → Outcome Qubit) : ℝ≥0∞ :=
  ∑' r : ℕ, if (r : ℕ∞) < roundsR P x A t ω then
    ((roundSource P T x A t ω r).2 : ℝ≥0∞) else 0

/-- The supremum is outside the expectation of the combined source costs. Unbounded
expectations and unbounded worst-case cost retain value infinity. -/
noncomputable def worstCommunication (t : ℕ) (T : SendTiming P) : ℝ≥0∞ :=
  ⨆ (x : Fin n → Bool) (A : Adversary n Qubit P.M P.Hd),
    expect P x A t (fun ω => sourceC P T x A t ω + sourceQ P T x A t ω)

end QuantumBA.PackedShares.Supplement


