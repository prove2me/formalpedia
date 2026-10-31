-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P69
-- name    : QAlgorithms_Papers_Independent_Intake100_P69
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:25:34.737481+00:00
-- url     : https://prove2.me/theorems/eb9afe43-3b2a-46b7-8b82-7925381ea9e4
-- title:
--   Definitions for Generalized teleportation and entanglement recycling
-- statement:
--   The objects the formalized statements of *Generalized teleportation and entanglement recycling* (arXiv:1209.2683) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `singletAmplitude`: PDF pp.1,3: amplitudes of the normalized singlet, in Alice/Bob order.
--   - `OneAlice`: PDF p.3: Alice's input qubit followed by her N port halves.
--   - `recyclingInput`: PDF pp.3,6: the input/reference singlet and the N resource singlets. The second factor consists of R0 followed by Bob's N halves.
--   - `portSignal`: PDF p.3: sigma_i = 2^{-(N-1)} Pminus_{A0,Ai} tensor I on other Alice halves. Theorems use N >= 1, so N-1 is the number of unused Alice halves.
--   - `signalSum`: PDF p.3: rho is constructed as the sum of the port signals.
--   - `supportInvSqrt`: PDF pp.3,6: support inverse square root. The scalar inverse sends zero to zero; functional calculus is on the finite spectrum, including at the singular endpoint.
--   - `recyclingEffect`: PDF pp.3,6: conclusive square-root-measurement effect E_i. No input state is an argument of the measurement. A complementary failure effect is permitted by (21).
--   - `recyclingBranch`: PDF p.6, (18): the unnormalized branch after the positive square root of E_i. The identity acts on R0 and every Bob half, so R0 is untouched.
--   - `recyclingIdeal`: PDF p.3: the normalized ideal full branch, with singlets A0-Ai and R0-Bi, and every unused Aj-Bj. This explicit product corrects the factor in p.6, (20): that printed vector has norm 1/2, whereas the p.3 vector is a unit vector. The change is normalization only; overall singlet-swapping phase is immaterial.
--   - `recyclingFidelity`: PDF p.3, (3), and p.6, (18)-(25): conclusive outcome average of full-branch ROOT fidelities. For an unnormalized branch v, p = ||v||^2, so its contribution p |<ideal|v/||v||>| is ||v|| |<ideal|v>|. This formula assigns zero to a zero-probability branch without division. A nonnegative failure term from (21) can only increase this quantity. Simultaneous swaps of actual and ideal ports leave these overlaps invariant.
--   - `deterministicPortEffect`: PDF pp.3-4: original deterministic one-input PBT measurement, completed symmetrically on the kernel. The completion is an Alice-only effect and requires no correction by Bob. Unlike recycling, the unused resource is discarded.
--   - `singlePortFidelity`: PDF p.4, (8)-(9), with p.10, (80) at k=1: entanglement fidelity of the original deterministic single-input channel, (1/4) sum_i Tr(E_i sigma_i). The signals are normalized. This is a physical channel expression, not the unjustified exact scalar 1-3/(4N) appearing in (8).
--   - `Assignment`: PDF pp.4,10: an ordered assignment of the k labeled inputs to distinct ports.
--   - `JointRegister`: PDF pp.4,10: k input halves (or reference halves), followed by N port halves.
--   - `simultaneousInput`: PDF pp.3-4,10: N resource singlets and k independent input/reference singlets. This is the normalized Choi test input for JOINT entanglement fidelity.
--   - `selectedTarget`: PDF pp.4,10: the target singlet projector between the reference halves and the selected Bob halves in input order, tensor identity on every unselected Bob half. Expectation of this operator traces out unused Bob ports; it does not test their resource fidelity. Only register selection is allowed on Bob's side.
--   - `SimMeasurement`: PDF pp.4,10: a single joint measurement on Alice's inputs and N halves. It has one outcome for every ordered injection, and has no input-state argument.
--   - `simultaneousBranch`: PDF pp.4,10: unnormalized branch of an Alice-only joint measurement. Choosing the positive square root gives the same Bob reduced channel as any instrument with these effects, since Alice's registers are discarded.
--   - `simultaneousFidelity`: PDF p.4, (6)-(7), and p.10, (80): JOINT entanglement fidelity of the operational protocol: measure Alice once, announce the injection once, retain Bob's selected ports in input order, and discard all other registers. The sum is unconditional; each branch is subnormalized. Both resource and test input are normalized singlets, so Bob performs no corrective unitary.
-- source:
--   Generalized teleportation and entanglement recycling, arXiv:1209.2683v2, https://arxiv.org/abs/1209.2683v2

import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
# Generalized teleportation and entanglement recycling

Strelchuk, Horodecki and Oppenheim, arXiv:1209.2683v2.
All new objects are local to this paper. Recycling uses root fidelity of the full
resource; simultaneous and parallel teleportation use joint entanglement fidelity.
The source ambiguities and normalisation correction are recorded in the unit artifacts.
-/

namespace QAlgorithms.Papers.Independent.Intake100.P69

open scoped ComplexConjugate
open Filter

/-- PDF pp.1,3: amplitudes of the normalized singlet, in Alice/Bob order. -/
noncomputable def singletAmplitude (a b : Bool) : ℂ :=
  if a = b then 0 else if a then -((Real.sqrt 2 : ℂ)⁻¹) else (Real.sqrt 2 : ℂ)⁻¹

/-- PDF p.3: Alice's input qubit followed by her N port halves. -/
abbrev OneAlice (N : ℕ) := Bool × Qubits N

/-- PDF pp.3,6: the input/reference singlet and the N resource singlets.
The second factor consists of R0 followed by Bob's N halves. -/
noncomputable def recyclingInput (N : ℕ) :
    EuclideanSpace ℂ (OneAlice N × OneAlice N) :=
  WithLp.toLp 2 fun z =>
    singletAmplitude z.1.1 z.2.1 *
      ∏ j : Fin N, singletAmplitude (z.1.2 j) (z.2.2 j)

/-- PDF p.3: sigma_i = 2^{-(N-1)} Pminus_{A0,Ai} tensor I on other Alice halves.
Theorems use N >= 1, so N-1 is the number of unused Alice halves. -/
noncomputable def portSignal (N : ℕ) (i : Fin N) :
    Matrix (OneAlice N) (OneAlice N) ℂ := by
  classical
  exact fun a b =>
    ((2 : ℂ) ^ (N - 1))⁻¹ *
      singletAmplitude a.1 (a.2 i) * conj (singletAmplitude b.1 (b.2 i)) *
      (if ∀ j : Fin N, j ≠ i → a.2 j = b.2 j then 1 else 0)

/-- PDF p.3: rho is constructed as the sum of the port signals. -/
noncomputable def signalSum (N : ℕ) : Matrix (OneAlice N) (OneAlice N) ℂ :=
  ∑ i : Fin N, portSignal N i

/-- PDF pp.3,6: support inverse square root. The scalar inverse sends zero to zero;
functional calculus is on the finite spectrum, including at the singular endpoint. -/
noncomputable def supportInvSqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A

/-- PDF pp.3,6: conclusive square-root-measurement effect E_i. No input state is
an argument of the measurement. A complementary failure effect is permitted by (21). -/
noncomputable def recyclingEffect (N : ℕ) (i : Fin N) :
    Matrix (OneAlice N) (OneAlice N) ℂ :=
  supportInvSqrt (signalSum N) * portSignal N i * supportInvSqrt (signalSum N)

/-- PDF p.6, (18): the unnormalized branch after the positive square root of E_i.
The identity acts on R0 and every Bob half, so R0 is untouched. -/
noncomputable def recyclingBranch (N : ℕ) (i : Fin N) :
    EuclideanSpace ℂ (OneAlice N × OneAlice N) :=
  act (Matrix.kronecker (cfc Real.sqrt (recyclingEffect N i)) 1) (recyclingInput N)

/-- PDF p.3: the normalized ideal full branch, with singlets A0-Ai and R0-Bi,
and every unused Aj-Bj. This explicit product corrects the factor in p.6, (20):
that printed vector has norm 1/2, whereas the p.3 vector is a unit vector.
The change is normalization only; overall singlet-swapping phase is immaterial. -/
noncomputable def recyclingIdeal (N : ℕ) (i : Fin N) :
    EuclideanSpace ℂ (OneAlice N × OneAlice N) := by
  classical
  exact WithLp.toLp 2 fun z =>
    singletAmplitude z.1.1 (z.1.2 i) * singletAmplitude z.2.1 (z.2.2 i) *
      ∏ j ∈ Finset.univ.erase i, singletAmplitude (z.1.2 j) (z.2.2 j)

/-- PDF p.3, (3), and p.6, (18)-(25): conclusive outcome average of full-branch
ROOT fidelities. For an unnormalized branch v, p = ||v||^2, so its contribution
p |<ideal|v/||v||>| is ||v|| |<ideal|v>|. This formula assigns zero to a
zero-probability branch without division. A nonnegative failure term from (21)
can only increase this quantity. Simultaneous swaps of actual and ideal ports
leave these overlaps invariant. -/
noncomputable def recyclingFidelity (N : ℕ) : ℝ :=
  ∑ i : Fin N, ‖recyclingBranch N i‖ *
    ‖inner ℂ (recyclingIdeal N i) (recyclingBranch N i)‖

/-- PDF pp.3-4: original deterministic one-input PBT measurement, completed
symmetrically on the kernel. The completion is an Alice-only effect and requires
no correction by Bob. Unlike recycling, the unused resource is discarded. -/
noncomputable def deterministicPortEffect (N : ℕ) (i : Fin N) :
    Matrix (OneAlice N) (OneAlice N) ℂ :=
  recyclingEffect N i + (N : ℂ)⁻¹ • (1 - ∑ j : Fin N, recyclingEffect N j)

/-- PDF p.4, (8)-(9), with p.10, (80) at k=1: entanglement fidelity of the
original deterministic single-input channel, (1/4) sum_i Tr(E_i sigma_i).
The signals are normalized. This is a physical channel expression, not the
unjustified exact scalar 1-3/(4N) appearing in (8). -/
noncomputable def singlePortFidelity (N : ℕ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i : Fin N,
    (deterministicPortEffect N i * portSignal N i).trace.re

/-- PDF pp.4,10: an ordered assignment of the k labeled inputs to distinct ports. -/
abbrev Assignment (N k : ℕ) := Fin k ↪ Fin N

/-- PDF pp.4,10: k input halves (or reference halves), followed by N port halves. -/
abbrev JointRegister (N k : ℕ) := Qubits k × Qubits N

/-- PDF pp.3-4,10: N resource singlets and k independent input/reference singlets.
This is the normalized Choi test input for JOINT entanglement fidelity. -/
noncomputable def simultaneousInput (N k : ℕ) :
    EuclideanSpace ℂ (JointRegister N k × JointRegister N k) :=
  WithLp.toLp 2 fun z =>
    (∏ l : Fin k, singletAmplitude (z.1.1 l) (z.2.1 l)) *
      ∏ j : Fin N, singletAmplitude (z.1.2 j) (z.2.2 j)

/-- PDF pp.4,10: the target singlet projector between the reference halves and
the selected Bob halves in input order, tensor identity on every unselected Bob
half. Expectation of this operator traces out unused Bob ports; it does not test
their resource fidelity. Only register selection is allowed on Bob's side. -/
noncomputable def selectedTarget (N k : ℕ) (f : Assignment N k) :
    Matrix (JointRegister N k) (JointRegister N k) ℂ := by
  classical
  exact fun a b =>
    (∏ l : Fin k, singletAmplitude (a.1 l) (a.2 (f l)) *
      conj (singletAmplitude (b.1 l) (b.2 (f l)))) *
      (if ∀ j : Fin N, (∀ l : Fin k, f l ≠ j) → a.2 j = b.2 j then 1 else 0)

/-- PDF pp.4,10: a single joint measurement on Alice's inputs and N halves.
It has one outcome for every ordered injection, and has no input-state argument. -/
abbrev SimMeasurement (N k : ℕ) :=
  Assignment N k → Matrix (JointRegister N k) (JointRegister N k) ℂ

/-- PDF pp.4,10: unnormalized branch of an Alice-only joint measurement.
Choosing the positive square root gives the same Bob reduced channel as any
instrument with these effects, since Alice's registers are discarded. -/
noncomputable def simultaneousBranch {N k : ℕ} (M : SimMeasurement N k)
    (f : Assignment N k) :
    EuclideanSpace ℂ (JointRegister N k × JointRegister N k) :=
  act (Matrix.kronecker (cfc Real.sqrt (M f)) 1) (simultaneousInput N k)

/-- PDF p.4, (6)-(7), and p.10, (80): JOINT entanglement fidelity of the
operational protocol: measure Alice once, announce the injection once, retain
Bob's selected ports in input order, and discard all other registers. The sum
is unconditional; each branch is subnormalized. Both resource and test input
are normalized singlets, so Bob performs no corrective unitary. -/
noncomputable def simultaneousFidelity {N k : ℕ} (M : SimMeasurement N k) : ℝ :=
  ∑ f : Assignment N k,
    (inner ℂ (simultaneousBranch M f)
      (act (Matrix.kronecker 1 (selectedTarget N k f)) (simultaneousBranch M f))).re

/-! Small sanity checks of signs, unused-register factors and zero branches. -/

example (a : Bool) : singletAmplitude a a = 0 := by
  simp [singletAmplitude]

example : singletAmplitude false true = -singletAmplitude true false := by
  simp [singletAmplitude]

example (z : OneAlice 0 × OneAlice 0) :
    recyclingInput 0 z = singletAmplitude z.1.1 z.2.1 := by
  simp [recyclingInput]

example : recyclingFidelity 0 = 0 := by
  simp [recyclingFidelity]

example (N : ℕ) : singlePortFidelity (N / 0) ^ (0 : ℕ) = 1 := by
  simp

example (N k : ℕ) (f : Assignment N k) (b : Qubits N) (r : Qubits k) :
    selectedTarget N k f (r, b) (r, b) =
      ∏ l : Fin k, singletAmplitude (r l) (b (f l)) *
        conj (singletAmplitude (r l) (b (f l))) := by
  simp [selectedTarget]

end QAlgorithms.Papers.Independent.Intake100.P69


