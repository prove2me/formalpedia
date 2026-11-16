-- Prove2me | Definitions.Def_InterleavedUnitaryNOF_LowerBound_Supplement_Quantum
-- name    : InterleavedUnitaryNOF_LowerBound_Supplement_Quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:45:29.524975+00:00
-- url     : https://prove2.me/theorems/cd0267b1-8727-4890-b838-368b52d9e4dd
-- title:
--   Operational three-player one-clean-qubit protocols
-- statement:
--   A run has a single moving register with basis $\{0,1\}\times\{0,\ldots,2^q-1\}$, initially held by a fixed player in the density matrix
--
--   $$\rho_0=|0\rangle\langle0|\otimes I_{2^q}/2^q.$$
--
--   A finite list of local gate tables fixes the acting players and their order. Alice's gates depend only on $(y,z)$, Bob's only on $(x,z)$, and Charlie's only on $(x,y)$. The whole register moves to the next acting player whenever the owner changes, then to the fixed final measuring player if necessary. There is no prior entanglement and no additional quantum memory. Physical validity requires every gate to be unitary on every input and the fixed measurement effect $P$ to be Hermitian and idempotent. The complementary outcome has effect $I-P$.
--
--   Evolution is successive unitary conjugation of $\rho_0$. Outcome probabilities are the real traces $\operatorname{Re}\operatorname{Tr}(P_b\rho_{\rm final})$. A protocol uses $L>0$ identical independent fresh runs and a fixed Boolean function of the $L$ outcomes at their common final player. Transcript probabilities are products of Born probabilities; error is the sum over transcripts with incorrect final output. Correctness at tolerance $\varepsilon$ is required on every input where the specified partial Boolean function is defined. These probabilities are derived from execution, never supplied as data or correctness certificates.
--
--   The communication cost is $L(q+1)$ times the number of register transfers per run. Final local output and local computation are free. This reusable model describes a concrete operational subclass sufficient for existential quantum communication upper bounds. Raw gate tables can be written before their physical validity is proved; every protocol asserted to exist in a theorem is required to satisfy that validity predicate.
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), §2, p.7, Quantum communication; p.3 footnote 1; Protocol 1, p.8

import Mathlib

namespace InterleavedUnitaryNOF.LowerBound.Supplement

/-- Three owners of the single moving register. -/
inductive Player where
  | alice | bob | charlie
  deriving DecidableEq

/-- One control qubit and q target qubits, with their computational basis. -/
abbrev Register (q : ℕ) := Bool × Fin (2^q)
abbrev QMat (q : ℕ) := Matrix (Register q) (Register q) ℂ

/-- Local gate tables: the constructor fixes the owner independently of the input.
Alice sees (y,z), Bob sees (x,z), and Charlie sees (x,y). Raw tables are admitted
here; physical unitarity is checked by `QuantumRun.WellFormed`, never assumed
as a correctness certificate. -/
inductive LocalGate (X Y Z : Type) (q : ℕ) where
  | alice : (Y → Z → QMat q) → LocalGate X Y Z q
  | bob : (X → Z → QMat q) → LocalGate X Y Z q
  | charlie : (X → Y → QMat q) → LocalGate X Y Z q

def LocalGate.owner {X Y Z : Type} {q : ℕ} : LocalGate X Y Z q → Player
  | .alice _ => .alice
  | .bob _ => .bob
  | .charlie _ => .charlie

def LocalGate.eval {X Y Z : Type} {q : ℕ} (g : LocalGate X Y Z q)
    (x : X) (y : Y) (z : Z) : QMat q :=
  match g with
  | .alice f => f y z
  | .bob f => f x z
  | .charlie f => f x y

/-- A fresh run. The only quantum memory is this register, initially all at
`initialOwner`. Before each gate it moves to that gate's owner when necessary,
and at the end to `finalOwner` for a fixed projective measurement. -/
structure QuantumRun (X Y Z : Type) where
  q : ℕ
  initialOwner : Player
  gates : List (LocalGate X Y Z q)
  finalOwner : Player
  projector : QMat q

/-- Exactly |0><0| tensor I/(2^q), independent of inputs and with no entanglement
or additional pure workspace. -/
noncomputable def initialDensity (q : ℕ) : QMat q :=
  fun i j => if i.1 = false ∧ j.1 = false ∧ i.2 = j.2 then 1 / (2^q : ℂ) else 0

namespace QuantumRun

/-- Structural physical validity only: unitary gates on every input, and a
Hermitian idempotent effect. The complementary outcome is I minus this effect. -/
def WellFormed {X Y Z : Type} (R : QuantumRun X Y Z) : Prop :=
  (∀ g ∈ R.gates, ∀ x y z,
    (g.eval x y z).conjTranspose * g.eval x y z = 1 ∧
    g.eval x y z * (g.eval x y z).conjTranspose = 1) ∧
  R.projector.IsHermitian ∧ R.projector * R.projector = R.projector

/-- Chronological conjugation of the density matrix by the local gates. -/
noncomputable def finalDensity {X Y Z : Type} (R : QuantumRun X Y Z)
    (x : X) (y : Y) (z : Z) : QMat R.q :=
  R.gates.foldl (fun ρ g => g.eval x y z * ρ * (g.eval x y z).conjTranspose)
    (initialDensity R.q)

/-- Born rule for both outcomes. No clipping, renormalization or supplied
acceptance probability is used. WellFormed makes these a probability law. -/
noncomputable def outcomeProb {X Y Z : Type} (R : QuantumRun X Y Z)
    (x : X) (y : Y) (z : Z) (b : Bool) : ℝ :=
  (Matrix.trace ((if b then R.projector else 1 - R.projector) *
    R.finalDensity x y z)).re

/-- Count actual whole-register transfers, including any transfer to the first
gate or the measuring owner. Local gates and the final local output are free. -/
def transfers {X Y Z : Type} (R : QuantumRun X Y Z) : ℕ :=
  let s := R.gates.foldl (fun (s : Player × ℕ) g =>
    (g.owner, s.2 + if s.1 = g.owner then 0 else 1)) (R.initialOwner, 0)
  s.2 + if s.1 = R.finalOwner then 0 else 1

def cost {X Y Z : Type} (R : QuantumRun X Y Z) : ℕ :=
  R.transfers * (1 + R.q)

end QuantumRun

/-- Identical independent fresh runs, followed by fixed classical processing at
their common final owner. This concrete subclass suffices for upper bounds.
There is one initially pure qubit per run, not per amplified protocol. -/
structure QuantumProtocol (X Y Z : Type) where
  run : QuantumRun X Y Z
  repetitions : ℕ
  output : (Fin repetitions → Bool) → Bool

namespace QuantumProtocol

def WellFormed {X Y Z : Type} (P : QuantumProtocol X Y Z) : Prop :=
  0 < P.repetitions ∧ P.run.WellFormed

/-- Independence is the product of the actual single-run Born probabilities. -/
noncomputable def transcriptProb {X Y Z : Type} (P : QuantumProtocol X Y Z)
    (x : X) (y : Y) (z : Z) (ω : Fin P.repetitions → Bool) : ℝ :=
  ∏ i, P.run.outcomeProb x y z (ω i)

noncomputable def errorProb {X Y Z : Type} (P : QuantumProtocol X Y Z)
    (x : X) (y : Y) (z : Z) (b : Bool) : ℝ :=
  ∑ ω : Fin P.repetitions → Bool,
    if P.output ω = b then 0 else P.transcriptProb x y z ω

/-- Two-sided worst-case promise correctness. Undefined values impose nothing. -/
def Correct {X Y Z : Type} (P : QuantumProtocol X Y Z)
    (f : X → Y → Z → Option Bool) (ε : ℝ) : Prop :=
  ∀ x y z b, f x y z = some b → P.errorProb x y z b ≤ ε

def cost {X Y Z : Type} (P : QuantumProtocol X Y Z) : ℕ :=
  P.repetitions * P.run.cost

end QuantumProtocol

end InterleavedUnitaryNOF.LowerBound.Supplement


