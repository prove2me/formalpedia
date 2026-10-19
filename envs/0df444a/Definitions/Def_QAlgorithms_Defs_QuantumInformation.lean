-- Prove2me | Definitions.Def_QAlgorithms_Defs_QuantumInformation
-- name    : QAlgorithms_Defs_QuantumInformation
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:44:21.964751+00:00
-- url     : https://prove2.me/theorems/d7724374-056a-4b6c-981e-c751394dbaee
-- title:
--   Fidelity, the pretty good measurement for mixed ensembles, mutual information, two-party qubit
-- statement:
--   # Fidelity, the pretty good measurement for mixed ensembles, mutual information, two-party qubit
--   protocols (shared definition layer)
--
--   * H. Barnum, E. Knill, *Reversing quantum dynamics with near-optimal quantum and classical
--     fidelity* (arXiv:quant-ph/0004088v2), cited "Barnum–Knill p.N" (PDF pages), §§V–VI.
--   * R. Cleve, W. van Dam, M. Nielsen, A. Tapp, *Quantum entanglement and the communication
--     complexity of the inner product function* (arXiv:quant-ph/9708019v3), cited "CDNT p.N",
--     Appendix (Theorem 2 and its proof).
--
--   Matrix square roots of Hermitian matrices are Mathlib's continuous functional calculus `cfc`
--   applied to `Real.sqrt` (on positive semidefinite matrices this is the PSD square root).
--   -/
--
--   namespace QAlgorithms
--
--   /-- The Bures–Uhlmann fidelity `F_BU(σ₁, σ₂) = tr √(σ₁^{1/2} σ₂ σ₁^{1/2})` (Barnum–Knill p.11,
--   §VI, before Theorem 5; the root fidelity, not squared). Same object as `ShiQuantum.fidelity` in
--   `qip/src/Quantum/Fidelity.lean`, with square roots via `cfc Real.sqrt` (equal to `CFC.sqrt` on the
--   positive semidefinite arguments the statements use).
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\QuantumInformation.lean

import Definitions.Def_QAlgorithms_Defs_AdaptiveQuery
/-!
# Fidelity, the pretty good measurement for mixed ensembles, mutual information, two-party qubit
protocols (shared definition layer)

* H. Barnum, E. Knill, *Reversing quantum dynamics with near-optimal quantum and classical
  fidelity* (arXiv:quant-ph/0004088v2), cited "Barnum–Knill p.N" (PDF pages), §§V–VI.
* R. Cleve, W. van Dam, M. Nielsen, A. Tapp, *Quantum entanglement and the communication
  complexity of the inner product function* (arXiv:quant-ph/9708019v3), cited "CDNT p.N",
  Appendix (Theorem 2 and its proof).

Matrix square roots of Hermitian matrices are Mathlib's continuous functional calculus `cfc`
applied to `Real.sqrt` (on positive semidefinite matrices this is the PSD square root).
-/

namespace QAlgorithms

/-- The Bures–Uhlmann fidelity `F_BU(σ₁, σ₂) = tr √(σ₁^{1/2} σ₂ σ₁^{1/2})` (Barnum–Knill p.11,
§VI, before Theorem 5; the root fidelity, not squared). Same object as `ShiQuantum.fidelity` in
`qip/src/Quantum/Fidelity.lean`, with square roots via `cfc Real.sqrt` (equal to `CFC.sqrt` on the
positive semidefinite arguments the statements use). -/
noncomputable def rootFidelity {ι : Type*} [Fintype ι] [DecidableEq ι] (σ1 σ2 : Matrix ι ι ℂ) : ℝ :=
  (cfc Real.sqrt (cfc Real.sqrt σ1 * σ2 * cfc Real.sqrt σ1)).trace.re

/-- Barnum–Knill eqs. (37)–(38) (pp.10–11): the success probability of the pretty good
measurement for the ensemble `{p_j, ρ̂_j}`: with `ρ_j = p_j ρ̂_j` and `ρ_out = Σ_j ρ_j`,
`Σ_j tr(ρ_out^{−1/2} ρ_j ρ_out^{−1/2} ρ_j)`. `ρ_out^{−1/2}` is the generalized inverse square
root (non-zero eigenvalues inverted, zero eigenvalues kept: `(√0)⁻¹ = 0` in Lean). -/
noncomputable def mixedPgmSuccess {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    (p : O → ℝ) (ρh : O → Matrix ι ι ℂ) : ℝ :=
  let ρout : Matrix ι ι ℂ := ∑ j, (p j : ℂ) • ρh j
  let S : Matrix ι ι ℂ := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρout
  ∑ j, (S * ((p j : ℂ) • ρh j) * S * ((p j : ℂ) • ρh j)).trace.re

/-- Barnum–Knill eq. (10) (p.5) and §VI (p.11): the optimal success probability `F_cl` of
identifying the label `j` of `ρ̂_j`, drawn with probability `p_j`, over all POVMs whose outcomes are
the labels. Real `⨆`: the statements supply a nonempty label set, a probability vector and density
matrices, under which the set is nonempty and bounded by `1`. -/
noncomputable def mixedOptSuccess {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    (p : O → ℝ) (ρh : O → Matrix ι ι ℂ) : ℝ :=
  ⨆ M : {M : O → Matrix ι ι ℂ // IsPOVM M}, ∑ j, p j * effectProb (M.1 j) (ρh j)

/-- The Shannon mutual information `I(X : Y)` in bits of a finite joint distribution `P` (CDNT
p.13, proof of Theorem 2): `Σ_{a,b} P(a,b) log₂(P(a,b) / (P_X(a) P_Y(b)))`, terms with
`P(a,b) = 0` contributing `0`. -/
noncomputable def mutualInfoBits {α β : Type*} [Fintype α] [Fintype β] (P : α × β → ℝ) : ℝ :=
  ∑ a, ∑ b, P (a, b) * Real.logb 2 (P (a, b) / ((∑ b', P (a, b')) * (∑ a', P (a', b))))

/-- The owner of a qubit in a two-party protocol (CDNT p.13). -/
inductive Party where
  | alice
  | bob
  deriving DecidableEq

/-- The other party. -/
def Party.other : Party → Party
  | .alice => .bob
  | .bob => .alice

/-- One step of a two-party qubit protocol on `N` wires (CDNT p.13, proof of Theorem 2, steps
1–4; p.4, §2.1): party `p` applies a unitary `U` to the wires `w` (identity elsewhere), or party
`p` sends qubit `q` to the other party. -/
inductive CommStep (N : ℕ) where
  | unitary (p : Party) (k : ℕ) (w : Fin k ↪ Fin N) (U : Matrix.unitaryGroup (Qubits k) ℂ)
  | send (p : Party) (q : Fin N)

/-- The wire ownership after a step (CDNT p.13): a send moves the qubit to the other party. -/
def CommStep.updateOwner {N : ℕ} (s : CommStep N) (own : Fin N → Party) : Fin N → Party :=
  match s with
  | .unitary _ _ _ _ => own
  | .send p q => Function.update own q p.other

/-- A step is legal for the current ownership (CDNT p.13): a party applies unitaries only to qubits
in its possession and sends only a qubit it possesses. -/
def CommStep.ValidFor {N : ℕ} (s : CommStep N) (own : Fin N → Party) : Prop :=
  match s with
  | .unitary p _ w _ => ∀ i, own (w i) = p
  | .send p q => own q = p

/-- Legality of a whole step list from an initial ownership (CDNT p.13). -/
def CommStep.StepsValid {N : ℕ} : (Fin N → Party) → List (CommStep N) → Prop
  | _, [] => True
  | own, s :: l => s.ValidFor own ∧ CommStep.StepsValid (s.updateOwner own) l

/-- A qubit protocol for Alice's `n`-bit input (CDNT p.13, proof of Theorem 2; p.4, §2.1; p.12,
Theorem 2): `N` wires; Alice's input wires `inp` hold `|x⟩`; the shared wires `sh` hold a prior
entangled state `Φ` independent of `x` (`e = 0`: no prior entanglement); all other wires start in
`|0⟩`; the step list is fixed independently of `x`. -/
structure TwoPartyProtocol (n : ℕ) where
  /-- Number of wires. -/
  N : ℕ
  /-- Number of wires of the prior shared state. -/
  e : ℕ
  /-- Alice's input wires. -/
  inp : Fin n ↪ Fin N
  /-- The wires of the prior shared state. -/
  sh : Fin e ↪ Fin N
  /-- The prior shared state. -/
  Φ : EuclideanSpace ℂ (Qubits e)
  /-- The initial owner of each wire. -/
  own0 : Fin N → Party
  /-- The steps. -/
  steps : List (CommStep N)

namespace TwoPartyProtocol

variable {n : ℕ} (P : TwoPartyProtocol n)

/-- The ownership after the steps `l` from the ownership `own` (CDNT p.13). -/
def ownerAfter {N : ℕ} (own : Fin N → Party) (l : List (CommStep N)) : Fin N → Party :=
  l.foldl (fun o s => s.updateOwner o) own

/-- The final ownership of the wires (CDNT p.13: Bob measures the qubits in his possession after
the steps). -/
def finalOwner : Fin P.N → Party :=
  ownerAfter P.own0 P.steps

/-- Validity of a protocol (CDNT p.13): `Φ` is a unit vector, the input and shared wires are
disjoint, Alice owns her input wires initially, and every step is legal. -/
def IsValid : Prop :=
  ‖P.Φ‖ = 1 ∧ Disjoint (Set.range P.inp) (Set.range P.sh) ∧ (∀ i, P.own0 (P.inp i) = .alice) ∧
    CommStep.StepsValid P.own0 P.steps

/-- The initial state (CDNT p.13; p.4, §2.1): `|x⟩` on the input wires, `Φ` on the shared wires,
`|0⟩` on all other wires. -/
noncomputable def initState (x : Qubits n) : EuclideanSpace ℂ (Qubits P.N) :=
  open Classical in
  WithLp.toLp 2 fun z =>
    if (∀ q, q ∉ Set.range P.inp → q ∉ Set.range P.sh → z q = false) ∧ z ∘ P.inp = x then
      P.Φ (z ∘ P.sh)
    else 0

/-- The joint state after all steps (CDNT p.13): unitaries act on their wires; sending a qubit
changes its owner, not the state. -/
noncomputable def finalState (x : Qubits n) : EuclideanSpace ℂ (Qubits P.N) :=
  P.steps.foldl (fun ψ s => match s with
    | .unitary _ _ w U => act (embedOp (U : Matrix _ _ ℂ) w) ψ
    | .send _ _ => ψ) (P.initState x)

/-- `n_AB`, the number of qubits Alice sends to Bob (CDNT p.12, Theorem 2). -/
def nAB : ℕ :=
  P.steps.countP fun s => match s with
    | .send .alice _ => true
    | _ => false

/-- `n_BA`, the number of qubits Bob sends to Alice (CDNT p.12, Theorem 2). -/
def nBA : ℕ :=
  P.steps.countP fun s => match s with
    | .send .bob _ => true
    | _ => false

/-- A measurement by Bob on the qubits he holds at the end (CDNT p.13): a POVM whose effects act
only on Bob's final wires (`M_y ⊗ I_Alice`). -/
def IsBobMeasurement {Y : Type*} [Fintype Y] (M : Y → Matrix (Qubits P.N) (Qubits P.N) ℂ) : Prop :=
  IsPOVM M ∧ ∀ y, ActsWithin (Finset.univ.filter fun q => P.finalOwner q = .bob) (M y)

/-- `p(y | x)`, the probability that Bob's measurement `M` yields `y` on Alice's input `x`
(CDNT p.13). -/
noncomputable def outcomeProb {Y : Type*} [Fintype Y] (M : Y → Matrix (Qubits P.N) (Qubits P.N) ℂ)
    (x : Qubits n) (y : Y) : ℝ :=
  effectProb (M y) (pureDensity (P.finalState x))

/-- `I(X : Y)` in bits, `X` uniform on `{0,1}^n` (CDNT p.13, proof of Theorem 2) and `Y` the
outcome of Bob's measurement `M`. -/
noncomputable def mutualInfo {Y : Type*} [Fintype Y] (M : Y → Matrix (Qubits P.N) (Qubits P.N) ℂ) :
    ℝ :=
  mutualInfoBits fun xy : Qubits n × Y => ((2 : ℝ) ^ n)⁻¹ * P.outcomeProb M xy.1 xy.2

end TwoPartyProtocol

/-! ### Sanity tests -/

example {ι : Type*} [Fintype ι] [DecidableEq ι] : rootFidelity (1 : Matrix ι ι ℂ) 1 = Fintype.card ι := by
  simp [rootFidelity, cfc_one]

example : Party.alice.other = .bob ∧ Party.bob.other = .alice := ⟨rfl, rfl⟩

example (P : TwoPartyProtocol 0) (h : P.steps = []) (x : Qubits 0) :
    P.finalState x = P.initState x := by
  simp [TwoPartyProtocol.finalState, h]

example {N : ℕ} (q : Fin N) (own : Fin N → Party) :
    (CommStep.send .alice q).updateOwner own q = .bob := by
  simp [CommStep.updateOwner, Party.other]

example (P : TwoPartyProtocol 1) (q : Fin P.N) (h : P.steps = [.send .alice q, .send .bob q]) :
    P.nAB = 1 ∧ P.nBA = 1 := by
  simp [TwoPartyProtocol.nAB, TwoPartyProtocol.nBA, h]

example {α β : Type*} [Fintype α] [Fintype β] : mutualInfoBits (fun _ : α × β => (0 : ℝ)) = 0 := by
  simp [mutualInfoBits]

end QAlgorithms


