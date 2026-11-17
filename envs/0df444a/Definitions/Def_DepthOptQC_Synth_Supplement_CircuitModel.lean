-- Prove2me | Definitions.Def_DepthOptQC_Synth_Supplement_CircuitModel
-- name    : DepthOptQC_Synth_Supplement_CircuitModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:44:48.257288+00:00
-- url     : https://prove2.me/theorems/761a7fa8-7e87-4632-9e01-32b7ed009a55
-- title:
--   Standard, universal and real shallow quantum circuit models
-- statement:
--   This definition bundle gives the circuit models used in Theorems 9–15. A gate is applied to an injective tuple of wires; a layer consists of applications with pairwise disjoint supports; depth is the number of layers and size is the number of gate occurrences.
--
--   The standard hierarchy permits arbitrary one-qubit unitaries, the universal hierarchy restricts them to $\{H,T,X\}$, and the real hierarchy restricts them to $\{H,X\}$. Their bounded-Toffoli, generalized-Toffoli and Threshold levels, with optional Fan-Out, define QNC/QAC/QTC and their universal and real variants. A decision circuit starts on $|x\rangle|0^a\rangle$, has one designated output, and records its outcome-one probability.
--
--   The bundle also defines clean approximation of an arbitrary-width unitary with fresh zero ancillas and one input-independent phase, the output channel obtained after discarding every register except a designated qubit, the worst-case $R_z$ synthesis depth in the extended reals, and the actual Hadamard/phase decomposition counts used by Theorem 11, with the fivefold depth and size bounds supplied by the paper's Euler expansion.
--
--   **Formalization Note** Data wires precede clean ancillas, a fixed relabelling of the paper's tensor order. The output-channel distance is the unhalved diamond norm. `rotationDepth` is $+\infty$ if no finite depth succeeds.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §§1.1, 4, 7.2–7.3, pp.4–5, 28, 43–49 (PDF pp.6–7, 30, 45–51), Definitions 1–3 and Eqs. (1), (3)–(5), (118)–(120), (203), (215)

import Mathlib
import Definitions.Def_DepthOptQC_Synth_LayeredCircuit
import Definitions.Def_DepthOptQC_Synth_rzQ
import Definitions.Def_DepthOptQC_Synth_gToffoli
import Definitions.Def_DepthOptQC_Synth_fanOut
import Definitions.Def_DepthOptQC_Synth_precLog
import Definitions.Def_QAlgorithms_Defs_CircuitResources
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71

set_option autoImplicit false

noncomputable section

namespace DepthOptQC.Synth.Supplement

open QAlgorithms DepthOptQC.Synth
open scoped Matrix.Norms.L2Operator

/-- The standard hierarchy's arbitrary one-qubit gates (§1.1, p.5). -/
def arbitraryOneQubitGates : Set Gate :=
  {g | ∃ U : Matrix Bool Bool ℂ, U ∈ Matrix.unitaryGroup Bool ℂ ∧ g = Gate.ofMatrix1 U}

/-- The threshold gate of Eq. (4), with `k` controls and threshold `u`. -/
def thresholdGate (k u : ℕ) : Gate :=
  ⟨k + 1, Matrix.of fun y z =>
    if y = Function.update z (Fin.last k)
        (xor (z (Fin.last k)) (decide (u ≤ (Finset.univ.filter fun i : Fin k => z i.castSucc).card)))
    then 1 else 0⟩

/-- Bounded Toffoli primitives: `X`, CNOT and ordinary three-qubit Toffoli. -/
def boundedToffoliGates : Set Gate := {g | ∃ k ≤ 2, g = gToffoli k}

/-- Generalized Toffoli primitives of arbitrary finite width. -/
def generalizedToffoliGates : Set Gate := {g | ∃ k, g = gToffoli k}

/-- Threshold primitives of arbitrary finite width and a valid threshold. -/
def thresholdGates : Set Gate :=
  {g | ∃ k u, 1 ≤ u ∧ u ≤ k ∧ g = thresholdGate k u}

/-- Fan-Out primitives with at least one target. -/
def fanOutGates : Set Gate := {g | ∃ k, 1 ≤ k ∧ g = fanOut k}

/-- The fixed universal one-qubit basis `{H,T,X}` of Definition 2. -/
def universalOneQubitGates : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 gateT, Gate.ofMatrix1 pauliX}

/-- The real one-qubit basis `{H,X}` of Definition 3. -/
def realOneQubitGates : Set Gate := {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 pauliX}

def qncGateSet : Set Gate := arbitraryOneQubitGates ∪ boundedToffoliGates
def qncfGateSet : Set Gate := qncGateSet ∪ fanOutGates
def qacGateSet : Set Gate := arbitraryOneQubitGates ∪ generalizedToffoliGates
def qacfGateSet : Set Gate := qacGateSet ∪ fanOutGates
def qtcGateSet : Set Gate := arbitraryOneQubitGates ∪ thresholdGates
def qtcfGateSet : Set Gate := qtcGateSet ∪ fanOutGates

def quncGateSet : Set Gate := universalOneQubitGates ∪ boundedToffoliGates
def quncfGateSet : Set Gate := quncGateSet ∪ fanOutGates
def quacGateSet : Set Gate := universalOneQubitGates ∪ generalizedToffoliGates
def quacfGateSet : Set Gate := quacGateSet ∪ fanOutGates
def qutcGateSet : Set Gate := universalOneQubitGates ∪ thresholdGates
def qutcfGateSet : Set Gate := qutcGateSet ∪ fanOutGates

def qrncGateSet : Set Gate := realOneQubitGates ∪ boundedToffoliGates
def qrncfGateSet : Set Gate := qrncGateSet ∪ fanOutGates
def qracGateSet : Set Gate := realOneQubitGates ∪ generalizedToffoliGates
def qracfGateSet : Set Gate := qracGateSet ∪ fanOutGates
def qrtcGateSet : Set Gate := realOneQubitGates ∪ thresholdGates
def qrtcfGateSet : Set Gate := qrtcGateSet ∪ fanOutGates

/-- The four wide-gate models in Theorems 12 and 15. -/
inductive WideModel where | ac | acf | tc | tcf deriving DecidableEq

def standardWideGateSet : WideModel → Set Gate
  | .ac => qacGateSet | .acf => qacfGateSet | .tc => qtcGateSet | .tcf => qtcfGateSet

def universalWideGateSet : WideModel → Set Gate
  | .ac => quacGateSet | .acf => quacfGateSet | .tc => qutcGateSet | .tcf => qutcfGateSet

def realWideGateSet : WideModel → Set Gate
  | .ac => qracGateSet | .acf => qracfGateSet | .tc => qrtcGateSet | .tcf => qrtcfGateSet

/-- A decision circuit on `n` classical input bits, with fresh zero workspace and a designated
output qubit (§1.1, Eq. (1), p.4). -/
structure DecisionCircuit (S : Set Gate) (n : ℕ) where
  workspace : ℕ
  circuit : LayeredCircuit S (n + workspace)
  output : Fin (n + workspace)

def DecisionCircuit.depth {S : Set Gate} {n : ℕ} (C : DecisionCircuit S n) : ℕ := C.circuit.depth
def DecisionCircuit.size {S : Set Gate} {n : ℕ} (C : DecisionCircuit S n) : ℕ := C.circuit.size
def DecisionCircuit.width {S : Set Gate} {n : ℕ} (C : DecisionCircuit S n) : ℕ := n + C.workspace

/-- The probability of outcome one on the designated output, Eq. (1). -/
def DecisionCircuit.acceptance {S : Set Gate} {n : ℕ} (C : DecisionCircuit S n)
    (x : Qubits n) : ℝ :=
  probEvent (act C.circuit.unitary (inputState x C.workspace)) (fun z => z C.output)

/-- Clean approximation of an arbitrary `m`-qubit operator with one input-independent phase.
The implementation workspace is appended after the `m` data wires. -/
def CleanlyApproximatesCircuit {m A : ℕ}
    (M : Matrix (Qubits (m + A)) (Qubits (m + A)) ℂ)
    (U : Matrix (Qubits m) (Qubits m) ℂ) (ε : ℝ) : Prop :=
  ∃ φ : ℝ, ∀ ψ : EuclideanSpace ℂ (Qubits m),
    ‖act M (zeroAncillaVec ψ A) -
        Complex.exp (φ * Complex.I) • zeroAncillaVec (act U ψ) A‖ ≤ ε * ‖ψ‖

/-- A circuit with one data input, arbitrary clean ancillas and a designated output. All registers
other than the output are discarded in `outputChannel` (Eq. (118), p.28). -/
structure OutputCircuit (G : Set Gate) where
  ancillas : ℕ
  circuit : LayeredCircuit G (1 + ancillas)
  output : Fin (1 + ancillas)

/-- The output channel induced by `C`, written entrywise as the partial trace over every wire other
than `C.output`. -/
def outputChannel {G : Set Gate} (C : OutputCircuit G) : Superop (Qubits 1) (Qubits 1) :=
  fun ρ o o' =>
    ∑ i : Qubits 1, ∑ j : Qubits 1, ρ i j *
      ∑ y : Qubits (1 + C.ancillas), ∑ z : Qubits (1 + C.ancillas),
        if y C.output = o 0 ∧ z C.output = o' 0 ∧
            (∀ q, q ≠ C.output → y q = z q) then
          C.circuit.unitary y (Fin.append i fun _ => false) *
            star (C.circuit.unitary z (Fin.append j fun _ => false))
        else 0

/-- The `Rz(θ)` conjugation channel of Eq. (119). -/
def rzChannel (θ : ℝ) : Superop (Qubits 1) (Qubits 1) := conjSuperop (rzQ θ)

/-- The unhalved diamond distance used in Theorem 9. -/
def channelDiamondDistance (E F : Superop (Qubits 1) (Qubits 1)) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P71.diamond (fun X => E X - F X)

/-- The minimum depth `D_ε` from Eq. (120), valued in `EReal` so that the infimum of the empty
set is `+∞`, exactly as stipulated by the paper. -/
def rotationDepth (G : Set Gate) (ε : ℝ) : EReal :=
  sInf {D : EReal | ∃ d : ℕ, D = d ∧ ∀ θ : ℝ, θ ∈ Set.Ico 0 (2 * Real.pi) →
    ∃ C : OutputCircuit G, C.circuit.depth ≤ d ∧
      channelDiamondDistance (outputChannel C) (rzChannel θ) ≤ ε}

/-- A phase gate `P(θ)=diag(1,e^{iθ})`, used to record the decomposition preceding Theorem 11. -/
def phaseGate (θ : ℝ) : Gate :=
  Gate.ofMatrix1 (Matrix.diagonal fun b => if b then Complex.exp (θ * Complex.I) else 1)

/-- The intermediate gate alphabet after decomposing the one-qubit gates of a QNCf circuit into
Hadamards and phase gates. -/
def phaseDecompositionGateSet : Set Gate :=
  {Gate.ofMatrix1 hadamard} ∪ {g | ∃ θ, g = phaseGate θ} ∪ boundedToffoliGates ∪ fanOutGates

def IsPhaseGate (g : Gate) : Prop := ∃ θ, g = phaseGate θ

def phaseCount {n : ℕ} (C : LayeredCircuit phaseDecompositionGateSet n) : ℕ :=
  (C.map fun L => L.gates.countP fun a => @decide (IsPhaseGate a.gate) (Classical.propDecidable _)).sum

def maxPhaseLayer {n : ℕ} (C : LayeredCircuit phaseDecompositionGateSet n) : ℕ :=
  (C.map fun L => L.gates.countP fun a => @decide (IsPhaseGate a.gate) (Classical.propDecidable _)).foldl max 0

/-- The decomposition named in Theorem 11. The numbers `r` and `w` are computed from an actual
Hadamard/phase circuit rather than supplied as unrelated parameters.  The fivefold depth and size
bounds are those of the paper's gate-by-gate Euler decomposition: each arbitrary one-qubit gate is
replaced, up to phase, by three phase gates and two Hadamards. -/
def IsPhaseDecomposition {n : ℕ} (C : LayeredCircuit qncfGateSet n) (r w : ℕ) : Prop :=
  ∃ P : LayeredCircuit phaseDecompositionGateSet n, ∃ φ : ℝ,
    P.unitary = Complex.exp (φ * Complex.I) • C.unitary ∧
      P.depth ≤ 5 * C.depth ∧ P.size ≤ 5 * C.size ∧
      r = phaseCount P ∧ w = maxPhaseLayer P

/-- The positive precision scale used to state uniform logarithmic resource bounds. -/
def loglogScale (x : ℝ) : ℝ := 1 + Real.logb 2 (Real.logb 2 x)

end DepthOptQC.Synth.Supplement


