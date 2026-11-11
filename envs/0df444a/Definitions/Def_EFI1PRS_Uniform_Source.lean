-- Prove2me | Definitions.Def_EFI1PRS_Uniform_Source
-- name    : EFI1PRS_Uniform_Source
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:33.831061+00:00
-- url     : https://prove2.me/theorems/84b859a9-4e59-4cd7-adbb-e072f37e4896
-- title:
--   Correlated flags, coherent source and separate prefix witnesses
-- statement:
--   Starting from the actual branch preparations, define the correlated flag state $\alpha$, independent-flag state $\beta$, their entropy difference $\chi$, and $\eta=h_2((1-D(\rho_0,\rho_1))/2)$. Coherent preparation retains the branch circuit's entire workspace. Its output wires are reordered as $R,F,E$, followed by zero padding to a power-of-two qubit width $M\ge4$.
--
--   The pure one-bit source is $G(b)=|b\rangle_F|\psi_b\rangle_{RE}|0\rangle_{\rm pad}$ in that explicit wire order. Its average is $\tau$. The witness $\gamma_j$ is the actual $j$-qubit prefix except at the flag, where it is $\beta$. Its conditional entropy is $h_j=S(\gamma_j)-S((\gamma_j)_{<j})$. No entropy bound, exact marginal identity, indistinguishability conclusion, nonnegative conditional entropy or common global witness is assumed in these definitions.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, §3, Eq. (3.1), Lemma 3.1, pp.10–11

import Definitions.Def_EFI1PRS_Uniform_Entropy

/-! Batra, §3, pp.10–11. Actual coherent preparation, explicit R,F,E,pad order,
and separate prefix witnesses. No witness estimate is assumed. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

def bitAt {n : ℕ} (x : Qubits n) (j : ℕ) : Bool :=
  if h : j < n then x ⟨j,h⟩ else false

/-- General finite partial trace on a specified ordered list of wire positions.
Applications below use distinct, in-range positions; outside that domain this is
still an explicit finite sum rather than an unspecified state. -/
def reducePositions {n k : ℕ} (pos : Fin k → ℕ)
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (Qubits k) (Qubits k) ℂ :=
  fun x y => ∑ u : Qubits n, ∑ v : Qubits n,
    if (∀ j, bitAt u (pos j) = x j) ∧ (∀ j, bitAt v (pos j) = y j) ∧
      (∀ j : Fin n, j.val ∉ Set.range pos → u j = v j)
    then ρ u v else 0

def prefixState {n : ℕ} (ρ : Matrix (Qubits n) (Qubits n) ℂ) (j : ℕ) :=
  reducePositions (fun i : Fin j => i.val) ρ

def interval {n : ℕ} (ρ : Matrix (Qubits n) (Qubits n) ℂ) (start len : ℕ) :=
  reducePositions (fun i : Fin len => start + i.val) ρ

def alpha (g : PairPreparation) (sec : ℕ) :=
  (1/2 : ℂ) • (tensorQubits (g.branch false sec) (pureDensity (ket (fun _ : Fin 1 => false))) +
    tensorQubits (g.branch true sec) (pureDensity (ket (fun _ : Fin 1 => true))))

def beta (g : PairPreparation) (sec : ℕ) :=
  tensorQubits ((1/2 : ℂ) • (g.branch false sec + g.branch true sec)) (maximallyMixed 1)

def chi (g : PairPreparation) (sec : ℕ) : ℝ := vnEntropy (beta g sec) - vnEntropy (alpha g sec)

def eta (g : PairPreparation) (sec : ℕ) : ℝ :=
  binaryEntropy ((1 - distance (g.branch false sec) (g.branch true sec))/2)

/-- The original workspace and measured randomness are retained coherently. The
finite-vocabulary circuit itself contains no discarded intermediate wire. -/
def coherentBranch (g : PairPreparation) (sec : ℕ) (b : Bool) :=
  act (g.program sec).circuit.unitary (inputState (fun _ : Fin 1 => b) (g.program sec).work)

/-- First the retained R wires, then the original discarded wires in increasing
order. The independent flag is inserted between these two lists by sourceVector. -/
def sourceWireOrder (g : PairPreparation) (sec : ℕ) : List (Fin (1 + (g.program sec).work)) :=
  List.ofFn (g.program sec).outputs ++
    (List.finRange (1 + (g.program sec).work)).filter
      (fun j => j ∉ Set.range (g.program sec).outputs)

/-- A power-of-two qubit width at least four and large enough for R,F,E. The
source permits any such zero padding, so choosing the next larger power is harmless. -/
def sourceWidth (g : PairPreparation) (sec : ℕ) : ℕ :=
  2 ^ (Nat.log2 (max 4 (2 + (g.program sec).work)) + 1)

def flagPosition (g : PairPreparation) (sec : ℕ) : ℕ := g.width sec + 1

/-- Wire 0 is the first R qubit; the flag has zero-based position width(R).
The remaining active wires carry E, followed by zero padding. -/
def sourceVector (g : PairPreparation) (sec : ℕ) (b : Bool) :
    EuclideanSpace ℂ (Qubits (sourceWidth g sec)) :=
  WithLp.toLp 2 fun z =>
    if bitAt z (g.width sec) = b ∧
      (∀ j : Fin (sourceWidth g sec), 2 + (g.program sec).work ≤ j.val → z j = false)
    then coherentBranch g sec b (fun old =>
      let j := (sourceWireOrder g sec).idxOf old
      bitAt z (if j < g.width sec then j else j+1))
    else 0

def tau (g : PairPreparation) (sec : ℕ) :=
  (1/2 : ℂ) • (pureDensity (sourceVector g sec false) + pureDensity (sourceVector g sec true))

def gamma (g : PairPreparation) (sec j : ℕ) : Matrix (Qubits j) (Qubits j) ℂ :=
  if h : g.width sec + 1 = j then h ▸ beta g sec else prefixState (tau g sec) j

def localEntropy (g : PairPreparation) (sec j : ℕ) : ℝ :=
  vnEntropy (gamma g sec j) - vnEntropy (prefixState (gamma g sec j) (j-1))

end EFI1PRS.Uniform


