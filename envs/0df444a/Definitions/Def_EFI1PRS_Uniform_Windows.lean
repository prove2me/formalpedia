-- Prove2me | Definitions.Def_EFI1PRS_Uniform_Windows
-- name    : EFI1PRS_Uniform_Windows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:41:58.952192+00:00
-- url     : https://prove2.me/theorems/383a4c40-23d3-4892-9a7a-0373bfd3aaa1
-- title:
--   Random-start windows and independent rows grouped into columns
-- statement:
--   Set $L=4M$, $N=M(L-1)$, $t=2^{16}M^2(\lambda+4)$ and $\ell=t/2+3t/(4M)$. Natural quotients denote these exact integral values; their divisibility and positivity must be proved from the parameters. A row is the product of $L$ independent copies of $\tau$. A uniformly sampled public shift $J\in\{0,\ldots,M-1\}$ selects the $N$-qubit window starting at $J+1$.
--
--   The actual prefix $\omega_i$ retains $J$ and the first $i$ window qubits. In $\Omega_i$ only the current copy is replaced by its local witness; preceding factors are actual marginals and the first truncated tail is retained. Repetition uses $t$ independent rows and shifts. The explicit permutation groups all shifts first and then columns. The min-entropy representation puts the current column first and the whole original past second. No estimate is part of the construction data.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, §4, pp.11–12

import Definitions.Def_EFI1PRS_Uniform_Source

/-! Batra, §4, pp.11–12. Exact parameters, the actual shifted prefix, its
current-copy witness, and independent rows regrouped into columns. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

def copies (M : ℕ) : ℕ := 4*M
def windowLength (M : ℕ) : ℕ := M*(copies M-1)
def rows (M sec : ℕ) : ℕ := 2^16 * M^2 * (sec+4)
/-- Divisibility is a proof obligation of these exact source parameters. -/
def retained (M sec : ℕ) : ℕ := rows M sec / 2 + 3 * rows M sec / (4*M)
def shiftBits (M : ℕ) : ℕ := Nat.log2 M

def natBits (q j : ℕ) : Qubits q := fun k => Nat.testBit j (q-1-k.val)

def rowDensity (g : PairPreparation) (sec : ℕ) :
    Matrix (Qubits (sourceWidth g sec * copies (sourceWidth g sec)))
      (Qubits (sourceWidth g sec * copies (sourceWidth g sec))) ℂ :=
  fun x y => ∏ c : Fin (copies (sourceWidth g sec)),
    tau g sec (fun j => bitAt x (c.val * sourceWidth g sec + j.val))
      (fun j => bitAt y (c.val * sourceWidth g sec + j.val))

def omega (g : PairPreparation) (sec i : ℕ) :
    Matrix (Qubits (shiftBits (sourceWidth g sec)+i))
      (Qubits (shiftBits (sourceWidth g sec)+i)) ℂ :=
  ((sourceWidth g sec : ℂ))⁻¹ • ∑ J : Fin (sourceWidth g sec),
    tensorQubits (pureDensity (ket (natBits (shiftBits (sourceWidth g sec)) J.val)))
      (interval (rowDensity g sec) J.val i)

def currentCopy (M i J : ℕ) : ℕ := (J+i-1)/M
def currentCoordinate (M i J : ℕ) : ℕ := (J+i-1)%M+1

/-- Every preceding factor is the actual source marginal. Only the current
copy uses gamma. Copies after it contribute the scalar tensor unit. -/
def witnessAtShift (g : PairPreparation) (sec i J : ℕ) :
    Matrix (Qubits i) (Qubits i) ℂ :=
  let M := sourceWidth g sec
  let k := currentCopy M i J
  let j := currentCoordinate M i J
  fun x y => ∏ c : Fin (copies M),
    let start := if c.val = 0 then J else 0
    let stop := min M (J+i-c.val*M)
    let factor := if c.val = k then interval (gamma g sec j) start (stop-start)
      else interval (tau g sec) start (stop-start)
    factor (fun h => bitAt x (c.val*M+start+h.val-J))
      (fun h => bitAt y (c.val*M+start+h.val-J))

def bigOmega (g : PairPreparation) (sec i : ℕ) :
    Matrix (Qubits (shiftBits (sourceWidth g sec)+i))
      (Qubits (shiftBits (sourceWidth g sec)+i)) ℂ :=
  if h : 0 = i then h ▸ omega g sec 0 else
    ((sourceWidth g sec : ℂ))⁻¹ • ∑ J : Fin (sourceWidth g sec),
      tensorQubits (pureDensity (ket (natBits (shiftBits (sourceWidth g sec)) J.val)))
        (witnessAtShift g sec i J.val)

/-- New wire order is J^t,C1,...,Ci. Original row r reads its own shift bits,
then its r-th qubit from every column. All t shifts are independent. -/
def groupedPower (q i t : ℕ)
    (ζ : Matrix (Qubits (q+i)) (Qubits (q+i)) ℂ) :
    Matrix (Qubits (t*q+i*t)) (Qubits (t*q+i*t)) ℂ :=
  fun x y => ∏ r : Fin t,
    ζ (fun j => bitAt x (if j.val < q then r.val*q+j.val else t*q+(j.val-q)*t+r.val))
      (fun j => bitAt y (if j.val < q then r.val*q+j.val else t*q+(j.val-q)*t+r.val))

def actualColumns (g : PairPreparation) (sec i : ℕ) :=
  groupedPower (shiftBits (sourceWidth g sec)) i (rows (sourceWidth g sec) sec) (omega g sec i)

def witnessColumns (g : PairPreparation) (sec i : ℕ) :=
  groupedPower (shiftBits (sourceWidth g sec)) i (rows (sourceWidth g sec) sec) (bigOmega g sec i)

/-- Put the current column first and its complete quantum past second for the
conditional entropy convention. This is the row-to-column permutation, not a trace. -/
def columnAndPast (g : PairPreparation) (sec i : ℕ) :
    Matrix (Qubits (rows (sourceWidth g sec) sec) ×
      Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec) +
        (i-1)*rows (sourceWidth g sec) sec))
      (Qubits (rows (sourceWidth g sec) sec) ×
      Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec) +
        (i-1)*rows (sourceWidth g sec) sec)) ℂ :=
  let past := rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec) +
    (i-1)*rows (sourceWidth g sec) sec
  fun x y => witnessColumns g sec i
    (fun j => if j.val < past then bitAt x.2 j.val else bitAt x.1 (j.val-past))
    (fun j => if j.val < past then bitAt y.2 j.val else bitAt y.1 (j.val-past))

end EFI1PRS.Uniform


