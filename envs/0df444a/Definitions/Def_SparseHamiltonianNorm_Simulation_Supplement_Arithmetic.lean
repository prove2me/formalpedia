-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_Supplement_Arithmetic
-- name    : SparseHamiltonianNorm_Simulation_Supplement_Arithmetic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:29:49.093528+00:00
-- url     : https://prove2.me/theorems/25d47abe-08bc-4b8f-8676-52aeba6d4eb9
-- title:
--   Fixed-point arithmetic library and circuit resource parameters
-- statement:
--   The public rational parameters are stored by reduced numerator and denominator, with one sign bit and the larger of their binary lengths. The bound $b_{\rm val}$ covers each public parameter and the published complex value-register width. With $Q_{\rm sim}$ equal to the published simulation scale, define
--   $$X=\lceil\log_2 N\rceil+b_{\rm val}+\log d+\log(2Q_{\rm sim}/\varepsilon).$$
--
--   A library with constants $c_A,k_A$, working length $W$, and workspace bound $a_{\rm ar}$ supplies reversible circuits for addition, subtraction, multiplication, division, comparison, square root, exponential, sine, cosine, and complex argument. Input words use the published signed-magnitude decoder, with a separately specified binary point. Two input words are preserved and a result word is XORed into an output register. Comparison is exact. The other results have additive error at most $2^{-P}$. Division requires a nonzero divisor, square root a nonnegative input, and argument a nonzero complex input. Accuracy applies when the exact result fits the caller-selected output format; overflow behavior is unspecified. All formats, including sign bits, enter the aggregate word length $w\le W$, and the binary-point parameters satisfy the stated working bounds.
--
--   Each numerical circuit has at most $c_A(w+P+1)^{k_A}$ one- and two-qubit gates. It uses at most $a_{\rm ar}$ additional qubits, returned exactly to zero coherently. The library also supplies coherent angle-word-controlled rotations about the $Y$ and $Z$ axes, within operator-norm $2^{-P}$, with the same polynomial size convention and clean workspace. There is no state-preparation, Fourier-transform, table-access, or Hamiltonian-dependent primitive. Uniformity is omitted, so this predicate also covers nonuniform libraries with the stated costs. The arithmetic interface records the gate-model assumption; it does not assert any simulation or finite-coupling approximation.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Gate-model assumptions preceding Theorem 3; Eq. (138), p.4 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_SparseAccess

noncomputable section

namespace SparseHamiltonianNorm.Simulation.Supplement
open QAlgorithms
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Binary lengths of a reduced rational numerator and denominator, with a sign bit. -/
def rationalBits (x : ℚ) : ℕ :=
  1 + max (Nat.clog 2 (x.num.natAbs + 1)) (Nat.clog 2 (x.den + 1))

/-- The full argument X in Eqs. (15)--(16), natural logarithms. -/
def resourceArgument (N d bval : ℕ) (t Λ Λmax ε : ℝ) : ℝ :=
  addressBits N + bval + Real.log d +
    Real.log (2 * simulationScale d t Λ Λmax ε / ε)

/-- All four public rationals and the value register fit in bval bits. -/
def ParametersFit (bval k : ℕ) (t Λ Λmax ε : ℚ) : Prop :=
  valueBits k ≤ bval ∧ rationalBits t ≤ bval ∧ rationalBits Λ ≤ bval ∧
    rationalBits Λmax ≤ bval ∧ rationalBits ε ≤ bval

/-- Explicit list of the arithmetic primitives assumed on p.4; no QFT, clock,
state-preparation or Hamiltonian-dependent primitive is included. -/
inductive ArithmeticOp where
  | add | sub | mul | div | lt | sqrt | exp | sin | cos | arg
  deriving DecidableEq

def ArithmeticOp.eval (op : ArithmeticOp) (x y : ℝ) : ℝ :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y
  | .div => x / y
  | .lt => if x < y then 1 else 0
  | .sqrt => Real.sqrt x
  | .exp => Real.exp x
  | .sin => Real.sin x
  | .cos => Real.cos x
  | .arg => Complex.arg ((x : ℂ) + Complex.I * y)

def ArithmeticOp.valid (op : ArithmeticOp) (x y : ℝ) : Prop :=
  match op with
  | .div => y ≠ 0
  | .sqrt => 0 ≤ x
  | .arg => x ≠ 0 ∨ y ≠ 0
  | _ => True

/-- Reversible XOR of a numerical result into an arbitrary output register.
The two input words are preserved. -/
def xorResult (k r : ℕ)
    (f : Qubits ((k + 1) + (k + 1)) → Qubits (r + 1)) :
    Matrix (Qubits (((k + 1) + (k + 1)) + (r + 1)))
      (Qubits (((k + 1) + (k + 1)) + (r + 1))) ℂ :=
  Matrix.of fun y z =>
    let zy := qubitsAppendEquiv ((k + 1) + (k + 1)) (r + 1) z
    if y = (qubitsAppendEquiv ((k + 1) + (k + 1)) (r + 1)).symm
      (zy.1, fun j => Bool.xor (zy.2 j) (f zy.1 j)) then 1 else 0

/-- Reusable ancillas are appended, begin and end in zero, on every superposition. -/
def CleanRealization {m : ℕ} (aar budget : ℕ)
    (A : Matrix (Qubits m) (Qubits m) ℂ) : Prop :=
  ∃ a : ℕ, a ≤ aar ∧ ∃ c : Circuit oneTwoQubitGateSet (m + a),
    c.size ≤ budget ∧ ImplementsWithCleanAncillas c.unitary A

/-- Ry(theta) and Rz(theta) = exp(-i theta Y/2), exp(-i theta Z/2). -/
def axisRotation (zAxis : Bool) (θ : ℝ) : Matrix Bool Bool ℂ :=
  if zAxis then
    Matrix.of fun i j => if i = j then
      Complex.exp ((if i then Complex.I else -Complex.I) * (θ / 2 : ℝ)) else 0
  else
    Matrix.of fun i j => if i = j then (Real.cos (θ / 2) : ℂ)
      else if i then (Real.sin (θ / 2) : ℂ) else -(Real.sin (θ / 2) : ℂ)

/-- A signed angle word controls the target qubit coherently. -/
def wordRotation (k p : ℕ) (zAxis : Bool) :
    Matrix (Qubits ((k + 1) + 1)) (Qubits ((k + 1) + 1)) ℂ :=
  Matrix.of fun y x =>
    let ys := qubitsAppendEquiv (k + 1) 1 y
    let xs := qubitsAppendEquiv (k + 1) 1 x
    if ys.1 = xs.1 then axisRotation zAxis (decodeReal p k xs.1) (ys.2 0) (xs.2 0)
    else 0

/-- Operational fixed-point library, p.4, needed only up to working length W (p.35).
An arithmetic call uses two (k+1)-bit signed-magnitude words at binary point p
and an (r+1)-bit output at binary point P. The aggregate word length is
2(k+1)+(r+1); p and P also fit the working bound. Numeric accuracy is required
on valid inputs whose exact output fits that output format. On overflow and
undefined inputs its reversible action is unspecified. This is the ordinary
finite-register convention, with caller-selected integer and fractional widths.
Uniformity is not built in: the theorem also covers nonuniform libraries. -/
def ArithmeticLibrary (cA kA W aar : ℕ) : Prop :=
  (∀ (op : ArithmeticOp) (k p r P : ℕ),
    let w := (k + 1) + (k + 1) + (r + 1)
    w ≤ W → p ≤ w → P ≤ w →
    ∃ f : Qubits ((k + 1) + (k + 1)) → Qubits (r + 1),
      (∀ z,
        let xy := qubitsAppendEquiv (k + 1) (k + 1) z
        let x := decodeReal p k xy.1
        let y := decodeReal p k xy.2
        op.valid x y →
        |op.eval x y| ≤ ((2 : ℝ) ^ r - 1) * (2 : ℝ) ^ (-(P : ℤ)) →
        (if op = .lt then decodeReal P r (f z) = op.eval x y
         else |decodeReal P r (f z) - op.eval x y| ≤ (2 : ℝ) ^ (-(P : ℤ)))) ∧
      CleanRealization aar (cA * (w + P + 1) ^ kA) (xorResult k r f)) ∧
  (∀ (k p P : ℕ) (zAxis : Bool),
    k + 2 ≤ W → p ≤ k + 2 → P ≤ W →
    ∃ U : Matrix (Qubits ((k + 1) + 1)) (Qubits ((k + 1) + 1)) ℂ,
      U ∈ Matrix.unitaryGroup _ ℂ ∧
      opNorm (U - wordRotation k p zAxis) ≤ (2 : ℝ) ^ (-(P : ℤ)) ∧
      CleanRealization aar (cA * (k + 2 + P + 1) ^ kA) U)

end SparseHamiltonianNorm.Simulation.Supplement


