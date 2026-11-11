-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_SparseAccess
-- name    : SparseHamiltonianNorm_Simulation_SparseAccess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:32.908011+00:00
-- url     : https://prove2.me/theorems/8039ccfa-be76-4afa-84af-36314837c996
-- title:
--   Sparse access, fixed-point values, and clean-output error
-- statement:
--   Let $H$ be a complex matrix on $\mathbb C^N$. Its column norm is the largest Euclidean norm of a column; its entry norm is the largest entry magnitude. A sparse promise asserts Hermiticity, at most $d$ nonzeros per row, and the public bounds $\Lambda,\Lambda_{\max}$, without a spectral-norm promise.
--
--   A location table consists of full row permutations covering the support in their first $d$ slots. The binary location oracle applies these permutations. The value oracle XORs a finite word into its target register. Both fix unused addresses. A word decodes two signed fixed-point coordinates with step $2^{-p}$ and $k$ magnitude bits each. The public range covers $\Lambda_{\max}$. The error allowance is $\zeta=\sqrt2\,2^{-p}$; for positive time it is at most each of $\Lambda_{\max}/4$, $\Lambda/(4\sqrt d)$, and $\varepsilon/(32td)$. Compatible tables have entry error at most $\zeta$, Hermitian decoded values, and preserve zero entries.
--
--   The clean system embedding $J$ puts all work qubits in zero and uses the minimal binary system register. With $A$ the evaluated circuit, the error predicate is unitarity together with
--   $$\|AJ-J\exp(-itH)\|_{\mathrm{op}}\le\varepsilon.$$
--   The rectangular norm includes leakage and every ancillary output. The syntactic query count includes forward, inverse, and controlled queries. These definitions separate public circuit syntax from hidden oracle evaluation and specify a precision convention without narrowing the original complex matrix.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), pp.2–3, Eqs. (2), (5)–(11); pp.10–11, norm and query conventions; p.6, entry perturbation; p.35, precision budgeting; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Mathlib
import Definitions.Def_QAlgorithms_Defs_CircuitResources
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Defs_SpectralFilter

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace SparseHamiltonianNorm.Simulation
open QAlgorithms
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Euclidean induced norm, also for rectangular maps (source pp.3,10). -/
def opNorm {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℂ) : ℝ := by
  classical
  exact QAlgorithms.specNorm A

/-- The maximum column Euclidean norm, Eq. (2). Empty matrices have value zero. -/
def columnNorm {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (insert 0 (Finset.univ.image fun j => Real.sqrt (∑ i, ‖H i j‖ ^ 2))).max' (by simp)

/-- Maximum entry magnitude, source Eq. (6). -/
def entryNorm {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (insert 0 (Finset.univ.image fun ij : Fin N × Fin N => ‖H ij.1 ij.2‖)).max' (by simp)

/-- Source promises, with no spectral-norm promise. -/
def SparsePromise {N : ℕ} (d : ℕ) (Λ Λmax : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  H.IsHermitian ∧ (∀ i, (Finset.univ.filter fun j => H i j ≠ 0).card ≤ d) ∧
  columnNorm H ≤ Λ ∧ entryNorm H ≤ Λmax

/-- Each row has a permutation; precisely its first d addresses cover the support. -/
def ListsSupport {N : ℕ} (d : ℕ) (H : Matrix (Fin N) (Fin N) ℂ)
    (f : Fin N → Equiv.Perm (Fin N)) : Prop :=
  ∀ i j, H i j ≠ 0 → ∃ l : Fin N, l.val < d ∧ f i l = j

/-- Signed magnitude grid. The first bit is the sign and the rest the magnitude. -/
def decodeReal (p k : ℕ) (w : Qubits (k + 1)) : ℝ :=
  (if w 0 then -1 else 1) * (bitsToNat (Fin.tail w) : ℝ) * (2 : ℝ) ^ (-(p : ℤ))

/-- Public finite complex format: two signed fixed-point coordinates. -/
def decodeValue (p k : ℕ) (w : Qubits ((k + 1) + (k + 1))) : ℂ :=
  let xy := qubitsAppendEquiv (k + 1) (k + 1) w
  (decodeReal p k xy.1 : ℂ) + Complex.I * (decodeReal p k xy.2 : ℂ)

def valueBits (k : ℕ) : ℕ := (k + 1) + (k + 1)
def addressBits (N : ℕ) : ℕ := Nat.clog 2 N

def precisionError (p : ℕ) : ℝ := Real.sqrt 2 * (2 : ℝ) ^ (-(p : ℤ))

/-- Public sufficient precision, including the range needed for the entry bound.
At time zero no accuracy requirement is imposed. -/
def SufficientPrecision (d : ℕ) (t Λ Λmax ε : ℝ) (p k : ℕ) : Prop :=
  Λmax ≤ ((2 : ℝ) ^ k - 1) * (2 : ℝ) ^ (-(p : ℤ)) ∧
  (t = 0 ∨ (precisionError p ≤ Λmax / 4 ∧
    precisionError p ≤ Λ / (4 * Real.sqrt d) ∧
    precisionError p ≤ ε / (32 * t * d)))

/-- Coherent value words approximate the original complex H. Decoded entries are
Hermitian, zero stays zero, and no exact representability of H is imposed. -/
def ValueTableFor {N : ℕ} (p k : ℕ) (H : Matrix (Fin N) (Fin N) ℂ)
    (table : Fin N → Fin N → Qubits (valueBits k)) : Prop :=
  (∀ i j, ‖decodeValue p k (table i j) - H i j‖ ≤ precisionError p) ∧
  (∀ i j, decodeValue p k (table j i) = conj (decodeValue p k (table i j))) ∧
  (∀ i j, H i j = 0 → decodeValue p k (table i j) = 0)

/-- Permute a valid pair of binary addresses; unused addresses are fixed. -/
def locationMap {N : ℕ} (f : Fin N → Equiv.Perm (Fin N))
    (w : Qubits (addressBits N + addressBits N)) : Qubits (addressBits N + addressBits N) :=
  let xy := qubitsAppendEquiv (addressBits N) (addressBits N) w
  if h : bitsToNat xy.1 < N ∧ bitsToNat xy.2 < N then
    (qubitsAppendEquiv (addressBits N) (addressBits N)).symm
      (xy.1, natToBits (addressBits N) (f ⟨_, h.1⟩ ⟨_, h.2⟩).val)
  else w

/-- Value oracle XOR, with the value word after the two address registers. -/
def valueMap {N : ℕ} {k : ℕ} (table : Fin N → Fin N → Qubits (valueBits k))
    (w : Qubits ((addressBits N + addressBits N) + valueBits k)) :
    Qubits ((addressBits N + addressBits N) + valueBits k) :=
  let av := qubitsAppendEquiv (addressBits N + addressBits N) (valueBits k) w
  let xy := qubitsAppendEquiv (addressBits N) (addressBits N) av.1
  if h : bitsToNat xy.1 < N ∧ bitsToNat xy.2 < N then
    (qubitsAppendEquiv (addressBits N + addressBits N) (valueBits k)).symm
      (av.1, fun b => Bool.xor (av.2 b) (table ⟨_, h.1⟩ ⟨_, h.2⟩ b))
  else w

def sparseArities (N k : ℕ) (q : Fin 2) : ℕ :=
  if q = 0 then addressBits N + addressBits N
  else (addressBits N + addressBits N) + valueBits k

/-- Oracle matrices, columns input and rows output. -/
def sparseOracles {N k : ℕ} (f : Fin N → Equiv.Perm (Fin N))
    (table : Fin N → Fin N → Qubits (valueBits k)) (q : Fin 2) :
    Matrix (Qubits (sparseArities N k q)) (Qubits (sparseArities N k q)) ℂ :=
  if h : q = 0 then
    by simpa [sparseArities, h] using (Matrix.of fun y z => if y = locationMap f z then (1 : ℂ) else 0)
  else
    by simpa [sparseArities, h] using (Matrix.of fun y z => if y = valueMap table z then (1 : ℂ) else 0)

abbrev SparseCircuit (N k n : ℕ) := OracleCircuit oneTwoQubitGateSet (sparseArities N k) n

/-- All calls, including inverse and controlled calls, counted syntactically. -/
def sparseQueries {N k n : ℕ} (c : SparseCircuit N k n) : ℕ :=
  c.queryCount 0 + c.queryCount 1

/-- The clean embedding puts all work qubits first and the minimal system register last. -/
def cleanInput (N w : ℕ) : Matrix (Qubits (w + addressBits N)) (Fin N) ℂ :=
  Matrix.of fun z j => if (qubitsAppendEquiv w (addressBits N) z).1 = (fun _ => false) ∧
    bitsToNat (qubitsAppendEquiv w (addressBits N) z).2 = j.val then 1 else 0

/-- Matrix exponential with its Euclidean operator topology. -/
def evolution {N : ℕ} (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • H)

/-- Eq. (10) sees every output address and ancillary amplitude, not just a clean block. -/
def CleanSimulation {N : ℕ} (w : ℕ) (t ε : ℝ) (H : Matrix (Fin N) (Fin N) ℂ)
    (A : Matrix (Qubits (w + addressBits N)) (Qubits (w + addressBits N)) ℂ) : Prop :=
  A ∈ Matrix.unitaryGroup _ ℂ ∧
  opNorm (A * cleanInput N w - cleanInput N w * evolution t H) ≤ ε

/-- Exact displayed scale in Eq. (11). -/
def simulationScale (d : ℕ) (t Λ Λmax ε : ℝ) : ℝ :=
  t * Real.sqrt d * Λ + Real.sqrt (t * d * Λmax * Real.log (2 / ε)) + Real.log (2 / ε)

end SparseHamiltonianNorm.Simulation


