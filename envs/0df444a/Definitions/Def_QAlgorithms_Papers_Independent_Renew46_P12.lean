-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12
-- name    : QAlgorithms_Papers_Independent_Renew46_P12
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:08:01.50807+00:00
-- url     : https://prove2.me/theorems/ea134d38-f255-4a5f-8f4b-b80bed52f1e8
-- title:
--   Definitions for Synthesis of unitaries with Clifford+T circuits
-- statement:
--   The objects the formalized statements of *Synthesis of unitaries with Clifford+T circuits* (arXiv:1306.3200) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HasDenominator`: PDF pp.1–2: a coordinate with four integer coefficients and denominator `base^k`. Use `base = sqrt 2` in exact synthesis and `base = 2` in Lemma 3. The exponent is a representation bound, with no minimality requirement.
--   - `householderReflection`: PDF p.1: `R_v = I - 2 |v><v|`, with this sign and with no phase quotient. Unit normalization is a separate hypothesis whenever the source says reflection.
--   - `simulationDilation`: PDF pp.1–2, Lemma 1: the explicitly constructed simulation unitary `|0><1| tensor U + |1><0| tensor U†`; the added qubit is the first tensor factor.
--   - `reflectionVector`: PDF p.2, Lemma 1: `( |1,j> plus/minus |0,u_j> ) / sqrt 2`. `negative = true` selects the minus vector (eigenvalue -1). The column is computed from U, rather than supplied as an unrelated vector.
--   - `identityExtension`: PDF p.3, Lemma 3: the full `I_2 tensor A`, including both ancillary sectors.
--   - `initializedMap`: PDF pp.1–3: the rectangular input/output map of M with all w trailing ancillas initialized to zero. All output rows are retained, so leakage is charged as error.
--   - `idealMap`: PDF pp.1–3: ideal map `psi -> (U psi) tensor |0^w>` on the same fixed trailing ancilla wires as `initializedMap`; an ordinary complex matrix, including global phase.
-- source:
--   Synthesis of unitaries with Clifford+T circuits, arXiv:1306.3200v1, https://arxiv.org/abs/1306.3200v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_CircuitResources

/-!
Statements from V. Kliuchnikov, arXiv:1306.3200v1, PDF pp.1–3.
The circuit gate set is the frozen elementary {H,T,CNOT} set. Ancillas occupy
fixed trailing wires and start in zero. Errors are ordinary, unnormalized,
phase-sensitive Frobenius errors. The uniform bounds below use threshold n = 1;
the constructive bounds on pp.2–3 allow absolute constants to cover this whole regime.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P12

noncomputable section

/-- PDF pp.1–2: a coordinate with four integer coefficients and denominator `base^k`.
Use `base = sqrt 2` in exact synthesis and `base = 2` in Lemma 3. The exponent
is a representation bound, with no minimality requirement. -/
def HasDenominator (base : ℝ) (k : ℕ) (z : ℂ) : Prop :=
  ∃ a b c d : ℤ, z =
    ((a : ℂ) + (b : ℂ) * (Real.sqrt 2 : ℂ) +
      Complex.I * ((c : ℂ) + (d : ℂ) * (Real.sqrt 2 : ℂ))) / (base : ℂ) ^ k

/-- PDF p.1: `R_v = I - 2 |v><v|`, with this sign and with no phase quotient.
Unit normalization is a separate hypothesis whenever the source says reflection. -/
def householderReflection {ι : Type*} [DecidableEq ι] (v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - 2 * v i * star (v j)

/-- PDF pp.1–2, Lemma 1: the explicitly constructed simulation unitary
`|0><1| tensor U + |1><0| tensor U†`; the added qubit is the first tensor factor. -/
def simulationDilation {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ :=
  Matrix.of fun p q => if p.1 then (if q.1 then 0 else star (U q.2 p.2))
    else (if q.1 then U p.2 q.2 else 0)

/-- PDF p.2, Lemma 1: `( |1,j> plus/minus |0,u_j> ) / sqrt 2`.
`negative = true` selects the minus vector (eigenvalue -1). The column is computed
from U, rather than supplied as an unrelated vector. -/
def reflectionVector {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (j : Qubits n) (negative : Bool) : EuclideanSpace ℂ (Bool × Qubits n) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (tensorVec (ket true) (ket j) + (if negative then (-1 : ℂ) else 1) •
      tensorVec (ket false) (WithLp.toLp 2 fun i => U i j))

/-- PDF p.3, Lemma 3: the full `I_2 tensor A`, including both ancillary sectors. -/
def identityExtension {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then A p.2 q.2 else 0

/-- PDF pp.1–3: the rectangular input/output map of M with all w trailing ancillas
initialized to zero. All output rows are retained, so leakage is charged as error. -/
def initializedMap {n w : ℕ} (M : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ) :
    Matrix (Qubits (n + w)) (Qubits n) ℂ :=
  Matrix.of fun y x => M y (Fin.append x (fun _ : Fin w => false))

/-- PDF pp.1–3: ideal map `psi -> (U psi) tensor |0^w>` on the same fixed trailing
ancilla wires as `initializedMap`; an ordinary complex matrix, including global phase. -/
def idealMap {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (w : ℕ) :
    Matrix (Qubits (n + w)) (Qubits n) ℂ :=
  Matrix.of fun y x => if (qubitsAppendEquiv n w y).2 = (fun _ => false)
    then U (qubitsAppendEquiv n w y).1 x else 0

/-! Small definitional sanity checks; the six paper theorems below have no proofs. -/

example (base : ℝ) (k : ℕ) : HasDenominator base k 0 := by
  refine ⟨0, 0, 0, 0, ?_⟩
  simp

example (base : ℝ) : HasDenominator base 0 1 := by
  refine ⟨1, 0, 0, 0, ?_⟩
  simp

example {ι : Type*} [DecidableEq ι] (i : ι) : householderReflection (ket i) i i = -1 := by
  norm_num [householderReflection, ket]

example {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (i j : Qubits n) :
    simulationDilation U (false, i) (true, j) = U i j := rfl

example {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (i j : Qubits n) :
    simulationDilation U (true, i) (false, j) = star (U j i) := rfl

example {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (j : Qubits n) (s : Bool) :
    reflectionVector U j s (true, j) = (Real.sqrt 2 : ℂ)⁻¹ := by
  cases s <;> simp [reflectionVector, tensorVec, ket]

example {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ) (i j : Qubits n) :
    identityExtension A (false, i) (true, j) = 0 := rfl

example {n w : ℕ} (x : Qubits n) :
    initializedMap (1 : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ)
      (Fin.append x (fun _ : Fin w => false)) x = 1 := by
  simp [initializedMap]

example {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (w : ℕ) (x y : Qubits n) :
    idealMap U w (Fin.append y (fun _ : Fin w => false)) x = U y x := by
  simp [idealMap, qubitsAppendEquiv]

end

end QAlgorithms.Papers.Independent.Renew46.P12


