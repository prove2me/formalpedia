-- Prove2me | Definitions.Def_QAlgorithms_Defs_FiniteValueAccess
-- name    : QAlgorithms_Defs_FiniteValueAccess
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:12.813421+00:00
-- url     : https://prove2.me/theorems/5dafe5b6-9a2e-489a-afa4-9cb2d5d22183
-- title:
--   FiniteValueAccess
-- statement:
--   FiniteValueAccess
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FiniteValueAccess.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_FiniteOraclePrograms
noncomputable section

namespace QAlgorithms.ValueAccess

variable {n m d k b w M K N c out : ℕ}

/-- Fixed affine binary decoding, 1809.00643 pp.5,10,28.
The offset is unrestricted, and the resolution is positive. -/
structure FixedPointEncoding (b : ℕ) where
  offset : ℝ
  scale : ℝ
  scale_pos : 0 < scale

/-- Binary fixed-point value, 1809.00643 p.10. -/
def FixedPointEncoding.value {b : ℕ} (E : FixedPointEncoding b) (z : Qubits b) : ℝ :=
  E.offset + E.scale * bitsToNat z

/-- Exact finite union of center, local Jordan and finite-difference query
grids, 1809.00643 pp.9–13 and 2503.17356 pp.22–23.
A finite index set need not be a single rational lattice: the union handles
incommensurate public scales. meshBudget is geometric, independent of f. -/
structure CompatibleHypergrid (d : ℕ) (I : Type) [Fintype I] where
  dim_pos : 0 < d
  centerBits : ℕ
  jordanBits : ℕ
  x : Fin d → ℝ
  r1 : ℝ
  r2 : ℝ
  r1_pos : 0 < r1
  r2_pos : 0 < r2
  r2_le : r2 ≤ r1
  meshBudget : ℝ
  mesh_pos : 0 < meshBudget
  centerMesh : 2 * r1 * ((2 : ℝ) ^ centerBits)⁻¹ ≤ meshBudget
  localMesh : (2 * r2 / d) * ((2 : ℝ) ^ jordanBits)⁻¹ ≤ meshBudget
  point : I → Fin d → ℝ
  injective : Function.Injective point
  contained : ∀ i j, |point i j - x j| ≤ 2 * r1
  localIndex : (Fin d → Qubits centerBits) → (Fin d → Qubits jordanBits) → I
  local_eq : ∀ s z j, point (localIndex s z) j =
    x j + 2 * r1 * gridPoint centerBits (s j) +
      (2 * r2 / d) * gridPoint jordanBits (z j)
  differenceIndex : (Fin d → Qubits centerBits) → Fin d → Bool → I
  difference_eq : ∀ s j sign k, point (differenceIndex s j sign) k =
    x k + 2 * r1 * gridPoint centerBits (s k) +
      (if k = j then (if sign then r2 else -r2) else 0)

/-- Closed versus strict approximation endpoint: 1809.00643 pp.10,12
uses ≤; 2503.17356 pp.5,22 uses <. All XOR basis inputs are specified. -/
def IsApproxBinaryValueOracle {d b : ℕ} {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (point : I → Fin d → ℝ) (decode : Qubits b → ℝ) (strict : Bool)
    (f : (Fin d → ℝ) → ℝ) (theta : ℝ)
    (U : Matrix (I × Qubits b) (I × Qubits b) ℂ) : Prop :=
  Function.Injective point ∧ 0 < theta ∧ U ∈ Matrix.unitaryGroup _ ℂ ∧
    ∃ code : I → Qubits b,
      (∀ i, if strict then |decode (code i) - f (point i)| < theta
        else |decode (code i) - f (point i)| ≤ theta) ∧
      ∀ i y, act U (ket (i,y)) = ket (i, y + code i)

/-- Relational value approximator with preserved query index and arbitrary
garbage, 1809.00643 p.5 Definition 2, pp.12,27.
Inverse access follows from unitarity; phase uncomputation is not assumed. -/
def IsRelationalValueApproximator {d b w : ℕ} {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (point : I → Fin d → ℝ) (decode : Qubits b → ℝ)
    (f : (Fin d → ℝ) → ℝ) (delta : ℝ)
    (U : Matrix (I × (Qubits b × Qubits w)) (I × (Qubits b × Qubits w)) ℂ) : Prop :=
  Function.Injective point ∧ 0 < delta ∧ U ∈ Matrix.unitaryGroup _ ℂ ∧
    ∀ i, (∀ z, z.1 ≠ i → act U (ket (i,(0,0))) z = 0) ∧
      probEvent (act U (ket (i,(0,0))))
        (fun z => |decode z.2.1 - f (point i)| ≤ delta) ≥ 2 / 3

/-- Sanity check for the modeled source objects (arxiv-1809.00643v4, PDF pp.5,9,10,12,27,28; arxiv-2503.17356v2, PDF pp.5,22,23,30). -/
example {b : ℕ} (E : FixedPointEncoding b) :
    E.value (fun _ => false) = E.offset := by
  simp [FixedPointEncoding.value, bitsToNat]

/-- Sanity check for the modeled source objects (arxiv-1809.00643v4, PDF pp.5,9,10,12,27,28; arxiv-2503.17356v2, PDF pp.5,22,23,30). -/
example {d b : ℕ} {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (point : I → Fin d → ℝ) (hpoint : Function.Injective point) (theta : ℝ) (ht : 0 < theta)
    (decode : Qubits b → ℝ) (f : (Fin d → ℝ) → ℝ) (h : ∀ i, decode 0 = f (point i)) :
    IsApproxBinaryValueOracle point decode false f theta 1 := by
  refine ⟨hpoint, ht, one_mem _, fun _ => 0, ?_, ?_⟩
  · intro i; simp [h i, ht.le]
  · intro i y; simp [act]

end QAlgorithms.ValueAccess


