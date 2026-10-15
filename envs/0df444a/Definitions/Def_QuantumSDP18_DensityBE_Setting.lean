-- Prove2me | Definitions.Def_QuantumSDP18_DensityBE_Setting
-- name    : QuantumSDP18_DensityBE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:44.008996+00:00
-- url     : https://prove2.me/theorems/e860c718-4a71-4a3b-9a9f-fb37eff06699
-- title:
--   Definition 1 and proof of Lemma 12 — subnormalized purification and register construction
-- statement:
--   A **subnormalized density operator** ϱ on a w-qubit register is a positive semidefinite matrix with trace at most one. A **purification** is a unit vector |φ⟩ on three registers: the w-qubit system, one flag qubit, and c junk qubits. Taking the flag-zero block and tracing out the junk gives ϱ. In matrix entries,
--
--   $$
--   \langle\varphi|\varphi\rangle=1,\qquad
--   \varrho_{ij}=\sum_{t\in\{0,1\}^{c}}\varphi_{i,0,t}\,\overline{\varphi_{j,0,t}}.
--   $$
--
--   The all-zero input of a unitary G prepares |φ⟩ by G|0⟩. The proof of Lemma 12 adds a system register and one extra qubit, swaps the first w+1 qubits with the system-and-flag part of G's register, and applies G†. It names the resulting operator V and the intermediate SWAP sandwich. These definitions fix the register order used by the theorem and its proof steps.
--
--   **Formalization Note** The paper's a ancillary qubits for G are represented as a=c+1, so the flag is always present. The zero state is the all-false basis index. The swap fixes the c junk qubits; this gives the identity factor I on c=a−1 qubits. The paper prints a qubit factor of a in the SWAP formula, which is inconsistent with its register count. The flag-zero block is the w-qubit operator intended by Definition 1 and used in Lemma 12.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 3, Definition 1; p. 16, proof of Lemma 12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding

open scoped Kronecker ComplexOrder

namespace QuantumSDP18.DensityBE

/-- The three registers used by the preparation unitary: system, flag, junk. -/
abbrev Reg (w c : ℕ) := QAlgorithms.Qubits w × Bool × QAlgorithms.Qubits c

/-- The all-zero state of the preparation register. -/
def zeroReg (w c : ℕ) : Reg w c := (fun _ => false, false, fun _ => false)

/-- The state prepared by applying `G` to the all-zero computational basis state. -/
def purifVec {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ) : Reg w c → ℂ :=
  fun r => G r (zeroReg w c)

/-- Definition 1: positive semidefinite with trace at most one. -/
def IsSubnormDensity {w : ℕ} (ϱ : Matrix (QAlgorithms.Qubits w) (QAlgorithms.Qubits w) ℂ) : Prop :=
  ϱ.PosSemidef ∧ (ϱ.trace).re ≤ 1

/-- Definition 1, read as the flag-zero block after tracing out the junk register. -/
def IsPurification {w c : ℕ} (φ : Reg w c → ℂ)
    (ϱ : Matrix (QAlgorithms.Qubits w) (QAlgorithms.Qubits w) ℂ) : Prop :=
  (∑ r, ‖φ r‖ ^ 2) = 1 ∧
    ϱ = Matrix.of fun i j => ∑ t : QAlgorithms.Qubits c,
      φ (i, false, t) * star (φ (j, false, t))

/-- System and extra flag qubit, followed by the three preparation registers. -/
abbrev Big (w c : ℕ) := (QAlgorithms.Qubits w × Bool) × Reg w c

/-- Exchange the first two `(system, flag)` registers, fixing the junk register. -/
def swapEquiv (w c : ℕ) : Big w c ≃ Big w c where
  toFun := fun x => ((x.2.1, x.2.2.1), (x.1.1, x.1.2, x.2.2.2))
  invFun := fun x => ((x.2.1, x.2.2.1), (x.1.1, x.1.2, x.2.2.2))
  left_inv := by intro x; cases x with | mk p r => cases p; cases r with | mk g ft => cases ft; rfl
  right_inv := by intro x; cases x with | mk p r => cases p; cases r with | mk g ft => cases ft; rfl

/-- The permutation matrix of the `(w + 1)`-qubit swap, with junk fixed. -/
def swapReg (w c : ℕ) : Matrix (Big w c) (Big w c) ℂ :=
  Matrix.of fun x y => if x = swapEquiv w c y then 1 else 0

/-- The unitary constructed in the proof of Lemma 12. -/
noncomputable def V {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ) : Matrix (Big w c) (Big w c) ℂ :=
  ((1 : Matrix (QAlgorithms.Qubits w × Bool) (QAlgorithms.Qubits w × Bool) ℂ) ⊗ₖ G.conjTranspose) *
    swapReg w c *
    ((1 : Matrix (QAlgorithms.Qubits w × Bool) (QAlgorithms.Qubits w × Bool) ℂ) ⊗ₖ G)

/-- The all-zero ancilla register of the reindexed block encoding. -/
def ancZero (w c : ℕ) : Bool × Reg w c := (false, zeroReg w c)

/-- Move the ancillas before the system register, as `QAlgorithms.IsBlockEncoding` expects. -/
def blockEquiv (w c : ℕ) : Big w c ≃ (Bool × Reg w c) × QAlgorithms.Qubits w where
  toFun := fun x => ((x.1.2, x.2), x.1.1)
  invFun := fun x => ((x.2, x.1.1), x.1.2)
  left_inv := by intro x; cases x with | mk p r => cases p; rfl
  right_inv := by intro x; cases x with | mk er s => cases er; rfl

/-- The central SWAP sandwich in the proof, prior to discarding the flag-one part. -/
def sandwich {w c : ℕ} (φ : Reg w c → ℂ) :
    Matrix (QAlgorithms.Qubits w) (QAlgorithms.Qubits w) ℂ :=
  Matrix.of fun i j => ∑ r : Reg w c, ∑ r' : Reg w c,
    star (φ r) * swapReg w c ((i, false), r) ((j, false), r') * φ r'

/-- The (generally unnormalized) flag-zero part of the preparation vector. -/
def flag0 {w c : ℕ} (φ : Reg w c → ℂ) : Reg w c → ℂ :=
  fun r => if r.2.1 = false then φ r else 0

end QuantumSDP18.DensityBE


