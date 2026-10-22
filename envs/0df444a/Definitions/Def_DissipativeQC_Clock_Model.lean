-- Prove2me | Definitions.Def_DissipativeQC_Clock_Model
-- name    : DissipativeQC_Clock_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:10.080244+00:00
-- url     : https://prove2.me/theorems/9de99e20-96b0-41a7-9e32-5ddb37580bfc
-- title:
--   Eqs. (2)–(4), pp. 1–2 and Appendix pp. 4–5 — DQC clock model
-- statement:
--   The DQC model consists of $N$ qubits and clock times $0,\ldots,T$. For gates $U_1,\ldots,U_T$, the reset operators lower one qubit at clock zero, and the clock operators move from $t$ to $t+1$ with $U_{t+1}$ and back with its adjoint. The Lindblad generator applies equation (1) to these jumps. The history vectors and state are
--
--   $$|\psi_t\rangle=U_t\cdots U_1|0\cdots0\rangle,\qquad \rho_0=\frac1{T+1}\sum_{t=0}^T|\psi_t\rangle\langle\psi_t|\otimes|t\rangle\langle t|.$$
--
--   The same file defines the gate removal unitary $W$, the connected clock path matrix, and its clock zero penalized version. They expose the operators used by the appendix's spectral claims.
--
--   **Formalization Note** Qubit strings are functions from $\{0,\ldots,N-1\}$ to $\{0,1\}$; the carrier is qubits paired with a clock. Lean's $U(t)$ is $U_{t+1}$ in the paper, repairing the impossible endpoints of printed equation (3). The path matrix includes the first edge, as its stated spectrum requires. The model permits $N=0$ and arbitrary unitary gates.
-- source:
--   Verstraete, Wolf & Cirac, Quantum computation, quantum state engineering, and quantum phase transitions driven by dissipation, arXiv:0803.1447v2, pp. 1–2, eqs. (2)–(4); pp. 4–5, Appendix: Efficiency of DQC

import Mathlib
import Definitions.Def_DissipativeQC_Clock_Lindblad

noncomputable section
open scoped Matrix Kronecker ComplexConjugate

namespace DissipativeQC.Clock

/-- Computational basis strings for N qubits. -/
abbrev Qubits (N : ℕ) := Fin N → Fin 2

/-- Qubits followed by a clock with values 0 through T. -/
abbrev Sys (N T : ℕ) := Qubits N × Fin (T + 1)

/-- The lowering operator on qubit i. -/
def lowerAt {N : ℕ} (i : Fin N) : Matrix (Qubits N) (Qubits N) ℂ :=
  Matrix.of fun x y => if y i = 1 ∧ x = Function.update y i 0 then 1 else 0

/-- Eq. (2): reset qubit i at clock time zero. -/
def resetOp {N T : ℕ} (i : Fin N) : Matrix (Sys N T) (Sys N T) ℂ :=
  lowerAt i ⊗ₖ Matrix.single (0 : Fin (T + 1)) 0 1

/-- Eq. (3), with U t taking clock time t to t+1. -/
def stepOp {N T : ℕ} (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ) (t : Fin T) :
    Matrix (Sys N T) (Sys N T) ℂ :=
  U t ⊗ₖ Matrix.single t.succ t.castSucc 1 +
    (U t)ᴴ ⊗ₖ Matrix.single t.castSucc t.succ 1

/-- All the jump operators of the DQC process. -/
def jumpOps {N T : ℕ} (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ) :
    Fin N ⊕ Fin T → Matrix (Sys N T) (Sys N T) ℂ :=
  Sum.elim resetOp (stepOp U)

/-- The generator given literally by eqs. (1)–(3). -/
def dqcGen {N T : ℕ} (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ) :
    Module.End ℂ (Matrix (Sys N T) (Sys N T) ℂ) :=
  lindbladian (jumpOps U)

/-- The prefix U_t ... U_1, with U 0 denoting U_1. -/
def gatePrefix {N T : ℕ} (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ)
    (t : Fin (T + 1)) : Matrix (Qubits N) (Qubits N) ℂ :=
  ((List.ofFn (fun k : Fin t.val =>
    U ⟨k.val, lt_of_lt_of_le k.isLt (Nat.le_of_lt_succ t.isLt)⟩)).reverse).prod

/-- The circuit state at clock time t. -/
def histVec {N T : ℕ} (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ)
    (t : Fin (T + 1)) : Qubits N → ℂ :=
  (gatePrefix U t).mulVec (Pi.single (fun _ => (0 : Fin 2)) 1)

/-- Eq. (4): the normalized mixed history state. -/
def rho0 {N T : ℕ} (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ) :
    Matrix (Sys N T) (Sys N T) ℂ :=
  ((T : ℂ) + 1)⁻¹ • ∑ t : Fin (T + 1),
    Matrix.vecMulVec (histVec U t) (star (histVec U t)) ⊗ₖ Matrix.single t t 1

/-- The gate-removal unitary W on p. 4. -/
def gateRemoval {N T : ℕ} (U : Fin T → Matrix (Qubits N) (Qubits N) ℂ) :
    Matrix (Sys N T) (Sys N T) ℂ :=
  ∑ t : Fin (T + 1), gatePrefix U t ⊗ₖ Matrix.single t t 1

/-- Connected path generator for the L_00 block. -/
def pathMatrix (T : ℕ) : Matrix (Fin (T + 1)) (Fin (T + 1)) ℝ :=
  Matrix.of fun s t =>
    if (s : ℕ) + 1 = t ∨ (t : ℕ) + 1 = s then 1
    else if s = t then
      -((if (s : ℕ) = 0 then (0 : ℝ) else 1) +
        (if (s : ℕ) = T then (0 : ℝ) else 1))
    else 0

/-- The path block with an extra clock-zero penalty a. -/
def cornerMatrix (T : ℕ) (a : ℝ) : Matrix (Fin (T + 1)) (Fin (T + 1)) ℝ :=
  pathMatrix T - a • Matrix.single 0 0 1

end DissipativeQC.Clock


