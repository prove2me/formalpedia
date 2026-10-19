-- Prove2me | Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords
-- name    : QAlgorithms_Defs_ProjectiveCliffords
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:28.264759+00:00
-- url     : https://prove2.me/theorems/eeec1da5-165c-4101-8fb2-348eefa47aeb
-- title:
--   ProjectiveCliffords
-- statement:
--   ProjectiveCliffords
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ProjectiveCliffords.lean

import Definitions.Def_QAlgorithms_Defs_QECC
noncomputable section

namespace QAlgorithms.Clifford

/-- The unitary normalizer of the full phase-inclusive Pauli group
(2011.09636 p.4, Eq.(15); 2305.15398 p.2). -/
def normalizer (n : ℕ) : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ) :=
  Subgroup.normalizer (pauliGroup n : Set (Matrix.unitaryGroup (Qubits n) ℂ))

/-- Multiplication of canonical Pauli labels modulo phase, using the frozen product table
(2007.07901 p.2; 2305.15398 p.2). -/
def phaseFreeProduct {n : ℕ} (P Q : Fin n → Stabilizer.Pauli) : Fin n → Stabilizer.Pauli :=
  fun j => (Stabilizer.Pauli.mul (P j) (Q j)).2

example (n : ℕ) : (1 : Matrix.unitaryGroup (Qubits n) ℂ) ∈ normalizer n := one_mem _

example : phaseFreeProduct (![Stabilizer.Pauli.X] : Fin 1 → Stabilizer.Pauli)
    ![Stabilizer.Pauli.Z] = ![Stabilizer.Pauli.Y] := by
  funext j
  fin_cases j
  rfl


/-- Equivalence by identical physical conjugation on every operator. On the
nonempty qubit Hilbert space this is precisely quotienting by all scalar U(1)
phases, rather than only the four Pauli phases (2011.09636 pp.4,15,18). -/
def phaseSetoid (n : ℕ) : Setoid (normalizer n) where
  r U V := conjSuperop (U.val : Matrix (Qubits n) (Qubits n) ℂ) =
    conjSuperop (V.val : Matrix (Qubits n) (Qubits n) ℂ)
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- Global Clifford labels modulo every scalar phase (2011.09636 pp.4,15,18).
No local-Clifford or Pauli-subgroup replacement is made. -/
def ProjectiveGroup (n : ℕ) := Quotient (phaseSetoid n)

/-- A public representative, chosen before any unknown state or noise
(2011.09636 pp.4,18). Conjugation is independent of its scalar phase. -/
def representative {n : ℕ} (U : ProjectiveGroup n) : normalizer n := Quotient.out U

/-- Identity ensures the projective label space is nonempty
(2011.09636 p.4, Clifford group). -/
instance projectiveNonempty (n : ℕ) : Nonempty (ProjectiveGroup n) :=
  ⟨Quotient.mk (phaseSetoid n) 1⟩

/-- Uniform sampling of the entire finite projective group. A finite enumeration
does not select a design subset and does not depend on hidden inputs
(2011.09636 pp.4,15,18). The shape-independent finiteness proof is a remaining
substrate obligation; the enumeration supplied here may be any enumeration of
the entire quotient, since uniform sampling is enumeration independent. -/
def uniformGlobalEnsemble (n : ℕ) [Fintype (ProjectiveGroup n)] :
    PMF (ProjectiveGroup n) := PMF.uniformOfFintype _

example (n : ℕ) [Fintype (ProjectiveGroup n)] :
    ∑ U, uniformGlobalEnsemble n U = 1 := by
  simpa only [tsum_fintype] using (uniformGlobalEnsemble n).tsum_coe

example (n : ℕ) (U V : normalizer n)
    (h : conjSuperop (U.val : Matrix (Qubits n) (Qubits n) ℂ) =
      conjSuperop (V.val : Matrix (Qubits n) (Qubits n) ℂ)) :
    Quotient.mk (phaseSetoid n) U = Quotient.mk (phaseSetoid n) V := Quotient.sound h

end QAlgorithms.Clifford


