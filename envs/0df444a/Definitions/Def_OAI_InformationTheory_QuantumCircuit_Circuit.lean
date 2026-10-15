-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
-- name    : OAI_InformationTheory_QuantumCircuit_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:11:38.776866+00:00
-- url     : https://prove2.me/theorems/28a55a09-0001-43cb-aab8-668391d60c5b
-- title:
--   Unitary rotation and orthogonal flipping of counts, and reversed reflection layers
-- statement:
--   Let $M$ be a count on $N$ qubits with support $S$ and one-qubit vectors $(v_i)_{i\in[N]}$ that are unit vectors for $i\in S$. The file defines:
--
--   1. **Orthogonal vector.** For $v=(v_0,v_1)\in\mathbb{C}^2$, $v^{\perp}=(-\overline{v_1},\,\overline{v_0})$. It is orthogonal to $v$, and it is a unit vector whenever $v$ is.
--
--   2. **Rotation by a local layer.** For a local layer $L=(L_i)_{i\in[N]}$ of one-qubit unitaries, $M^{L}$ is the count with the same support $S$ and vectors $L_i v_i$. Unit vectors stay unit because a unitary preserves $\sum_b|v(b)|^2$.
--
--   3. **Flip on a set.** For $F\subseteq[N]$, $M^{\oplus F}$ is the count with the same support and vectors $v_i^{\perp}$ for $i\in F$ and $v_i$ for $i\notin F$.
--
--   4. **Reversed reflection layer.** For a reflection layer $R=(A_1,\dots,A_m)$, $R^{\mathrm{rev}}=(A_m,\dots,A_1)$, whose supports are again pairwise disjoint.
--
--   Two auxiliary facts are recorded for the normalization proofs: $\sum_b|v(b)|^2$, viewed as a complex number, equals $v^{*}v$; and for a unitary $U\in U(2)$, $\sum_b|v(b)|^2=1$ implies $\sum_b|(Uv)(b)|^2=1$.
--
--   These operations realize the symmetries of the circuit model inside the class of counts. Rotation implements conjugation by a local layer, $\Pi^{M^L}_0=\bigl(\bigotimes_iL_i\bigr)\,\Pi^M_0\,\bigl(\bigotimes_iL_i\bigr)^{*}$, so one-qubit gates never enlarge supports. Flipping exchanges $|v_i\rangle\langle v_i|$ and $I-|v_i\rangle\langle v_i|$ on $F$, so the pattern projection $\Pi^M_F$ becomes the zero projection of $M^{\oplus F}$. Reversing a layer computes the adjoint of its product of reflections.
--
--   **Formalization Note** The Lean names are `orthogonalVector`, `orthogonalVector_normalized`, `Count.rotate`, `Count.flip`, `ReflectionLayer.reverse`, `coe_sum_normSq` and `normalized_mulVec`. The flip replaces the vector at every $i\in F$, also outside the support, where this has no effect. The identities in the last paragraph are proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Circuit.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Circuit.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma coe_sum_normSq (v : Bit → ℂ) :
    ((∑ b, Complex.normSq (v b) : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [Complex.ofReal_sum, dotProduct, Pi.star_apply, Complex.star_def,
    mul_comm ((starRingEnd ℂ) _), Complex.mul_conj]

lemma normalized_mulVec {U : QubitOperator} (hU : U ∈ unitary QubitOperator)
    {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    ∑ b, Complex.normSq ((U *ᵥ v) b) = 1 := by
  apply Complex.ofReal_injective
  rw [coe_sum_normSq, Matrix.star_mulVec, dotProduct_mulVec, Matrix.vecMul_vecMul]
  change Matrix.vecMul (star v) (star U * U) ⬝ᵥ v = _
  rw [Unitary.star_mul_self_of_mem hU, Matrix.vecMul_one]
  simpa only [dotProduct, Pi.star_apply, Complex.ofReal_one] using normalized_complex hv

/-- The canonical orthogonal unit vector in a qubit. -/
def orthogonalVector (v : Bit → ℂ) : Bit → ℂ := ![-star (v 1), star (v 0)]

lemma orthogonalVector_normalized {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    ∑ b, Complex.normSq (orthogonalVector v b) = 1 := by
  simpa [orthogonalVector, Fin.sum_univ_two, Complex.star_def, add_comm] using hv

/-- Conjugation by a local layer preserves the exact count support. -/
def Count.rotate {N : ℕ} (M : Count N) (L : LocalLayer N) : Count N where
  support := M.support
  vector i := (L i : QubitOperator) *ᵥ M.vector i
  normalized i hi := normalized_mulVec (L i).property (M.normalized i hi)

/-- Flipping any subset of the reference axes is still a count, not an added gate. -/
def Count.flip {N : ℕ} (M : Count N) (F : Finset (Fin N)) : Count N where
  support := M.support
  vector i := if i ∈ F then orthogonalVector (M.vector i) else M.vector i
  normalized i hi := by
    split_ifs
    · exact orthogonalVector_normalized (M.normalized i hi)
    · exact M.normalized i hi

def ReflectionLayer.reverse {N : ℕ} (R : ReflectionLayer N) : ReflectionLayer N where
  gates := R.gates.reverse
  disjoint := (R.disjoint.imp (fun h => h.symm)).reverse

end QAC

end

end OAI


