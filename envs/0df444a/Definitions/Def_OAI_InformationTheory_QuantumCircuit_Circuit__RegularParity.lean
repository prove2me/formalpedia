-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Circuit__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:10:01.258195+00:00
-- url     : https://prove2.me/theorems/f24cbf23-1151-477e-bcf4-fa947798c854
-- title:
--   Rotating and flipping the reference axes of a product projection
-- statement:
--   This file introduces the operations that change the reference axes of a count $M=(S,v)$ (support $S$, unit vectors $v_i\in\mathbb C^2$ for $i\in S$) without changing its support, together with the normalization facts they need.
--
--   1. **Squared norm as an inner product.** For $v\in\mathbb C^2$, the real number $\sum_b |v_b|^2$, viewed in $\mathbb C$, equals $v^{\ast}v=\sum_b\overline{v_b}\,v_b$.
--   2. **Unitaries preserve unit vectors.** If $U\in\mathbb C^{2\times2}$ is unitary and $\sum_b|v_b|^2=1$, then $\sum_b|(Uv)_b|^2=1$.
--   3. **Canonical orthogonal vector.** For $v=(v_0,v_1)\in\mathbb C^2$,
--   $$
--   v^{\perp}=\bigl(-\overline{v_1},\ \overline{v_0}\bigr),
--   $$
--   which is orthogonal to $v$ and is a unit vector whenever $v$ is.
--   4. **Rotation by a local layer.** For a local layer $L=(L_0,\dots,L_{N-1})$ of one-qubit unitaries, the rotated count is $M^L=(S,(L_iv_i)_i)$. (Its zero-mismatch projection is $L\,P_M^0\,L^{\ast}$, which is how local gates are moved through product projections.)
--   5. **Flipping axes.** For a set $F$ of qubits, $M^{\oplus F}=(S,w)$ with $w_i=v_i^{\perp}$ for $i\in F$ and $w_i=v_i$ otherwise. Flipping the axes on $F$ turns the mismatch pattern $F$ of $M$ into the zero-mismatch pattern of $M^{\oplus F}$.
--   6. **Reversed reflection layer.** For a reflection layer $(A_1,\dots,A_m)$ (counts with pairwise disjoint supports), its reversal is $(A_m,\dots,A_1)$, again a reflection layer.
--
--   Rotation is used to absorb local unitaries into the projections, and flipping is used to express every pattern projection $P_M^F$ as the zero-mismatch projection of another count; both preserve the support, so all support-size bounds survive these operations.
--
--   **Formalization Note** The items correspond to `coe_sum_normSq`, `normalized_mulVec`, `orthogonalVector` with `orthogonalVector_normalized`, `Count.rotate`, `Count.flip` and `ReflectionLayer.reverse`. The vector $v_i$ is transformed for every qubit $i$, but only the values on the support matter.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Circuit.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Circuit.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RegularParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection__RegularParity

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


