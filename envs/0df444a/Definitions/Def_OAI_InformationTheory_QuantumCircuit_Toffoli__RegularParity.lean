-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Toffoli__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:23:07.640397+00:00
-- url     : https://prove2.me/theorems/516ae325-42b0-4393-9a85-fee003f29ab3
-- title:
--   Basis and minus vectors and the product projection of a Toffoli gate
-- statement:
--   This file introduces the one-qubit vectors needed to write a Toffoli gate as a reflection about a product projection.
--
--   1. **Computational basis vectors.** For $b\in\{0,1\}$, $|b\rangle\in\mathbb C^2$ is the vector with entry $1$ at $b$ and $0$ elsewhere; it is a unit vector.
--   2. **The constant $h$.** $h=1/\sqrt2$, with $h^2=\tfrac12$.
--   3. **Minus vector.** $|-\rangle=(h,\,-h)\in\mathbb C^2$, a unit vector.
--   4. **Toffoli count.** For a set $c$ of control qubits and a target qubit $t$, the count $T_{c,t}$ has support $c\cup\{t\}$, axis $|-\rangle$ at $t$ and axis $|1\rangle$ at every other qubit. When $t\notin c$ its zero-mismatch projection is
--   $$
--   P^0_{T_{c,t}}=|-\rangle\langle-|_{t}\ \otimes\ \bigotimes_{i\in c}|1\rangle\langle1|_{i}\ \otimes\ I_{\text{rest}} .
--   $$
--
--   The point of item 4 is the exact identity $\mathrm{Toffoli}_{c,t}=I-2\,P^0_{T_{c,t}}$ for $t\notin c$ (proved in the solution file): flipping the target when all controls are $1$ is the reflection that negates $|-\rangle$ on the target in the all-ones control subspace. This turns every Toffoli gate, of any arity, into a reflection about a product projection, which is the form required by the localization machinery.
--
--   **Formalization Note** The definitions are `basisVector`, `halfScale` (with `halfScale_sq`), `minusVector` and `toffoliCount`, with the normalization lemmas `basisVector_normalized` and `minusVector_normalized`. The definition of `toffoliCount` does not itself require $t\notin c$; if $t\in c$ the support is $c$ and qubit $t$ carries the axis $|-\rangle$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Toffoli.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Toffoli.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RegularParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization__RegularParity

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

/-- Computational basis vectors and the normalized minus vector. -/
def basisVector (b : Bit) : Bit → ℂ := fun x => if x=b then 1 else 0

def halfScale : ℝ := (Real.sqrt 2)⁻¹

lemma halfScale_sq : halfScale^2 = 1/2 := by
  rw [halfScale,inv_pow,Real.sq_sqrt (by norm_num)]
  norm_num

lemma basisVector_normalized (b : Bit) : ∑ x, Complex.normSq (basisVector b x) = 1 := by
  classical
  simp [basisVector]

def minusVector (b : Bit) : ℂ := if b=0 then (halfScale:ℂ) else -(halfScale:ℂ)

lemma minusVector_normalized : ∑ b, Complex.normSq (minusVector b) = 1 := by
  norm_num [Fin.sum_univ_two,minusVector,Complex.normSq_ofReal]
  nlinarith only [halfScale_sq]

/-- The product projection in the exact Toffoli identity I-2 C⊗|-><-|. -/
def toffoliCount {N : ℕ} (c : Finset (Fin N)) (t : Fin N) : Count N where
  support := insert t c
  vector i := if i=t then minusVector else basisVector 1
  normalized i _ := by
    split_ifs
    · exact minusVector_normalized
    · exact basisVector_normalized 1

end QAC

end

end OAI


