-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli
-- name    : OAI_InformationTheory_QuantumCircuit_Toffoli
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:23:59.731203+00:00
-- url     : https://prove2.me/theorems/f0d78a19-f9c4-4996-aaed-7e98a946c0f4
-- title:
--   Basis and minus vectors and the product projection of a Toffoli gate
-- statement:
--   The file defines the one-qubit vectors and the count used to write a Toffoli gate as a reflection:
--
--   1. **Basis vectors.** For $b\in\{0,1\}$, $|b\rangle\in\mathbb{C}^2$ is the standard basis vector with entry $1$ at $b$ and $0$ at the other bit; it is a unit vector.
--
--   2. **The constant $1/\sqrt2$.** $h=(\sqrt2)^{-1}$, with $h^2=\tfrac12$.
--
--   3. **Minus vector.** $|-\rangle=\bigl(\tfrac{1}{\sqrt2},-\tfrac{1}{\sqrt2}\bigr)\in\mathbb{C}^2$, a unit vector.
--
--   4. **Toffoli count.** For a control set $c\subseteq[N]$ and a target $t\in[N]$, $\tau_{c,t}$ is the count with support $c\cup\{t\}$, vector $|-\rangle$ at the target and $|1\rangle$ at every other qubit. For $t\notin c$ its zero projection is
--   $$
--   \Pi^{\tau_{c,t}}_0=|-\rangle\langle-|_{t}\otimes\bigotimes_{i\in c}|1\rangle\langle1|_{i}\otimes I_{\mathrm{rest}} .
--   $$
--
--   The purpose of $\tau_{c,t}$ is the exact identity $\mathrm{Tof}_{c,t}=I-2\,\Pi^{\tau_{c,t}}_0$ for the Toffoli gate that flips the target exactly when all controls are $1$ (for $t\notin c$): on the subspace where all controls are $1$ the bit flip on the target is $X=I-2|-\rangle\langle-|$, and elsewhere both sides act as the identity. Thus every Toffoli gate, of any arity, is a reflection about a product projection, which is what brings physical circuits into the reflection normal form.
--
--   **Formalization Note** The Lean names are `basisVector`, `halfScale`, `halfScale_sq`, `basisVector_normalized`, `minusVector`, `minusVector_normalized` and `toffoliCount`. The definition of `toffoliCount` does not require $t\notin c$ (if $t\in c$ the support is $c$ and the target still carries $|-\rangle$); the Toffoli identity is proved separately under the hypothesis $t\notin c$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Toffoli.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Toffoli.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization

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


