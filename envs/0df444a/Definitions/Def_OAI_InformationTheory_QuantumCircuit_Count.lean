-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
-- name    : OAI_InformationTheory_QuantumCircuit_Count
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:13:09.836901+00:00
-- url     : https://prove2.me/theorems/8f435165-60ac-4d45-9710-2101b95f9f6f
-- title:
--   The empty count and the join and restriction of counts
-- statement:
--   Recall that a count on $N$ qubits consists of a support $S\subseteq[N]$ and one-qubit vectors $v_i\in\mathbb{C}^2$ that are unit vectors for $i\in S$, and that its zero projection is $\Pi_0=\bigotimes_i Q_i$ with $Q_i=|v_i\rangle\langle v_i|$ on $S$ and $Q_i=I$ off $S$. The file defines three operations on counts:
--
--   1. **Empty count.** $\varnothing_N$ has empty support (and all vectors $0$). Its zero projection is the identity, $\Pi^{\varnothing_N}_0=I$, which is recorded as a simplification lemma.
--
--   2. **Join.** For counts $A=(S_A,(a_i))$ and $B=(S_B,(b_i))$, the join $A\vee B$ has support $S_A\cup S_B$ and vector $a_i$ for $i\in S_A$, $b_i$ for $i\notin S_A$.
--
--   3. **Restriction.** For a count $M=(S,(v_i))$ and a set $T\subseteq[N]$, $M|_T$ has support $S\cap T$ and the same vectors $v_i$.
--
--   When $A$ and $B$ have disjoint supports, $\Pi^{A\vee B}_0=\Pi^A_0\,\Pi^B_0$, so joins express products of commuting product projections as a single product projection; this is how a product of reflections $\prod_j(I-2\Pi^{A_j}_0)$ is expanded into product terms. Restrictions describe sub-products of one product projection with the same axes; they occur when powers of the mismatch operator are expanded into monomials, where repeated qubit indices collapse.
--
--   **Formalization Note** The Lean names are `Count.empty`, `Count.empty_zero`, `Count.join` and `Count.restrict`. The join is defined for arbitrary counts; on overlapping supports the vectors of $A$ take precedence. The product formula for joins is proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Count.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Count.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

def Count.empty {N : ℕ} : Count N where
  support := ∅
  vector := fun _ _ => 0
  normalized := by simp

@[simp] lemma Count.empty_zero {N : ℕ} : (Count.empty : Count N).zero = 1 := by
  simp [Count.zero, Count.empty]

def Count.join {N : ℕ} (A B : Count N) : Count N where
  support := A.support ∪ B.support
  vector i := if i ∈ A.support then A.vector i else B.vector i
  normalized i hi := by
    classical
    split_ifs with hA
    · exact A.normalized i hA
    · exact B.normalized i ((Finset.mem_union.mp hi).resolve_left hA)

/-- Subcounts with the same axes, allowing repeated monomial indices to collapse. -/
def Count.restrict {N : ℕ} (M : Count N) (S : Finset (Fin N)) : Count N where
  support := M.support ∩ S
  vector := M.vector
  normalized i hi := M.normalized i (Finset.mem_inter.mp hi).1

end QAC

end

end OAI


