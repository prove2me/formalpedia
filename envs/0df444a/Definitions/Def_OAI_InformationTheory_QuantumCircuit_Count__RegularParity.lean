-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Count__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:11:30.010424+00:00
-- url     : https://prove2.me/theorems/cb3211c3-2c5e-43a8-b923-560d95e4b523
-- title:
--   Empty, joined and restricted product-projection data
-- statement:
--   This file defines three elementary constructions on counts, i.e. on data $M=(S,v)$ consisting of a support $S\subseteq\{0,\dots,N-1\}$ and vectors $v_i\in\mathbb C^2$ that are unit vectors for $i\in S$, with zero-mismatch projection $P_M^0=\bigotimes_{i\in S}|v_i\rangle\langle v_i|\otimes I$.
--
--   1. **Empty count.** $\varnothing_N$ has empty support and all vectors equal to $0$. Its zero-mismatch projection is the identity:
--   $$
--   P^0_{\varnothing_N}=I.
--   $$
--   2. **Join.** For counts $A=(S_A,a)$ and $B=(S_B,b)$, the join $A\vee B$ has support $S_A\cup S_B$ and vectors $a_i$ for $i\in S_A$ and $b_i$ otherwise. When $S_A$ and $S_B$ are disjoint, $P^0_{A\vee B}=P^0_A\,P^0_B$ (proved later), so joins represent products of commuting product projections.
--   3. **Restriction.** For a count $M=(S,v)$ and a set $T$ of qubits, $M|_T=(S\cap T,v)$ keeps the same axes on the smaller support.
--
--   These constructions are used to expand products of reflections $I-2P^0_{A_j}$ into sums of single product projections, and to write powers of the mismatch operator $\mathcal N_M$ as sums of projections $P^0_{M'|_F}$, where $M'$ is $M$ with every axis replaced by its orthogonal vector and $F=\{i_1,\dots,i_k\}$ runs over the coordinate sets of ordered monomials (repeated indices collapse).
--
--   **Formalization Note** The definitions are `Count.empty` (with the simp lemma `Count.empty_zero`), `Count.join` and `Count.restrict`; normalization on the new support is inherited from the inputs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Count.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Count.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RegularParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit__RegularParity

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


