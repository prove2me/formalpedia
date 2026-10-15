-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Reflection__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:04:00.996898+00:00
-- url     : https://prove2.me/theorems/01845b08-958b-47d6-856c-c9a9baf05dfe
-- title:
--   Reflections about product projections and the expansion of their products
-- statement:
--   This file defines reflections about product projections and the bookkeeping needed to expand a layer of such reflections. For a count $D$ on $N$ qubits, $P_D^0$ denotes its zero-mismatch product projection, and $A\vee B$ denotes the join of two counts (union of supports, axes of $A$ taking precedence).
--
--   1. **Reflection.** $R_D=I-2\,P_D^0$.
--   2. **Product of reflections.** For a list $(A_1,\dots,A_m)$ of counts, $R_{(A_1,\dots,A_m)}=R_{A_1}R_{A_2}\cdots R_{A_m}$ (the identity for the empty list).
--   3. **Active sublayer.** For a reflection layer $\mathcal R=(D_1,\dots,D_m)$ (counts with pairwise disjoint supports) and a count $A$, the sublayer $\mathcal R|_A$ keeps, in their original order, exactly those $D_j$ whose support meets the support of $A$; it is again a reflection layer.
--   4. **Expansion terms.** A list $\mathcal T(l)$ of pairs (real coefficient, count) is defined by recursion on the list $l$:
--   $$
--   \mathcal T(\,)=\bigl((1,\varnothing)\bigr),\qquad \mathcal T(A,l)=\mathcal T(l)\ \mathbin{+\!\!+}\ \bigl((-2c,\ A\vee B)\bigr)_{(c,B)\in\mathcal T(l)} .
--   $$
--   For $l=(A_1,\dots,A_m)$ it has $2^m$ entries, one for each $J\subseteq\{1,\dots,m\}$, with coefficient $(-2)^{|J|}$ and count $\bigvee_{j\in J}A_j$.
--
--   When the supports of $A_1,\dots,A_m$ are pairwise disjoint, the projections $P^0_{A_j}$ commute and multiply to joins, so $R_{(A_1,\dots,A_m)}=\sum_{(c,B)\in\mathcal T}c\,P_B^0$ with total coefficient weight $\sum|c|=3^m$; the active sublayer shows that only the reflections touching the support of $A$ affect $R\,P_A^0\,R^{\ast}$. These two facts bound the cost of passing one reflection layer by $9^{|\operatorname{supp}A|}$ in the localization argument. A Toffoli gate is exactly such a reflection.
--
--   **Formalization Note** The definitions are `reflect`, `reflectList`, `ReflectionLayer.active` and `reflectionTerms`. The scalar $2$ in `reflect` is a real scalar acting on the complex matrix. The file also contains an empty section.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Reflection.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Reflection.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

/-- The real scalar spelling makes the coefficient budget transparent. -/
def reflect {N : ℕ} (D : Count N) : Operator N := 1 - (2:ℝ) • D.zero

def reflectList {N : ℕ} (l : List (Count N)) : Operator N := (l.map reflect).prod

def ReflectionLayer.active {N : ℕ} (R : ReflectionLayer N) (A : Count N) : ReflectionLayer N where
  gates := R.gates.filter (fun D => decide (¬Disjoint D.support A.support))
  disjoint := R.disjoint.filter _

/-- Expansion of a disjoint reflection product.  The real coefficients carry
all multiplicities; no commutation of the middle projection is required. -/
def reflectionTerms {N : ℕ} : List (Count N) → List (ℝ × Count N)
  | [] => [(1,Count.empty)]
  | A::l => reflectionTerms l ++ (reflectionTerms l).map (fun p => (-2*p.1,A.join p.2))

section BilinearBudget
variable {A : Type*} [CStarAlgebra A]

end BilinearBudget

end QAC

end

end OAI


