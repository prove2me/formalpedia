-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
-- name    : OAI_InformationTheory_QuantumCircuit_Reflection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:15:53.549976+00:00
-- url     : https://prove2.me/theorems/8b322323-7d8d-4497-bb27-6b74fae26b96
-- title:
--   Reflections about product projections and their signed product expansion
-- statement:
--   Let $N$ be a number of qubits, and for a count $D$ write $\Pi^D_0$ for its zero projection. The file defines:
--
--   1. **Reflection.** $\mathrm{refl}(D)=I-2\,\Pi^D_0$, which acts as $-1$ on the range of $\Pi^D_0$ and as $+1$ on its orthogonal complement; it is self-adjoint and unitary.
--
--   2. **Product of reflections.** For a list $l=(A_1,\dots,A_m)$ of counts, $\mathrm{refl}(l)=\mathrm{refl}(A_1)\,\mathrm{refl}(A_2)\cdots\mathrm{refl}(A_m)$.
--
--   3. **Active sub-layer.** For a reflection layer $R$ and a count $A$, $R_A$ is the reflection layer formed by the gates of $R$ (in their order) whose support meets the support of $A$.
--
--   4. **Reflection terms.** A list $T(l)$ of pairs (real coefficient, count), defined recursively by $T([\,])=[(1,\varnothing_N)]$ and
--   $$
--   T(A::l)=T(l)\ \text{++}\ \bigl[(-2c,\ A\vee B)\ :\ (c,B)\in T(l)\bigr],
--   $$
--   where $\varnothing_N$ is the empty count, $A\vee B$ the join of counts and $\text{++}$ concatenation of lists. For $l=(A_1,\dots,A_m)$ the list has $2^m$ entries, one for each $J\subseteq\{1,\dots,m\}$, with coefficient $(-2)^{|J|}$ and the join of the $A_j$, $j\in J$ (the empty count for $J=\varnothing$).
--
--   When the supports in $l$ are pairwise disjoint, multiplying out the product gives
--   $$
--   \mathrm{refl}(l)=\sum_{(c,B)\in T(l)}c\,\Pi^B_0,\qquad \sum_{(c,B)\in T(l)}|c|=3^{m},
--   $$
--   so a reflection layer is a signed combination of product projections with total coefficient weight $3^m$. Conjugating a product projection $\Pi_0^A$ by a reflection layer only involves the active gates, of which there are at most $|\operatorname{supp}A|$. These two facts produce the factor $9^{|\operatorname{supp}A|}$ when a localization estimate is pushed through one more layer of depth.
--
--   **Formalization Note** The Lean names are `reflect`, `reflectList`, `ReflectionLayer.active` and `reflectionTerms`. In `reflect` the coefficient $2$ is a real scalar acting on complex matrices; for a reflection layer `R` the matrix `reflectionMatrix R` equals `reflectList R.gates`. The identities in the last paragraph are proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Reflection.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Reflection.lean by skeleton subtraction
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


