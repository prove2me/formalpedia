-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Spectral__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:41:26.716438+00:00
-- url     : https://prove2.me/theorems/a5625121-85a2-45f7-9671-7ae25f354318
-- title:
--   Spectral calculus of the mismatch count and ordered monomial supports
-- statement:
--   Let $M=(S,v)$ be a count on $N$ qubits with pattern projections $P_M^F$ and high projections $[\mathcal N_M\ge r]=\sum_{F\subseteq S,\,|F|\ge r}P_M^F$. This file defines functions of the mismatch count through its explicit spectral decomposition, and an enumeration of the supports of ordered monomials.
--
--   1. **Low projection.** For $r\in\mathbb R$, $[\mathcal N_M<r]=I-[\mathcal N_M\ge r]$.
--   2. **Spectral calculus.** For $f:\mathbb N\to\mathbb R$,
--   $$
--   f(\mathcal N_M)=\sum_{F\subseteq S} f(|F|)\,P_M^F .
--   $$
--   3. **Polynomials of the count.** For a real polynomial $p$, $p(\mathcal N_M)$ is item 2 with $f(k)=p(k)$.
--   4. **Ordered monomial supports.** For a finite set $S$, listed in a fixed order as $(s_1,\dots,s_m)$, define lists of finite sets by $\Sigma_0(S)=(\varnothing)$ and
--   $$
--   \Sigma_{k+1}(S)=\bigl(\{s_1\}\cup G\bigr)_{G\in\Sigma_k(S)}\ \mathbin{+\!\!+}\ \cdots\ \mathbin{+\!\!+}\ \bigl(\{s_m\}\cup G\bigr)_{G\in\Sigma_k(S)} ,
--   $$
--   where $\mathbin{+\!\!+}$ is list concatenation. Thus $\Sigma_k(S)$ lists the coordinate sets $\{i_1,\dots,i_k\}$ of all ordered $k$-tuples $(i_1,\dots,i_k)\in S^k$, with multiplicity ($|S|^k$ entries), repeated coordinates being collapsed.
--
--   Because the patterns $P_M^F$ are mutually orthogonal projections summing to the identity, item 2 is the functional calculus of the mismatch operator $\mathcal N_M$ (whose eigenvalue on the range of $P_M^F$ is $|F|$), and $p(\mathcal N_M)$ agrees with substituting $\mathcal N_M$ into $p$. Item 4 indexes the expansion of $\mathcal N_M^k$ as a sum of $|S|^k$ product projections, each supported on at most $k$ qubits; this is what lets a low-degree polynomial in $\mathcal N_M$ be handled by bounds for product projections of small support.
--
--   **Formalization Note** The definitions are `Count.low`, `Count.spectral`, `Count.polynomial` and `selectionSets`; the fixed order in item 4 is `Finset.toList`. The identification with the usual functional calculus is proved in the solution file, not here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Spectral.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Spectral.lean by skeleton subtraction
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

-- Lean 4.34 name of List.sum_le_card_nsmul (same statement) in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

def Count.low {N : ℕ} (M : Count N) (r : ℝ) : Operator N := 1 - M.high r

def Count.spectral {N : ℕ} (M : Count N) (f : ℕ → ℝ) : Operator N :=
  ∑ F ∈ M.support.powerset, f F.card • M.pattern F

/-- Evaluate a real polynomial using the explicit integer spectral decomposition. -/
def Count.polynomial {N : ℕ} (M : Count N) (p : Polynomial ℝ) : Operator N :=
  M.spectral (fun k => p.eval (k:ℝ))

/-- Ordered monomials, retaining multiplicities, with repeated coordinates collapsed. -/
def selectionSets {ι : Type*} [DecidableEq ι] (S : Finset ι) : ℕ → List (Finset ι)
  | 0 => [∅]
  | k+1 => S.toList.flatMap (fun i => (selectionSets S k).map (insert i))

end QAC

end

end OAI


