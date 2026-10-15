-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
-- name    : OAI_InformationTheory_QuantumCircuit_Spectral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:14:04.873035+00:00
-- url     : https://prove2.me/theorems/28aad33b-4395-4f50-941c-a8ef00ded3f4
-- title:
--   Functional calculus of a mismatch count and ordered monomial supports
-- statement:
--   Let $M$ be a count on $N$ qubits with support $S$. Its pattern projections $\Pi^M_F$ ($F\subseteq S$) are mutually orthogonal projections summing to $I$, and on the range of $\Pi^M_F$ the mismatch operator $\widehat M$ acts as the integer $|F|$. The file defines:
--
--   1. **Low projection.** For $r\in\mathbb{R}$, $\Pi^M_{<r}=I-\Pi^M_{\ge r}$, the spectral projection onto fewer than $r$ mismatches.
--
--   2. **Spectral function of the count.** For $f:\mathbb{N}\to\mathbb{R}$,
--   $$
--   f(\widehat M)=\sum_{F\subseteq S}f(|F|)\,\Pi^M_F .
--   $$
--
--   3. **Polynomial of the count.** For a real polynomial $p$, $p(\widehat M)$ is the spectral function with $f(k)=p(k)$.
--
--   4. **Selection sets.** For a finite set $S$ (listed in a fixed order) and $k\in\mathbb{N}$, $\mathrm{Sel}(S,k)$ is the list of subsets of $S$ given by $\mathrm{Sel}(S,0)=[\varnothing]$ and, for $k+1$, the concatenation over $i\in S$ of the lists obtained from $\mathrm{Sel}(S,k)$ by inserting $i$ into each set. Thus $\mathrm{Sel}(S,k)$ lists the sets $\{i_1,\dots,i_k\}$ for all $|S|^k$ ordered tuples $(i_1,\dots,i_k)\in S^k$, keeping multiplicities and collapsing repeated indices.
--
--   The spectral calculus turns statements about a count into statements about real functions on $\{0,1,\dots,N\}$: for instance $\Pi^M_0=\mathbf 1_{\{0\}}(\widehat M)$, $\Pi^M_{\ge r}=\mathbf 1_{[r,\infty)}(\widehat M)$, and $p(\widehat M)$ agrees with the polynomial $p$ evaluated at the operator $\widehat M$. Selection sets index the expansion of $\widehat M^{\,k}$ into $|S|^k$ product projections with support of size at most $k$, which is what makes low-degree polynomials of a count cheap to propagate through a circuit.
--
--   **Formalization Note** The Lean names are `Count.low`, `Count.spectral`, `Count.polynomial` and `selectionSets`; the order on $S$ is that of `S.toList`. The identities in the last paragraph are proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Spectral.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Spectral.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count

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


