-- Prove2me | Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model
-- name    : LeeSviridenkoVondrak_LocalSearch_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:01.11272+00:00
-- url     : https://prove2.me/theorems/29f0df7b-5621-430d-b092-e0647bcda8a1
-- title:
--   Finite objective, common feasibility, and local search predicates
-- statement:
--   Let $N=\{0,\ldots,n-1\}$ and let $M_j$ be $k$ matroids on $N$. The objective $f$ is defined on every subset. Nonnegativity and nondecreasingness are separate predicates, with no normalization at the empty set. Common independence means independence in every matroid. The optimum is the maximum value on common independent sets, a finite nonempty family. A $p$-neighbor $T$ of $S$ is common independent with $|T\setminus S|\le 2p$ and $|S\setminus T|\le 2kp$. Exact local optimality requires feasible $S$ and $f(T)\le f(S)$ for all such neighbors. The literal Figure 1 terminal predicate instead requires
--   $$f(T)<\left(1+\frac{\varepsilon}{n(k+1)}\right)f(S).$$
--   Indexed families may repeat subsets; multiplicity counts indices containing the specified element.
--
--   **Formalization Note** The mathematical model permits $n=0$. At $n=0$ the strict terminal predicate is unsatisfiable; the headline algorithm handles the empty ground set separately. The real supremum defining the optimum is attained because its value set is finite and contains $f(\varnothing)$. These utility predicates are defined for arbitrary Mathlib matroid ground subsets; each source theorem separately requires every ground set to equal the full type.
-- source:
--   Lee, Sviridenko and Vondrák (2010), Submodular Maximization over Multiple Matroids via Generalized Exchange Properties, Mathematics of Operations Research 35(4), 795–806, https://doi.org/10.1287/moor.1100.0463; introduction p. 795 / PDF 1 and §3 pp. 801–803 / PDF 7–9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace LeeSviridenkoVondrak.LocalSearch

/-- Finite ground set, nonnegative objectives and common matroid feasibility.
Lee–Sviridenko–Vondrák (2010), pp. 795, 801, 803. No normalization is imposed. -/
def Nonnegative {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop := ∀ A, 0 ≤ f A

def Nondecreasing {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ A B, A ⊆ B → f A ≤ f B

def CommonIndependent {n k : ℕ} (M : Fin k → Matroid (Fin n))
    (S : Finset (Fin n)) : Prop := ∀ j, (M j).Indep (↑S : Set (Fin n))

/-- The feasible value set is finite and contains f ∅, since ∅ is independent.
This supremum is the attained finite maximum, including when n = 0 or k = 0. -/
noncomputable def optimum {n k : ℕ} (f : Finset (Fin n) → ℝ)
    (M : Fin k → Matroid (Fin n)) : ℝ :=
  sSup {v | ∃ S : Finset (Fin n), CommonIndependent M S ∧ v = f S}

def PNeighbor {n k : ℕ} (M : Fin k → Matroid (Fin n)) (p : ℕ)
    (S T : Finset (Fin n)) : Prop :=
  CommonIndependent M T ∧ (T \ S).card ≤ 2 * p ∧ (S \ T).card ≤ 2 * k * p

def ExactLocalOptimum {n k : ℕ} (f : Finset (Fin n) → ℝ)
    (M : Fin k → Matroid (Fin n)) (p : ℕ) (S : Finset (Fin n)) : Prop :=
  CommonIndependent M S ∧ ∀ T, PNeighbor M p S T → f T ≤ f S

/-- The literal no-move condition of Figure 1: the update is ≥, so stopping is <.
At n = 0 Lean's quotient is 0; no feasible S can satisfy this strict condition.
The headline algorithm handles empty and zero-value inputs separately. -/
def ApproxLocalOptimum {n k : ℕ} (f : Finset (Fin n) → ℝ)
    (M : Fin k → Matroid (Fin n)) (p : ℕ) (ε : ℝ) (S : Finset (Fin n)) : Prop :=
  CommonIndependent M S ∧ ∀ T, PNeighbor M p S T →
    f T < (1 + ε / ((n : ℝ) * ((k : ℝ) + 1))) * f S

/-- Incidence counts count indices, so families may contain repeated or empty sets. -/
def multiplicity {n m : ℕ} (A : Fin m → Finset (Fin n)) (x : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => x ∈ A i)).card

end LeeSviridenkoVondrak.LocalSearch


