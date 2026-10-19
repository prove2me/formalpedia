-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Dual
-- name    : OAI_Probability_GaussianPropeller_Dual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:07:57.597498+00:00
-- url     : https://prove2.me/theorems/0a254c66-e852-47bd-9487-8bdc475a9889
-- title:
--   Score maxima, widths and optimal partitions
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   For $k$ vectors $v=(v_1,\dots,v_k)$ in $\mathbb R^d$, viewed as one vector of the Euclidean space of $k$-tuples:
--
--   1. **Score maximum and width.** $\max_i\langle v_i,x\rangle$, and its Gaussian average
--   $$
--   w(v)=\int\max_i\langle v_i,x\rangle\,d\gamma_d(x).
--   $$
--   2. **Score cells.** The set of $x$ where $\langle v_i,x\rangle$ is maximal, ties broken towards the smallest index; the closed cell drops the tie-break.
--   3. **Moments.** The tuple of centroids $(z(A_1),\dots,z(A_k))$ of a partition.
--   4. **Optimal partitions.** Partitions maximizing $\sum_i|z(A_i)|^2$ among all partitions into $k$ cells. The active labels are those $i$ with $\gamma_d(A_i)>0$, and a minimal optimal partition has the fewest active labels among optimal ones.
--   5. **Merging.** Replacing $A_i$ by $A_i\cup A_j$ and $A_j$ by $\varnothing$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Dual.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Dual.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianPropeller mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

abbrev Tuple (d k : ℕ) := PiLp 2 (fun _ : Fin k => Space d)

variable {d k : ℕ} [NeZero k]

noncomputable def scoreMax (v : Fin k → Space d) (x : Space d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)

noncomputable def width (v : Tuple d k) : ℝ := ∫ x, scoreMax v.ofLp x ∂gaussian d

def scoreCell (v : Fin k → Space d) (i : Fin k) : Set (Space d) :=
  {x | (∀ j, ⟪v j, x⟫ ≤ ⟪v i, x⟫) ∧ (∀ j, j < i → ⟪v j, x⟫ < ⟪v i, x⟫)}

noncomputable def moments (A : Fin k → Set (Space d)) : Tuple d k :=
  WithLp.toLp 2 (fun i => centroid (A i))

def Optimal (A : Fin k → Set (Space d)) : Prop :=
  IsPartition A ∧ ∀ B : Fin k → Set (Space d), IsPartition B → value B ≤ value A

noncomputable def activeLabels (A : Fin k → Set (Space d)) : Finset (Fin k) :=
  Finset.univ.filter (fun i => gaussian d (A i) ≠ 0)

noncomputable def activeCount (A : Fin k → Set (Space d)) : ℕ := (activeLabels A).card

def MinimalOptimal (A : Fin k → Set (Space d)) : Prop :=
  Optimal A ∧ ∀ B : Fin k → Set (Space d), Optimal B → activeCount A ≤ activeCount B

def merge (A : Fin k → Set (Space d)) (i j : Fin k) (l : Fin k) : Set (Space d) :=
  if l = i then A i ∪ A j else if l = j then ∅ else A l

def closedCell (z : Fin k → Space d) (i : Fin k) : Set (Space d) :=
  {x | ∀ j, ⟪z j, x⟫ ≤ ⟪z i, x⟫}

end Reduction

end GaussianPropeller

end OAI


