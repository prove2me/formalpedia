-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
-- name    : OAI_Probability_GaussianPropeller_Deletion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:08:43.238652+00:00
-- url     : https://prove2.me/theorems/2c51ecfb-bbb1-40e0-ba2e-c0c9f6a9dbe1
-- title:
--   Omitted maxima and recentred score vectors
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   For $k\ge2$ vectors $z_1,\dots,z_k$ and an index $i$:
--
--   1. **Omitted maximum.** $\max_{j\ne i}\langle z_j,x\rangle$, the score maximum with the $i$-th vector removed.
--   2. **Recentred tuple.** The tuple obtained by deleting $z_i$ and spreading it evenly over the others:
--   $$
--   z'_j=\begin{cases}0,&j=i,\\ z_j+\dfrac{z_i}{k-1},&j\ne i.\end{cases}
--   $$
--   These compare an optimal partition with the partition obtained by deleting one cell, which yields a lower bound on the loss caused by a deletion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Deletion.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Deletion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianPropeller mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open scoped RealInnerProductSpace

namespace GaussianPropeller.Reduction

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
lemma erase_univ_nonempty (hk : 2 ≤ k) (i : Fin k) :
    (Finset.univ.erase i).Nonempty := by
  classical
  apply Finset.card_pos.mp
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

noncomputable def omittedMax (hk : 2 ≤ k) (z : Fin k → Space d)
    (i : Fin k) (x : Space d) : ℝ :=
  (Finset.univ.erase i).sup' (erase_univ_nonempty hk i) (fun j => ⟪z j,x⟫)

noncomputable def recentered (z : Fin k → Space d) (i : Fin k) : Tuple d k :=
  WithLp.toLp 2 (fun j => if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i)

end GaussianPropeller.Reduction

end OAI


