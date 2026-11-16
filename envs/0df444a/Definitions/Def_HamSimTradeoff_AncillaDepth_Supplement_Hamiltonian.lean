-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Hamiltonian
-- name    : HamSimTradeoff_AncillaDepth_Supplement_Hamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:47:07.865546+00:00
-- url     : https://prove2.me/theorems/ba1ac2a3-1a42-4fa7-8479-a76d38aa8e8d
-- title:
--   The normalized Hermitian class (4.1)
-- statement:
--   For a finite family of $d\times d$ complex matrices $H_j$, the unweighted Hamiltonian class requires each $H_j$ Hermitian and
--   $$\sum_j\|H_j\|\le1,\qquad A=\sum_jH_j.$$
--   The norm is spectral. The base Suzuki formula is used with weights identically one. The predicate HamiltonianApprox demands the success-block error uniformly over every number of terms, every positive system dimension, every such family and every real $|t|\le1$. The circuit is chosen before all of these inputs. The ancilla count is $\operatorname{clog}_2m=\lceil\log_2m\rceil$ for $m\ge2$.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 20, Eq. (4.1); p. 21, Theorem 4.2

import Definitions.Def_HamSimTradeoff_AncillaDepth_Architecture
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

/-- The unweighted class (4.1), without involution or positive-weight assumptions. -/
def HamiltonianClass {L d : ℕ} (H : Fin L → Mat d) : Prop :=
  (∀ j, (H j).IsHermitian) ∧ ∑ j, ‖H j‖ ≤ 1

def roundAncillas (m : ℕ) : ℕ := Nat.clog 2 m

def HamiltonianApprox (B : Architecture) (eps : ℝ) : Prop :=
  ∀ L d : ℕ, 1 ≤ d → ∀ H : Fin L → Mat d, HamiltonianClass H →
    ∀ t : ℝ, |t| ≤ 1 →
      ‖compression B (fun _ => 1) H t - eta B • evolution (∑ j, H j) t‖ ≤ eps

end
end HamSimTradeoff.AncillaDepth.Supplement


