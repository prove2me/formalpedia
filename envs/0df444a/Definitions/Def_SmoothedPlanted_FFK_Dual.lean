-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_Dual
-- name    : SmoothedPlanted_FFK_Dual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:32:48.773673+00:00
-- url     : https://prove2.me/theorems/a33de29b-75e4-41e6-87d8-d4933bac0611
-- title:
--   The dual SDP (D)
-- statement:
--   The dual variables are real $\alpha$, a real vector $\gamma$, nonnegative $\beta,\mu$, and a symmetric entrywise nonnegative matrix $N$. Its slack matrix has entries $Z_{00}=\alpha$, $Z_{0v}=Z_{v0}=-(\gamma_v+1)/2$, and $Z_{vw}=\mathbf1_{v=w}\gamma_v+\mathbf1_{v\ne w}\beta+\mu A_{vw}-N_{vw}$. Feasibility additionally requires $Z\succeq0$. These are precisely the entries of $\alpha E_{00}+\sum_v\gamma_vF_v+\beta\widetilde J+\mu\widetilde A-C_{\rm obj}-\widetilde N$. The dual objective used in Corollary 45 is $\alpha+\beta k(k-1)+2\mu\Delta$.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, The dual SDP (D), printed p. 29 (PDF p. 31), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_ThetaPrime

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

def adjacency {V : Type} (G : SimpleGraph V) : Matrix V V ℝ := by
  classical
  exact fun v w => if G.Adj v w then 1 else 0
/-- The entries of αE00 + ∑ γv Fv + βJtilde + μAtilde - Cobj - Ntilde. -/
def dualMatrix {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (α β μ : ℝ) (γ : V → ℝ) (N : Matrix V V ℝ) : Gram V
  | none, none => α
  | none, some v => -(γ v + 1) / 2
  | some v, none => -(γ v + 1) / 2
  | some v, some w => (if v = w then γ v else β) + μ * adjacency G v w - N v w
def dualFeasible {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (α β μ : ℝ) (γ : V → ℝ) (N : Matrix V V ℝ) : Prop :=
  0 ≤ β ∧ 0 ≤ μ ∧ N.IsSymm ∧ (∀ v w, 0 ≤ N v w) ∧
  (dualMatrix G α β μ γ N).PosSemidef

end SmoothedPlanted.FFK


