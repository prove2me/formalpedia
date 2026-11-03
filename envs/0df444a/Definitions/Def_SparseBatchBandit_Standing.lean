-- Prove2me | Definitions.Def_SparseBatchBandit_Standing
-- name    : SparseBatchBandit_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:33:05.575977+00:00
-- url     : https://prove2.me/theorems/dcc4d32f-43e6-4d9c-91cc-9b41fbc53083
-- title:
--   The standing hypotheses of §4
-- statement:
--   The hypotheses shared by the theorems of the mission on LBGL: the parameters are in the regime, the data follow Model-C, Assumptions 1 and 2 hold, the parameter satisfies $\|\theta^\star\|_2\le1$ and $\|\theta^\star\|_0\le s_0$, and `sel` is a measurable selection of Lasso minimizers.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §2.2, p.5; Theorem 2, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_ModelC
import Definitions.Def_SparseBatchBandit_Assumption1
import Definitions.Def_SparseBatchBandit_Assumption2
import Definitions.Def_SparseBatchBandit_Regime
import Definitions.Def_SparseBatchBandit_IsLassoSelector
import Definitions.Def_SparseBatchBandit_l0Norm
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
open MeasureTheory

namespace SparseBatchBandit

/-- The standing package of Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §4 (p.16, PDF 16): Model-C, Assumptions 1–4, `M = O(log log(T/s₀))`
through `Regime`, a parameter with `‖θ⋆‖₂ ≤ 1` and `‖θ⋆‖₀ ≤ s₀`, and a measurable selection `sel` of
Lasso minimizers. Every theorem of the mission on LBGL holds under this package. -/
structure Standing (A ε β : ℝ) (p : ℕ) {Ω : Type*} [MeasurableSpace Ω] {T d K M s₀ : ℕ} [NeZero K]
    (γ ρ : ℝ) (P : Measure Ω) (x : Ω → Fin T → Fin K → Fin d → ℝ) (ξ : Ω → Fin T → ℝ)
    (θstar : Fin d → ℝ) (sel : LassoSelector T s₀ M d) : Prop where
  /-- the parameters are in the regime of Theorem 2 -/
  regime : Regime A ε β p T d K M s₀ γ ρ
  /-- Model-C -/
  model : ModelC P x ξ
  /-- Assumption 1 -/
  assumption1 : Assumption1 P x
  /-- Assumption 2 -/
  assumption2 : Assumption2 P x γ ρ
  /-- `‖θ⋆‖₂ ≤ 1` -/
  theta_l2 : HighDimProb.SparseRecovery.l2Norm θstar ≤ 1
  /-- `‖θ⋆‖₀ ≤ s₀` -/
  theta_l0 : l0Norm θstar ≤ s₀
  /-- `sel` selects Lasso minimizers measurably -/
  selector : IsLassoSelector K sel

end SparseBatchBandit


