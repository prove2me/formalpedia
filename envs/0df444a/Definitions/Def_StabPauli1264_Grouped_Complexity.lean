-- Prove2me | Definitions.Def_StabPauli1264_Grouped_Complexity
-- name    : StabPauli1264_Grouped_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:47.753932+00:00
-- url     : https://prove2.me/theorems/10ea6d14-cf60-4829-92ba-8b7bc0c250a5
-- title:
--   Worst-distribution copy minima and the collective hard targets
-- statement:
--   For a fixed nonempty window $M$, grouped attainability at copy count $N$ means that for every known real evaluation law $p$ there is a permitted grouped procedure, chosen before $\rho$, whose success probability is at least $1-\delta$ for every density matrix $\rho$. Collective attainability uses arbitrary proper collective POVMs. Their least feasible copy counts are $N_{\rm grouped}(M,\varepsilon,\delta)$ and $N_{\rm coll}(M,\varepsilon,\delta)$, with infinity when no count is feasible.
--
--   For cutoffs $0<\varepsilon_0,\delta_0<1/2$, define
--
--   $$a=1+\frac1{2\varepsilon_0},\quad \bar\mu=\varepsilon_0+\frac12,\quad A=(1-2\delta_0)\left(1+\frac{\ln(1-\delta_0)}{\ln(1/\delta_0)}\right),$$
--   $$B=\frac{(1-\bar\mu^2)A}{2a^2},\qquad C=16+\frac{8c_0^2+\varepsilon_0^2+2\varepsilon_0}{\ln(1/\delta_0)}.$$
--
--   For any coordinate $i$ and accuracy $\varepsilon$, the literal hard targets are $\rho_\pm=2^{-n}(I\pm a\varepsilon P_i)$. Their being normalized physical stabilizer mixtures is a theorem conclusion. These quantities expose the constants in the minimax comparison; none depends on the window or individual accuracy and confidence parameters.
--
--   **Formalization Note** Complexity values are extended naturals. The order-preserving conversion to extended nonnegative reals is used for real-valued bounds, preserving infinity. The universal quantifier over $p$ precedes existence of a learner; the universal quantifier over $\rho$ follows it. No success property is a field of either procedure.
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), §1.1 p. 4; Theorem 2.3 p. 6; §7 Eqs. (25),(26),(30),(31), pp. 16–17; §8.2 p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Estimation
set_option autoImplicit false

namespace StabPauli1264.Grouped

open QAlgorithms.Stabilizer
open scoped BigOperators Classical ENNReal

/-- The family is chosen after p and before the unknown density matrix. -/
def GroupedAchievable {n m : ℕ} (M : Window n m) (ε δ : ℝ) (N : ℕ) : Prop :=
  ∀ p : EvalLaw m, ∃ A : GroupedProcedure n m N, GroupedPermitted M A ∧
    ∀ ρ : Density n, 1 - δ ≤ groupedSuccess M p A ρ.matrix ε

def CollectiveAchievable {n m : ℕ} (M : Window n m) (ε δ : ℝ) (N : ℕ) : Prop :=
  ∀ p : EvalLaw m, ∃ A : CollectiveProcedure n N,
    ∀ ρ : Density n, 1 - δ ≤ collectiveSuccess M p A ρ.matrix ε

/-- Extended natural infima; empty feasible sets give infinity. Nonempty sets attain their minimum. -/
noncomputable def groupedComplexity {n m : ℕ} (M : Window n m) (ε δ : ℝ) : ℕ∞ :=
  sInf {K | ∃ N : ℕ, K = (N : ℕ∞) ∧ GroupedAchievable M ε δ N}

noncomputable def collectiveComplexity {n m : ℕ} (M : Window n m) (ε δ : ℝ) : ℕ∞ :=
  sInf {K | ∃ N : ℕ, K = (N : ℕ∞) ∧ CollectiveAchievable M ε δ N}

/-- Order embedding used only to compare extended copy counts with real bounds. -/
noncomputable def countReal (N : ℕ∞) : ℝ≥0∞ :=
  if N = ⊤ then ⊤ else (N.toNat : ℝ≥0∞)

noncomputable def lowerA (ε₀ : ℝ) : ℝ := 1 + 1 / (2 * ε₀)
noncomputable def muBar (ε₀ : ℝ) : ℝ := ε₀ + 1 / 2
noncomputable def confidenceA (δ₀ : ℝ) : ℝ :=
  (1 - 2 * δ₀) * (1 + Real.log (1 - δ₀) / Real.log (1 / δ₀))
noncomputable def lowerConstant (ε₀ δ₀ : ℝ) : ℝ :=
  (1 - muBar ε₀ ^ 2) * confidenceA δ₀ / (2 * lowerA ε₀ ^ 2)
noncomputable def upperConstant (ε₀ δ₀ : ℝ) : ℝ :=
  16 + (8 * c0 ^ 2 + ε₀ ^ 2 + 2 * ε₀) / Real.log (1 / δ₀)

noncomputable def hardTarget {n m : ℕ} (M : Window n m) (i : Fin m)
    (ε₀ ε : ℝ) (positiveSign : Bool) : Mat n :=
  ((2 : ℂ) ^ n)⁻¹ • (1 + ((if positiveSign then 1 else -1) * lowerA ε₀ * ε : ℝ) •
    operator M i)

end StabPauli1264.Grouped


