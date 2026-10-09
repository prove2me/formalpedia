-- Prove2me | Definitions.Def_RobustOdds_SVM_Setting
-- name    : RobustOdds_SVM_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:27.668017+00:00
-- url     : https://prove2.me/theorems/aaf628bd-6ba9-446c-be72-52155f822c91
-- title:
--   Model (3), objectives (1), (2), (5), and classification accuracies
-- statement:
--   Let the label $y$ be uniform on $\{-1,+1\}$. Conditional on $y$, the first coordinate equals $y$ with probability $p$ and $-y$ with probability $1-p$; the remaining $d$ coordinates are independent $\mathcal N(y\eta,1)$ variables, independent of the first coordinate. This defines the conditional input laws $D_y$ and their balanced mixture $D$.
--
--   For a classifier $f$, its **standard accuracy** is $\Pr_D(f(x)=y)$ and its **robust accuracy** at radius $\varepsilon$ is $\Pr_D(\forall\delta,\ \|\delta\|_\infty\le\varepsilon\Rightarrow f(x+\delta)=y)$. The linear classifier $f_w$ predicts the sign of $\sum_iw_ix_i$. Its hinge loss is $\max\{0,1-y\sum_iw_ix_i\}$, and the soft-margin SVM objective is
--
--   $$
--   J_\lambda(w)=\mathbb E_D\left[\max\{0,1-yw^\top x\}\right]+\frac{\lambda}{2}\sum_iw_i^2.
--   $$
--
--   The adversarial objective replaces the hinge term by its maximum over $\|\delta\|_\infty\le\varepsilon$ **for each sample**, then takes expectation. These definitions connect the paper's classification model to its two optimization problems.
--
--   **Formalization Note** Inputs are functions on $\mathrm{Fin}(d+1)$, with coordinate zero representing $x_1$. Their function norm is $\ell_\infty$; weight $\ell_2^2$ and $\ell_1$ are explicit sums. A zero linear score is assigned label $-1$. The robust event is evaluated by outer measure, which agrees with completed probability. For negative training radius the adversarial supremum has an empty index type; theorem statements using it require a nonnegative radius.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, pp. 2, 4, 16, equations (1)–(3), (5) and App. D

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

namespace RobustOdds.SVM

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Sign of a linear score, with zero assigned label −1. -/
noncomputable def linClf {d : ℕ} (w : Fin (d + 1) → ℝ) :
    (Fin (d + 1) → ℝ) → ℝ :=
  fun x => if 0 < ∑ i, w i * x i then 1 else -1

/-- Hinge loss of a linear score on one labelled input. -/
noncomputable def hingeLoss {d : ℕ} (w : Fin (d + 1) → ℝ)
    (x : Fin (d + 1) → ℝ) (y : ℝ) : ℝ :=
  max 0 (1 - y * ∑ i, w i * x i)

/-- The expected hinge loss in the balanced two-class model. -/
noncomputable def marginLoss (d : ℕ) (p η : ℝ) (w : Fin (d + 1) → ℝ) : ℝ :=
  (1 / 2) * ∫ x, hingeLoss w x 1 ∂(RobustOdds.Tradeoff.condLaw d p η 1) +
    (1 / 2) * ∫ x, hingeLoss w x (-1) ∂(RobustOdds.Tradeoff.condLaw d p η (-1))

/-- Soft-margin SVM objective (5). -/
noncomputable def svmObj (d : ℕ) (p η lam : ℝ) (w : Fin (d + 1) → ℝ) : ℝ :=
  marginLoss d p η w + (1 / 2) * lam * ∑ i, w i ^ 2

/-- The per-sample worst-case hinge loss over an ℓ∞ ball. -/
noncomputable def advHingeLoss {d : ℕ} (ε : ℝ) (w : Fin (d + 1) → ℝ)
    (x : Fin (d + 1) → ℝ) (y : ℝ) : ℝ :=
  ⨆ δ : {δ : Fin (d + 1) → ℝ // ‖δ‖ ≤ ε}, hingeLoss w (x + δ.val) y

/-- Distributional adversarial hinge loss (2): the maximum is inside expectation. -/
noncomputable def advMarginLoss (d : ℕ) (p η ε : ℝ)
    (w : Fin (d + 1) → ℝ) : ℝ :=
  (1 / 2) * ∫ x, advHingeLoss ε w x 1 ∂(RobustOdds.Tradeoff.condLaw d p η 1) +
    (1 / 2) * ∫ x, advHingeLoss ε w x (-1) ∂(RobustOdds.Tradeoff.condLaw d p η (-1))

/-- The regularized distributional adversarial objective. -/
noncomputable def advObj (d : ℕ) (p η ε lam : ℝ)
    (w : Fin (d + 1) → ℝ) : ℝ :=
  advMarginLoss d p η ε w + (1 / 2) * lam * ∑ i, w i ^ 2

end RobustOdds.SVM


