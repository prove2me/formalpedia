-- Prove2me | Definitions.Def_RobustOdds_Tradeoff_Setting
-- name    : RobustOdds_Tradeoff_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:23.096976+00:00
-- url     : https://prove2.me/theorems/abc30cfd-9612-49b7-a2d1-54ff78c8fb15
-- title:
--   (3), (1)–(2), App. C, pp. 2, 4, 14–16 — the distribution D, standard and ℓ∞ robust accuracy, p_ij and the shift adversary
-- statement:
--   This file fixes the objects in which Theorem 2.1 of Tsipras, Santurkar, Engstrom, Turner and Mądry is stated and proved.
--
--   **The data model (3).** Fix $d \in \mathbb N$, $p \in \mathbb R$ and $\eta \in \mathbb R$. An input-label pair $(x, y)$, $x = (x_1, x_2, \dots, x_{d+1}) \in \mathbb R^{d+1}$, is drawn from the distribution $\mathcal D$ as follows: the label $y$ is uniform on $\{-1, +1\}$; given $y$, the **robust feature** $x_1$ equals $+y$ with probability $p$ and $-y$ with probability $1-p$; independently, the **weak features** $x_2, \dots, x_{d+1}$ are i.i.d. $\mathcal N(\eta y, 1)$. Write
--
--   1. $\mu_y^{(1)} = p\,\delta_y + (1-p)\,\delta_{-y}$ for the law of $x_1$ given $y$;
--   2. $G_y = \mathcal N(\eta y, 1)^{\otimes d}$ for the law of $(x_2, \dots, x_{d+1})$ given $y$; the paper calls $G_{+1}$ and $G_{-1}$ $G_+$ and $G_-$;
--   3. $\mathcal D_y = \mu_y^{(1)} \otimes G_y$ for the law of $x$ given $y$.
--
--   **Accuracies.** For a classifier $f : \mathbb R^{d+1} \to \{-1, +1\}$ and $\varepsilon \in \mathbb R$, the standard accuracy (objective (1) with the 0–1 loss) and the $\ell_\infty$ robust accuracy (objective (2) with the 0–1 loss and $\Delta = \{\delta : \|\delta\|_\infty \le \varepsilon\}$) are
--
--   $$\mathrm{acc}(f) = \tfrac12\,\mathcal D_{+1}[f(x) = 1] + \tfrac12\,\mathcal D_{-1}[f(x) = -1],$$
--
--   $$\mathrm{acc}_\varepsilon(f) = \tfrac12\,\mathcal D_{+1}\big[\forall \delta,\ \|\delta\|_\infty \le \varepsilon \Rightarrow f(x+\delta) = 1\big] + \tfrac12\,\mathcal D_{-1}\big[\forall \delta,\ \|\delta\|_\infty \le \varepsilon \Rightarrow f(x+\delta) = -1\big].$$
--
--   **The quantities of App. C.** For $i, j \in \{-1, +1\}$, $p_{ij} = G_j\big[\{z : f(i, z) = 1\}\big]$ is the probability that $f$ predicts $+1$ when $x_1 = i$ and the weak features follow $G_j$. The **shift adversary** with label $y$ maps $x$ to $x_{\mathrm{adv}}$ with $(x_{\mathrm{adv}})_1 = x_1$ and $(x_{\mathrm{adv}})_i = x_i - 2\eta y$ for $i \ge 2$, and the accuracy against it is
--
--   $$\mathrm{acc}_{\mathrm{adv}}(f) = \tfrac12\,\mathcal D_{+1}[f(x_{\mathrm{adv}}) = 1] + \tfrac12\,\mathcal D_{-1}[f(x_{\mathrm{adv}}) = -1].$$
--
--   These are the objects of Theorem 2.1 and of every step of its proof.
--
--   **Formalization Note** $\mathbb R^{d+1}$ is `Fin (d + 1) → ℝ`, whose Mathlib norm is the sup norm, so `‖δ‖ ≤ ε` is exactly the $\ell_\infty$ ball. Coordinate `0` is $x_1$ and coordinate `i.succ` is $x_{i+2}$. Labels and predictions are the reals $\pm 1$. The weights $p$, $1-p$ enter through `ENNReal.ofReal`; the theorems assume $\tfrac12 \le p \le 1$ (the paper's standing $p \ge 0.5$). `gaussianReal μ v` takes the variance. Accuracies are real numbers obtained with `toReal`. The robust event need not be measurable; the measure of it is its outer measure, which is its probability under the completion of $\mathcal D_y$.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, pp. 2, 4, 14–16, objectives (1)–(2), data model (3), App. C (G±, p_ij, the shift adversary)

import Mathlib

namespace RobustOdds.Tradeoff

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The law of the robust feature `x₁` given the label `y` (data model (3), p. 4):
`x₁ = +y` with probability `p` and `x₁ = −y` with probability `1 − p`. -/
noncomputable def x1Law (p y : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac y + ENNReal.ofReal (1 - p) • Measure.dirac (-y)

/-- The law of the weak features `x₂, …, x_{d+1}` given the label `y` (data model (3), p. 4):
i.i.d. `N(ηy, 1)`. `weakLaw d η 1` is the paper's `G₊`, `weakLaw d η (-1)` is `G₋`.
(`gaussianReal μ v` takes the variance `v`.) -/
noncomputable def weakLaw (d : ℕ) (η y : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => gaussianReal (y * η) 1

/-- The class-conditional law of the input `x = (x₁, x₂, …, x_{d+1}) ∈ ℝ^{d+1}` given the label `y`
(data model (3), p. 4): `x₁` and the weak features are independent given `y`. Coordinate `0` is the
paper's `x₁` and coordinate `i.succ` is `x_{i+2}`. -/
noncomputable def condLaw (d : ℕ) (p η y : ℝ) : Measure (Fin (d + 1) → ℝ) :=
  ((x1Law p y).prod (weakLaw d η y)).map (fun q => Matrix.vecCons q.1 q.2)

/-- Standard accuracy `Pr_{(x,y)∼D}[f(x) = y]` of a `{±1}`-valued classifier (objective (1), p. 2,
with the 0–1 loss); the label is uniform on `{−1, +1}`. -/
noncomputable def stdAcc (d : ℕ) (p η : ℝ) (f : (Fin (d + 1) → ℝ) → ℝ) : ℝ :=
  (1 / 2) * (condLaw d p η 1 {x | f x = 1}).toReal +
    (1 / 2) * (condLaw d p η (-1) {x | f x = -1}).toReal

/-- `ℓ∞`-robust accuracy `Pr_{(x,y)∼D}[f(x + δ) = y for every ‖δ‖_∞ ≤ ε]` (objective (2), p. 2,
with the 0–1 loss and `∆ = {‖δ‖_∞ ≤ ε}`). The norm on `Fin (d + 1) → ℝ` is the sup norm. The robust
event need not be measurable; the measure of it is its outer measure. -/
noncomputable def robustAcc (d : ℕ) (p η : ℝ) (f : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  (1 / 2) * (condLaw d p η 1 {x | ∀ δ : Fin (d + 1) → ℝ, ‖δ‖ ≤ ε → f (x + δ) = 1}).toReal +
    (1 / 2) * (condLaw d p η (-1) {x | ∀ δ : Fin (d + 1) → ℝ, ‖δ‖ ≤ ε → f (x + δ) = -1}).toReal

/-- `p_{ij}` (App. C, p. 15): the probability that `f` predicts `+1` when the first feature equals `i`
and the weak features `x₂, …, x_{d+1}` are distributed according to `G_j = weakLaw d η j`. -/
noncomputable def pij (d : ℕ) (η : ℝ) (f : (Fin (d + 1) → ℝ) → ℝ) (i j : ℝ) : ℝ :=
  (weakLaw d η j {z | f (Matrix.vecCons i z) = 1}).toReal

/-- The fixed adversary of App. C, p. 14: it replaces `x_i` by `x_i − yε`, `ε = 2η`, for each
`i ≥ 2` and leaves `x₁` unchanged. -/
noncomputable def shiftAdv (d : ℕ) (η y : ℝ) : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ) :=
  fun x => x - (2 * η * y) • Matrix.vecCons 0 (fun _ => 1)

/-- Accuracy `Pr(f(x_adv) = y)` against the fixed adversary `shiftAdv` (App. C, pp. 15–16). -/
noncomputable def shiftAcc (d : ℕ) (p η : ℝ) (f : (Fin (d + 1) → ℝ) → ℝ) : ℝ :=
  (1 / 2) * (condLaw d p η 1 {x | f (shiftAdv d η 1 x) = 1}).toReal +
    (1 / 2) * (condLaw d p η (-1) {x | f (shiftAdv d η (-1) x) = -1}).toReal

end RobustOdds.Tradeoff


