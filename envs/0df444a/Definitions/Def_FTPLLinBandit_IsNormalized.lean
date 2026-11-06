-- Prove2me | Definitions.Def_FTPLLinBandit_IsNormalized
-- name    : FTPLLinBandit_IsNormalized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:07.145584+00:00
-- url     : https://prove2.me/theorems/09905f9e-35f5-4374-b554-c9b5a9325fe1
-- title:
--   Assumption 1 — normalized action set $rB^d_2\subseteq\operatorname{conv}(A)\subseteq RB^d_2$ with exploration law $\nu$, $\mu(\nu)=0$, $\operatorname{Cov}(\nu)=I/d$
-- statement:
--   Let $A\subseteq\mathbb R^d$ be an action set, $\nu$ a probability distribution on $\mathbb R^d$ (the **exploration distribution**), and $r,R\in\mathbb R$. The pair $(A,\nu)$ satisfies **Assumption 1** with radii $r,R$ when
--
--   1. $r>0$ and $rB^d_2\subseteq\operatorname{conv}(A)\subseteq RB^d_2$, where $B^d_2$ is the closed Euclidean unit ball;
--   2. $\nu$ is carried by $A$, i.e. $\nu(\mathbb R^d\setminus A)=0$ ($\nu\in\Delta A$);
--   3. $\nu$ has mean zero, $\mu(\nu)=\mathbb E_{a\sim\nu}[a]=0$;
--   4. $\nu$ has covariance $I/d$: for every $u\in\mathbb R^d$,
--   $$\mathbb E_{a\sim\nu}\big[\langle u,a\rangle^2\big]=\frac{\|u\|_2^2}{d}.$$
--
--   This is the normalization under which the whole analysis of the paper is carried out ("Throughout the analysis, we impose the following geometric and exploration assumptions", p.4); every theorem of the mission that refers to the normalized setting assumes it.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. Since the mean is zero, the covariance is $\mathbb E[aa^\top]$, and a symmetric matrix is determined by its quadratic form, so item 4 is $\operatorname{Cov}(\nu)=I/d$. No integrability hypothesis is needed: $\nu$ is carried by $A\subseteq RB^d_2$, so $a$ and $\langle u,a\rangle^2$ are bounded $\nu$-almost surely. The paper's standing $d\ge1$ is a hypothesis of every theorem using this definition.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Assumption 1, p.4

import Mathlib

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **Assumption 1 (Action set and exploration basis).** Wei, *Follow the Perturbed Leader for
Linear Bandits: √T Regret over General Action Sets*, arXiv:2610.17818, Assumption 1, p.4: "The
action set A ⊂ ℝ^d and a fixed exploration distribution ν ∈ ∆A satisfy
r B^d_2 ⊆ conv(A) ⊆ R B^d_2, r > 0, µ(ν) = 0, Cov(ν) = I/d. Here B^d_2 is the Euclidean unit
ball."

`IsNormalized A ν r R` says: `r > 0`; the closed Euclidean ball of radius `r` about the origin is
contained in the convex hull of `A`, which is contained in the closed ball of radius `R`; `ν` is a
probability measure carried by `A` (`ν Aᶜ = 0`); its mean `∫ a dν(a)` is `0`; and its covariance
is `I/d`, stated as the quadratic-form identity `∫ ⟪u, a⟫² dν(a) = ‖u‖²/d` for every `u`.

**Formalization Note.** ℝ^d is `EuclideanSpace ℝ (Fin d)` and `B^d_2` its closed unit ball.
Since the mean is `0`, `Cov(ν) = E_ν[aaᵀ]`, and a symmetric matrix is determined by its quadratic
form, so `Cov(ν) = I/d` is the stated identity. No integrability hypothesis is added: `ν` is
carried by `A ⊆ conv(A) ⊆ R·B^d_2`, so `a` and `⟪u, a⟫²` are `ν`-a.e. bounded, hence integrable.
"ν ∈ ∆A" is read as "probability measure with `ν Aᶜ = 0`"; no measurability of `A` is required.
The paper's standing `d ≥ 1` is a hypothesis of every theorem that uses this definition. -/
def IsNormalized {d : ℕ} (A : Set (EuclideanSpace ℝ (Fin d)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (r R : ℝ) : Prop :=
  0 < r ∧ Metric.closedBall 0 r ⊆ convexHull ℝ A ∧ convexHull ℝ A ⊆ Metric.closedBall 0 R ∧
    IsProbabilityMeasure ν ∧ ν Aᶜ = 0 ∧ ∫ a, a ∂ν = 0 ∧
    ∀ u : EuclideanSpace ℝ (Fin d), ∫ a, ⟪u, a⟫_ℝ ^ 2 ∂ν = ‖u‖ ^ 2 / d

end FTPLLinBandit


