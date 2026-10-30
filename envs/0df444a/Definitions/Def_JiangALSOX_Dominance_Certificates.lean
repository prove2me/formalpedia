-- Prove2me | Definitions.Def_JiangALSOX_Dominance_Certificates
-- name    : JiangALSOX_Dominance_Certificates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:06:46.761964+00:00
-- url     : https://prove2.me/theorems/edbaeb8f-9b47-4693-b82a-1e3f157c8ba1
-- title:
--   The printed CVaR and hinge-loss KKT systems
-- statement:
--   For measurable multiplier functions $\alpha,\mu:\Xi\to\mathbb R$ and a scalar $\pi$, define $f_\alpha(y)=E[\alpha(\xi)g(y,\xi)]$ on its explicitly defined signed-expectation domain. Stationarity is
--   $$-\pi c\in\partial f_\alpha(x)+N_X(x),$$
--   with Minkowski addition (there are one subgradient and one normal whose sum is $-\pi c$).
--
--   The CVaR certificate is exactly the displayed system (KKT1): stationarity, $E[\mu]\le1-\varepsilon$, $\mu+\alpha=1$ almost surely, $\alpha\perp(s-g(x,\cdot))$ and $\mu\perp(s-\beta)$ almost surely, $\pi\perp(t-c^\top x)$, $\beta\le0$, and $x\in X$. No complementarity between $-\beta$ and $(1-\varepsilon)-E[\mu]$ is included.
--
--   The hinge certificate is exactly (KKT2): stationarity, $\mu+\alpha=1$ almost surely, $\alpha\perp(s-g(x,\cdot))$ and $\mu\perp s$ almost surely, $\pi\perp(t-c^\top x)$ and $x\in X$. Measurability of slack and multiplier functions is explicit. Complementarity includes both inequalities and the zero product. The expectation of $\mu$ is the nonnegative extended integral, valid because complementarity makes $\mu$ nonnegative almost surely. These certificates are defined independently of actual minimization.
-- source:
--   Nan Jiang and Weijun Xie, ALSO-X and ALSO-X+: Better Convex Approximations for Chance Constrained Programs, arXiv:2012.04763v4 (14 October 2021), https://arxiv.org/abs/2012.04763v4, p. 42, (KKT1)–(KKT2)

import Definitions.Def_JiangALSOX_Dominance_ConvexAnalysis
import Definitions.Def_JiangALSOX_Dominance_Programs

open MeasureTheory

namespace JiangALSOX.Dominance

noncomputable def weightedFunctional {n m I : ℕ} (D : Model n m I)
    (α : D.Ξ → ℝ) (x : Fin n → ℝ) : Option EReal :=
  signedExpectation D.P (fun ξ => α ξ * loss D x ξ)

def stationarity {n m I : ℕ} (D : Model n m I) (x : Fin n → ℝ)
    (α : D.Ξ → ℝ) (π : ℝ) : Prop :=
  ∃ h ∈ partialSubdiff (weightedFunctional D α) x,
    ∃ v ∈ normalCone D.X x, -π • D.c = h + v

def cvarCertificate {n m I : ℕ} (D : Model n m I) (t : ℝ)
    (x : Fin n → ℝ) (s : D.Ξ → ℝ) (β : ℝ)
    (α μ : D.Ξ → ℝ) (π : ℝ) : Prop :=
  Measurable s ∧ Measurable α ∧ Measurable μ ∧
  stationarity D x α π ∧
  (positiveExpectation D.P μ).toEReal ≤ ((1 - D.ε : ℝ) : EReal) ∧
  (∀ᵐ ξ ∂D.P, μ ξ + α ξ = 1 ∧
    complementary (α ξ) (s ξ - loss D x ξ) ∧ complementary (μ ξ) (s ξ - β)) ∧
  complementary π (t - dotProduct D.c x) ∧ β ≤ 0 ∧ x ∈ D.X

def hingeCertificate {n m I : ℕ} (D : Model n m I) (t : ℝ)
    (x : Fin n → ℝ) (s : D.Ξ → ℝ) (α μ : D.Ξ → ℝ) (π : ℝ) : Prop :=
  Measurable s ∧ Measurable α ∧ Measurable μ ∧
  stationarity D x α π ∧
  (∀ᵐ ξ ∂D.P, μ ξ + α ξ = 1 ∧
    complementary (α ξ) (s ξ - loss D x ξ) ∧ complementary (μ ξ) (s ξ)) ∧
  complementary π (t - dotProduct D.c x) ∧ x ∈ D.X

end JiangALSOX.Dominance


