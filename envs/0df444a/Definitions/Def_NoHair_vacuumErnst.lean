-- Prove2me | Definitions.Def_NoHair_vacuumErnst
-- name    : NoHair_vacuumErnst
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T20:51:18.673826+00:00
-- url     : https://prove2.me/theorems/bd9afb71-da00-48ec-863b-95d0c4daac3f
-- title:
--   Vacuum Ernst equations and the comparison bound on the Weyl half-plane
-- statement:
--   Let $X>0$ be the squared norm of the axial Killing field and $Y$ its twist potential. These are the two coordinates of a map into the hyperbolic upper half-plane. With $s=\log\rho$ and Weyl height $z$, put $L=\partial_s^2+e^{2s}\partial_z^2$ and $B(f,h)=f_s h_s+e^{2s} f_z h_z$. A twice continuously differentiable vacuum Ernst map satisfies
--
--   $$
--   X L X = B(X,X)-B(Y,Y),\qquad X L Y=2 B(X,Y).
--   $$
--
--   For two maps the comparison scalar is
--
--   $$
--   \sigma=\frac{(X_1-X_2)^2+(Y_1-Y_2)^2}{X_1X_2}.
--   $$
--
--   The comparison bound requires a uniform upper bound on $\sigma$ over all $\rho>0$, together with uniform convergence to zero as $\rho^2+z^2\to\infty$. This includes approaches arbitrarily close to the rotation axis.
-- source:
--   A. J. Amsel, G. T. Horowitz, D. Marolf and M. M. Roberts, Uniqueness of Extremal Kerr and Kerr–Newman Black Holes, pp. 3–5, eqs. (8)–(13), https://arxiv.org/abs/0906.2367. P. T. Chruściel, J. L. Costa and M. Heusler, Stationary Black Holes: Uniqueness and Beyond, §§8.2, 8.4, pp. 44, 47–48, eqs. (8.13), (8.24), Prop. 8.1, https://arxiv.org/abs/1205.6112.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

namespace NoHair.Weyl

/-- The pair `(s,z)` parametrizes the open Weyl half-plane by `ρ = exp s`. -/
abbrev OrbitPoint := ℝ × ℝ

/-- The squared norm of the axial Killing field and its twist potential. -/
structure ErnstPotentials where
  normSq : OrbitPoint → ℝ
  twist : OrbitPoint → ℝ

def ds (f : OrbitPoint → ℝ) (p : OrbitPoint) : ℝ := fderiv ℝ f p (1, 0)

def dz (f : OrbitPoint → ℝ) (p : OrbitPoint) : ℝ := fderiv ℝ f p (0, 1)

/-- The axisymmetric Euclidean Laplacian multiplied by `ρ²`. -/
def scaledLaplacian (f : OrbitPoint → ℝ) (p : OrbitPoint) : ℝ :=
  ds (ds f) p + Real.exp (2 * p.1) * dz (dz f) p

/-- The Euclidean inner product of two axisymmetric gradients multiplied by `ρ²`. -/
def scaledGradientPair (f h : OrbitPoint → ℝ) (p : OrbitPoint) : ℝ :=
  ds f p * ds h p + Real.exp (2 * p.1) * dz f p * dz h p

/-- The vacuum Ernst equations in upper half-plane target coordinates. -/
def ErnstPotentials.IsSolution (u : ErnstPotentials) : Prop :=
  ContDiff ℝ 2 u.normSq ∧ ContDiff ℝ 2 u.twist ∧
  ∀ p, 0 < u.normSq p ∧
    u.normSq p * scaledLaplacian u.normSq p =
      scaledGradientPair u.normSq u.normSq p - scaledGradientPair u.twist u.twist p ∧
    u.normSq p * scaledLaplacian u.twist p = 2 * scaledGradientPair u.normSq u.twist p

/-- The vacuum Mazur comparison scalar for two Ernst maps. -/
def deviation (u v : ErnstPotentials) (p : OrbitPoint) : ℝ :=
  ((u.normSq p - v.normSq p) ^ 2 + (u.twist p - v.twist p) ^ 2) /
    (u.normSq p * v.normSq p)

/-- Boundedness up to the entire singular axis and decay at Euclidean spatial infinity. -/
def HasComparisonBounds (u v : ErnstPotentials) : Prop :=
  (∃ C : ℝ, ∀ p, deviation u v p ≤ C) ∧
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ p : OrbitPoint,
    R ≤ Real.exp (2 * p.1) + p.2 ^ 2 → deviation u v p ≤ ε

end NoHair.Weyl


