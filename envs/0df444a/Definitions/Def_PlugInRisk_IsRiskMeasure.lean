-- Prove2me | Definitions.Def_PlugInRisk_IsRiskMeasure
-- name    : PlugInRisk_IsRiskMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:22.886479+00:00
-- url     : https://prove2.me/theorems/672b3e87-8b55-4758-9f4f-526cab2d14c2
-- title:
--   Convex law-invariant risk measure on $L^p$
-- statement:
--   Let $\Omega_0=[0,1]$ with Lebesgue measure be the standard probability space and $p\in[1,\infty]$. A functional $\rho:L^p(\Omega_0)\to\mathbb R$ is a **(convex, law-invariant) risk measure** if for all $X,Y\in L^p$:
--
--   1. (cash invariance) $\rho(X+m)=\rho(X)+m$ for every $m\in\mathbb R$, and $\rho(0)=0$;
--   2. (monotonicity) $\rho(X)\le\rho(Y)$ whenever $X\le Y$ almost surely;
--   3. (convexity) $\rho(\lambda X+(1-\lambda)Y)\le\lambda\rho(X)+(1-\lambda)\rho(Y)$ for $\lambda\in[0,1]$;
--   4. (law invariance) $\rho(X)=\rho(Y)$ whenever $X$ and $Y$ have the same distribution.
--
--   For $p=\infty$ this is Definition 1.1 with condition (d); §4 uses the same axioms on $L^p$. Here $X$ is a loss and $\rho(X)$ the capital needed to make it acceptable, so $\rho$ is increasing.
--
--   **Formalization Note** $\rho$ is a function on all real functions on $[0,1]$; the axioms are imposed only on $L^p$ functions (`MemLp X p volume`), so values outside $L^p$ play no role. Almost surely equal $L^p$ functions get the same value by monotonicity.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Definition 1.1 and condition (d), p.2; §4, p.17

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Convex law-invariant risk measure** (Bartl & Tangpi, *Non-asymptotic convergence rates for
the plug-in estimation of risk measures*, arXiv:2003.10479v2, Definition 1.1 and condition (d),
p.2; the extension to `Lᵖ`, §4, p.17).

A functional `ρ : Lᵖ → ℝ` over a standard probability space is a (convex, law-invariant) risk
measure if for all `X, Y ∈ Lᵖ`:
(a) `ρ(X + m) = ρ(X) + m` for all `m ∈ ℝ`, and `ρ(0) = 0`;
(b) `ρ(X) ≤ ρ(Y)` if `X ≤ Y` almost surely;
(c) `ρ(λX + (1 − λ)Y) ≤ λρ(X) + (1 − λ)ρ(Y)` for `λ ∈ [0, 1]`;
(d) `ρ(X) = ρ(Y)` if `X` and `Y` have the same distribution.
The paper's convention (p.2) is that "risk measure" always means a convex law-invariant one.
Definition 1.1 is the case `p = ∞`; §4 (p.17) uses the same axioms on `Lᵖ`, `p ∈ [1, ∞]`.

**Formalization Note** The standard probability space is `unitInterval` (`[0,1]`) with Lebesgue
measure `volume`. `ρ` is a function on all real functions on `[0,1]`; the axioms are required
only on `Lᵖ` (`MemLp X p volume`), so the values of `ρ` outside `Lᵖ` are irrelevant. Two `Lᵖ`
functions that agree almost surely get the same value by (b) applied in both directions, so `ρ`
is a function on `Lᵖ` classes. The sign convention is the paper's (footnote 2, p.2): `X` is a
loss and `ρ` is increasing. -/
def IsRiskMeasure (p : ℝ≥0∞) (ρ : (unitInterval → ℝ) → ℝ) : Prop :=
  (∀ X : unitInterval → ℝ, MemLp X p volume → ∀ m : ℝ, ρ (fun ω => X ω + m) = ρ X + m) ∧
  ρ (fun _ => 0) = 0 ∧
  (∀ X Y : unitInterval → ℝ, MemLp X p volume → MemLp Y p volume →
    X ≤ᵐ[volume] Y → ρ X ≤ ρ Y) ∧
  (∀ X Y : unitInterval → ℝ, MemLp X p volume → MemLp Y p volume →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ρ (fun ω => t * X ω + (1 - t) * Y ω) ≤ t * ρ X + (1 - t) * ρ Y) ∧
  (∀ X Y : unitInterval → ℝ, MemLp X p volume → MemLp Y p volume →
    volume.map X = volume.map Y → ρ X = ρ Y)

end PlugInRisk


