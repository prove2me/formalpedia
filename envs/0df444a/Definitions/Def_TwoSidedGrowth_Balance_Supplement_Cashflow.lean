-- Prove2me | Definitions.Def_TwoSidedGrowth_Balance_Supplement_Cashflow
-- name    : TwoSidedGrowth_Balance_Supplement_Cashflow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:31:49.69289+00:00
-- url     : https://prove2.me/theorems/44b92504-1e04-4d7b-b7d5-82b88e85320b
-- title:
--   §3.6 and Theorem 6 — Stieltjes cash flow, increasing paths, common endpoints, and constrained growth
-- statement:
--   Let $X$ be a nondecreasing, right-continuous real size path, represented by Mathlib's Stieltjes function. Its state measure is $dX$, which gives each jump its full size as mass. For a balance path $\gamma$, define the operating cash rate $a(\gamma,x)=(v-c)g(\gamma,x)-b(\gamma)x$ and the signed cash-flow measure on $[0,T]$ by
--   $$
--   dC_T=\mathbf{1}_{[0,T]}a(\gamma(t),X(t))\,dt-\mathbf{1}_{[0,T]}dX(t),\qquad
--   J_T=\int e^{-\rho t}\,dC_T(t).
--   $$
--   Thus a size jump $\Delta X$ costs $\Delta X$, exactly as in §3.6. Profit is defined from these original cash flows, not from the discounted-welfare identity. The latter, together with integrability of every density, is the conclusion named `FiniteAccounting` and is proved by the companion statements. Where output is positive, the implied ordinary margin is $(a-\dot X)/g$.
--
--   On a finite horizon, fixed endpoints mean $T>0$, $0<\underline x<\bar x$, $X(t)=\underline x$ for $t<0$, and $X(t)=\bar x$ for $t\ge T$. Thus the initial size is $X(0-)$, the final size is $X(T)$, and shocks at either endpoint are charged. A faster path is pointwise no smaller throughout $[0,T]$; a strictly faster path is strictly larger at every interior time. Monotonicity is non-strict, as in Definition 1.
--
--   For Theorem 4 a feasible trajectory starts at $x_0$, stays below the cap, has a locally integrable nonnegative growth density $r(t)\le f(X(t))$, satisfies $dX=r\,dt$ on $[0,\infty)$, and converges to the specified common target. Equality of measures excludes jumps and singular continuous growth under a finite rate constraint. No smoothness or positive lower bound on $f$ is imposed. Infinite-horizon profit is the discounted operating integral minus the discounted state expenditure integral; Theorem 4 proves both are integrable and that finite-horizon profits converge to this value.
--
--   These objects extend the source's classical and impulse accounting to all increasing paths of bounded variation on a finite interval, including singular continuous paths. Constant extensions outside the finite horizon are only a representation convention. The choice of a right-continuous representative fixes the timing of atoms and changes no classical or impulse cash flow.
-- source:
--   Lian, van Ryzin, Optimal Growth in Two-Sided Markets, SSRN working paper 3310559 (version of 2020-01-16), pp. 15–17, 22, 41–42, 55–57, (12)–(13), Definitions 1–2, subsidy shocks, Theorems 4 and 6

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Supplement_Stationary

namespace TwoSidedGrowth.Balance.Supplement

open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Subsidized means a negative margin, §3.6. -/
def IsSubsidized (pm : ℝ) : Prop := pm < 0

/-- The reduced operating cash rate before expenditure on state increments, (12). -/
def operating (M : Model) (γ x : ℝ) : ℝ :=
  (M.v - M.c) * out M γ x - attrition M γ * x

def discount (M : Model) (t : ℝ) : ℝ := Real.exp (-(M.ρ * t))

/-- On continuous pieces, π = (operating - x')/out wherever out > 0. -/
def impliedMargin (M : Model) (γ x rate : ℝ) : ℝ :=
  (operating M γ x - rate) / out M γ x

/-- Increasing paths are represented by Mathlib's monotone right-continuous
Stieltjes functions. The initial endpoint is x(0-), permitting an initial shock;
the terminal endpoint is x(T), permitting a terminal shock. Constant extensions
outside [0,T] change no path or cash payment within the horizon. -/
def FixedEndpoints (T lower upper : ℝ) (X : StieltjesFunction ℝ) : Prop :=
  0 < T ∧ 0 < lower ∧ lower < upper ∧
  (∀ t : ℝ, t < 0 → X t = lower) ∧
  (∀ t : ℝ, T ≤ t → X t = upper)

/-- Definition 2; common endpoints are imposed separately by FixedEndpoints. -/
def Faster (T : ℝ) (fast slow : StieltjesFunction ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, slow t ≤ fast t

def StrictlyFaster (T : ℝ) (fast slow : StieltjesFunction ℝ) : Prop :=
  Faster T fast slow ∧ ∀ t ∈ Set.Ioo (0 : ℝ) T, slow t < fast t

/-- Signed cash-flow measure [(v-c)out-bx]dt-dx on [0,T].
The state measure charges every jump by its full size, including at 0 and T.
withDensityᵥ has a zero fallback for nonintegrable densities: all its densities
are proved integrable in Theorem 6, rather than assumed in the path domain. -/
def cashflow (M : Model) (T : ℝ) (X : StieltjesFunction ℝ) (γ : ℝ → ℝ) : SignedMeasure ℝ :=
  (volume.restrict (Set.Icc 0 T)).withDensityᵥ (fun t => operating M (γ t) (X t)) -
  (X.measure.restrict (Set.Icc 0 T)).withDensityᵥ (fun _ => (1 : ℝ))

/-- Original discounted cash flow, integrated against the signed cash measure;
not the integration-by-parts welfare identity. -/
def cashProfit (M : Model) (T : ℝ) (X : StieltjesFunction ℝ) (γ : ℝ → ℝ) : ℝ :=
  ∫ᵛ t, discount M t ∂<•(cashflow M T X γ)

def optimalProfit (M : Model) (T : ℝ) (X : StieltjesFunction ℝ) : ℝ :=
  cashProfit M T X (fun t => balance M (X t))

/-- Accounting conclusions, not a condition defining a feasible path. Theorem 6
establishes these from the primitive signed cash-flow measure. -/
def FiniteAccounting (M : Model) (T initial : ℝ)
    (X : StieltjesFunction ℝ) (γ : ℝ → ℝ) : Prop :=
  IntegrableOn (fun t => operating M (γ t) (X t)) (Set.Icc 0 T) ∧
  IntegrableOn (fun t => discount M t * operating M (γ t) (X t)) (Set.Icc 0 T) ∧
  IntegrableOn (fun t => discount M t * G M (γ t) (X t)) (Set.Icc 0 T) ∧
  IntegrableOn (fun _ => (1 : ℝ)) (Set.Icc 0 T) X.measure ∧
  IntegrableOn (discount M) (Set.Icc 0 T) X.measure ∧
  Integrable (discount M) (cashflow M T X γ).variation ∧
  cashProfit M T X γ =
    (∫ t in Set.Icc (0 : ℝ) T, discount M t * operating M (γ t) (X t)) -
      ∫ t in Set.Icc (0 : ℝ) T, discount M t ∂X.measure ∧
  cashProfit M T X γ =
    (∫ t in Set.Icc (0 : ℝ) T, discount M t * G M (γ t) (X t)) -
      discount M T * X T + initial

/-- The two independent original cash-flow integrals on the infinite horizon.
Theorem 4 concludes absolute integrability and convergence of finite profits. -/
def infiniteProfit (M : Model) (X : StieltjesFunction ℝ) : ℝ :=
  (∫ t in Set.Ici (0 : ℝ), discount M t * operating M (balance M (X t)) (X t)) -
  ∫ t in Set.Ici (0 : ℝ), discount M t ∂X.measure

/-- Full printed feasible set for Theorem 4, with convergence to the target.
Equality of state measures with rate dt imposes absolute continuity, excluding
jumps and singular Cantor growth under a finite rate constraint. No regularity
or positive lower bound on f is imposed. Local integrability of the density is
part of the meaning of a locally absolutely continuous growth trajectory. -/
def FeasibleTo (x0 cap target : ℝ) (f : ℝ → ℝ) (X : StieltjesFunction ℝ) : Prop :=
  (∀ t : ℝ, t ≤ 0 → X t = x0) ∧
  (∀ t : ℝ, 0 ≤ t → X t ≤ cap) ∧
  Tendsto (fun t => X t) atTop (𝓝 target) ∧
  ∃ rate : ℝ → ℝ,
    (∀ T : ℝ, 0 ≤ T → IntegrableOn rate (Set.Icc 0 T)) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      0 ≤ rate t ∧ rate t ≤ f (X t)) ∧
    X.measure.restrict (Set.Ici (0 : ℝ)) =
      (volume.restrict (Set.Ici (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (rate t))

end
end TwoSidedGrowth.Balance.Supplement


