-- Prove2me | Definitions.Def_NondualStable_Optimization_Supplement_MinimaxRisk
-- name    : NondualStable_Optimization_Supplement_MinimaxRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:35:30.335872+00:00
-- url     : https://prove2.me/theorems/7f3d5779-b86e-41aa-84d1-8906322ecf7d
-- title:
--   Randomized algorithms and expected minimax risk
-- statement:
--   Let $X\subseteq\mathbb R^d$ be feasible, $\mathcal C$ an objective class, and $\mathcal O$ a local oracle. A randomized algorithm samples a seed from an arbitrary probability space, independently of the unknown objective, and the seed selects a deterministic decision tree of depth at most $T$. For every fixed objective its output and loss are almost everywhere measurable. The depth cap and feasibility hold for every seed, including null events.
--
--   For $x\in X$ define its nonnegative optimality gap by
--   $$
--   \operatorname{gap}_X(f,x)=\sup_{y\in X}\max\{f(x)-f(y),0\}.
--   $$
--   On the nonempty compact norm ball and finite convex objectives in Theorem 13 this equals $f(x)-\min_X f$. The expected minimax risk is
--   $$
--   \operatorname{Risk}_T(\mathcal O,\mathcal C)=\inf_{A\in\operatorname{RandAlg}_T(\mathcal O)}\ \sup_{f\in\mathcal C}\ \mathbb E_A\big[\operatorname{gap}_X(f,\widehat x(A,f))\big].
--   $$
--   The supremum chooses one fixed objective before internal randomness is drawn. The expectation is the nonnegative Lebesgue integral with respect to the actual seed law, and both extrema are genuine complete-lattice extrema in $[0,\infty]$. This prevents real infimum defaults or nonintegrable Bochner integrals from changing the problem. At the norm-ball inputs the objective class contains the zero function and constant feasible-output algorithms exist; losses are uniformly bounded, so the risk is finite. The definitions remain meaningful on other inputs without assuming these facts.
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 12 / PDF p. 13, Section 7, equation (20)

import Mathlib
import Definitions.Def_NondualStable_Optimization_Supplement_LocalOracle

open MeasureTheory

universe u

open scoped ENNReal

namespace NondualStable.Optimization.Supplement

/-- Optimality gap as a supremum of improvements over feasible comparison points.
For a nonempty compact X and finite convex f this equals f(x) - min_X f, is finite,
and is nonnegative. ENNReal retains the genuine supremum on arbitrary inputs. -/
noncomputable def gap {d : ℕ} (X : Set (Vec d)) (f : Vec d → ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ y : X, ENNReal.ofReal (f x.val - f y.val)

/-- Arbitrary measurable mixtures of deterministic adaptive trees. The seed law is
fixed independently of the unknown objective. No finite alphabet, computation model,
or almost-sure relaxation of the horizon is imposed. -/
structure RandomizedAlgorithm {d : ℕ} (X : Set (Vec d))
    (C : Set (Vec d → ℝ)) {Reply : Type u} (O : LocalOracle C Reply) (T : ℕ) where
  Seed : Type u
  measurableSpace : MeasurableSpace Seed
  law : @Measure Seed measurableSpace
  probability : @IsProbabilityMeasure Seed measurableSpace law
  choose : Seed → QueryTree X Reply T
  measurable_output : ∀ f : C,
    @AEMeasurable Seed (Vec d) inferInstance measurableSpace
      (fun s => ((choose s).run O f).val) law
  measurable_loss : ∀ f : C,
    @AEMeasurable Seed ℝ≥0∞ inferInstance measurableSpace
      (fun s => gap X f.val ((choose s).run O f)) law

/-- Equation (20), infimum over algorithms followed by supremum over a fixed
objective and expectation over the independent seed only. The nonnegative integral
never invokes the Bochner integral's nonintegrable-input default. -/
noncomputable def minimaxRisk {d : ℕ} (X : Set (Vec d))
    (C : Set (Vec d → ℝ)) {Reply : Type u} (O : LocalOracle C Reply) (T : ℕ) : ℝ≥0∞ :=
  ⨅ A : RandomizedAlgorithm X C O T, ⨆ f : C,
    @lintegral A.Seed A.measurableSpace A.law
      (fun s => gap X f.val ((A.choose s).run O f))

end NondualStable.Optimization.Supplement


