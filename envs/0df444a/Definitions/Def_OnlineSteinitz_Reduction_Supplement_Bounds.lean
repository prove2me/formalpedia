-- Prove2me | Definitions.Def_OnlineSteinitz_Reduction_Supplement_Bounds
-- name    : OnlineSteinitz_Reduction_Supplement_Bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:13:50.274415+00:00
-- url     : https://prove2.me/theorems/9c4cc0e1-4e87-46aa-841b-03be25a7896b
-- title:
--   Operational discrepancy guarantees and target rates
-- statement:
--   A deterministic guarantee of radius $\rho$ requires maximum proportional-prefix residual at most $\rho$ for every adaptive adversary whose realized stream is legal. A randomized guarantee of radius $\rho$ and failure parameter $\delta$ requires, for every fixed legal input, success probability at least $1-\delta$. The input is quantified outside the tape event. Validity and measurable decisions are separate properties of the algorithm; no discrepancy promise is included in its definition.
--
--   The deterministic target rate is $\log T$ when $d=1$ and $\sqrt T$ otherwise. Set $d_*=\min\{d,T\}$. The dimension rate is $\sqrt{d_*\log(T/d_*)}$ and the combined randomized rate is $\log T+\sqrt{d_*\log(T/d_*)}$. These use natural logarithms and real division. They are used only on the horizons and dimensions stated in the theorems. The formulation uses achievable bounds directly, without assuming an optimal algorithm or defining a possibly empty infimum.
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; §1, p.2; Theorem 3.1, p.13; Theorem 5.1, p.20; Lemma 5.5, p.23

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Algorithms

open MeasureTheory

namespace OnlineSteinitz.Reduction.Supplement

/-! Operational meanings of achievable bounds, §1 p.2.
No infimum or assumed optimal algorithm is introduced. -/
noncomputable def DeterministicGuarantee {T d : ℕ} (A : OrderingRule d Unit)
    (ρ : ℝ) : Prop :=
  ∀ adv : ℕ → List (ℕ × Vec d) → Vec d,
    LegalAdaptiveRun (adaptiveOrderingRun (T := T) A adv) →
    maxResidual (adaptiveOrderingRun (T := T) A adv) ≤ ρ

noncomputable def RandomizedGuarantee {T d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : OrderingRule d Ω) (δ ρ : ℝ) : Prop :=
  ∀ v : Fin T → Vec d, LegalInput v →
    ENNReal.ofReal (1 - δ) ≤ μ {ω | maxResidual (orderingRun A ω v) ≤ ρ}

noncomputable def deterministicRate (T d : ℕ) : ℝ :=
  if d = 1 then Real.log T else Real.sqrt T

noncomputable def dimensionRate (T d : ℕ) : ℝ :=
  Real.sqrt ((min d T : ℕ) * Real.log ((T : ℝ) / (min d T : ℕ)))

noncomputable def randomizedRate (T d : ℕ) : ℝ :=
  Real.log T + dimensionRate T d

end OnlineSteinitz.Reduction.Supplement


