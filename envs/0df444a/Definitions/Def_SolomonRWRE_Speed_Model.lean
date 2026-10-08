-- Prove2me | Definitions.Def_SolomonRWRE_Speed_Model
-- name    : SolomonRWRE_Speed_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:20.576848+00:00
-- url     : https://prove2.me/theorems/a64558ac-f583-47c7-a1dd-eedbfeb70cdd
-- title:
--   Solomon §0–§1 — environment, nearest-neighbor walk, passage times, and σ
-- statement:
--   A fixed environment assigns a right-step probability $a_z\in[0,1]$ to each integer site $z$; the left-step probability is $1-a_z$. The fixed-environment chain starts at a specified integer and follows these transitions. In the annealed model, the probabilities $\alpha_z$ form an independent, identically distributed random field and the path starts at zero. The joint environment/path cylinder probabilities equal the environmental averages of the fixed-environment chain probabilities.
--
--   For a walk $X$, let $T_z$ be the first positive time at which $X$ visits $z$, with $T_z=\infty$ if it never does, and set $T_0=0$. For positive $n$, put $\tau_n=T_n-T_{n-1}$ on paths where these times are finite. Define $\sigma_z=(1-\alpha_z)/\alpha_z$ and the possibly infinite means $E\sigma$ and $E(\sigma^{-1})$.
--
--   These definitions supply the common stochastic model for the speed theorem and its passage-time lemmas.
--
--   **Formalization Note** The environment is pointwise in $[0,1]$. Ratios and their expectations use extended nonnegative reals; passage times use extended natural numbers.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, pp. 1–2, §0; p. 5, passage times; pp. 6–7, Eσ and E(σ⁻¹)

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

namespace SolomonRWRE.Speed

/-- Solomon (1975), §1, p. 2: `σ_n = (1-α_n)/α_n`. The extended nonnegative
value retains `σ_n = ∞` when `α_n = 0`. -/
noncomputable def sigma {Ω : Type*} (α : ℤ → Ω → ℝ) (n : ℤ) (ω : Ω) : ENNReal :=
  ENNReal.ofReal (1 - α n ω) / ENNReal.ofReal (α n ω)

/-- Solomon (1975), Lemma (1.1), p. 2: the same ratio in a fixed
environment. -/
noncomputable def sigmaFixed (a : ℤ → ℝ) (n : ℤ) : ENNReal :=
  ENNReal.ofReal (1 - a n) / ENNReal.ofReal (a n)

/-- Solomon (1975), §1, pp. 6–7: `Eσ`, potentially infinite. -/
noncomputable def meanSigma {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (α : ℤ → Ω → ℝ) : ENNReal := ∫⁻ ω, sigma α 0 ω ∂P

/-- Solomon (1975), §1, p. 7: `E(σ⁻¹)`, potentially infinite. -/
noncomputable def meanInvSigma {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (α : ℤ → Ω → ℝ) : ENNReal := ∫⁻ ω, (sigma α 0 ω)⁻¹ ∂P

/-- Solomon (1975), §1, p. 5: `T_0=0`, and `T_z` is the first strictly positive
time of a visit to `z`; it is `∞` if there is no such visit. -/
noncomputable def passageTime {Ω : Type*} (X : ℕ → Ω → ℤ) (z : ℤ) (ω : Ω) : ℕ∞ :=
  if z = 0 then 0 else ⨅ k ∈ {k : ℕ | 0 < k ∧ X k ω = z}, (k : ℕ∞)

/-- Solomon (1975), §1, p. 5: the time between first visits to successive
positive sites. Used only on paths where both passage times are finite. -/
noncomputable def ladderTime {Ω : Type*} (X : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) : ℕ∞ :=
  passageTime X (n : ℤ) ω - passageTime X ((n : ℤ) - 1) ω

/-- Solomon (1975), Theorem (1.8), p. 5: the complete law of the positive
ladder-time sequence is ergodic under the left shift; Mathlib's `Ergodic`
includes measure preservation, hence strict stationarity. -/
def IsStationaryErgodic {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ℕ → Ω → ℤ) : Prop :=
  Measurable (fun ω n => ladderTime X (n + 1) ω) ∧
    Ergodic (fun s : ℕ → ℕ∞ => fun n => s (n + 1))
      (P.map (fun ω n => ladderTime X (n + 1) ω))

end SolomonRWRE.Speed


