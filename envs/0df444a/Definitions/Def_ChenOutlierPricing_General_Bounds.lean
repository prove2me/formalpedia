-- Prove2me | Definitions.Def_ChenOutlierPricing_General_Bounds
-- name    : ChenOutlierPricing_General_Bounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:44:07.764916+00:00
-- url     : https://prove2.me/theorems/9cd38014-3b58-4829-9cfc-e0e3a0f78521
-- title:
--   Uniform modular policy contracts and asymptotic envelopes
-- statement:
--   Defines the two input-policy regret contracts and the meta-policy conclusion separately. For a fixed model and α>0, constants, polynomial/logarithmic degrees and thresholds are chosen before all sufficiently large global horizons, all $0\le\varepsilon\le T^{-\alpha}$, all positive eligible nominal subroutine horizons H≤2T, all valid lower-price inputs and all admissible environments. A subroutine of horizon H receives stock $x_0H$ and the absolute corruption budget $\varepsilon T$. The $\pi^o$ contract applies in $p^c<p^o$ for every lower input between those prices; the $\pi^c$ contract applies in the other strict regime. No contract is imposed on wrong-regime calls. The meta-policy's guarantee is a separate predicate used only as the theorem's conclusion. The envelope retains the printed fixed-model parameter list and the $\varepsilon T+\sqrt H$ rate. Also defines the printed maximum in Corollary EC.1 and its five polynomial arguments, without repairing the source.
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, §3.2 and §6.2, supplied source.pdf pp. 12–13, 31–32; e-companion ec15, Corollary EC.1

import Definitions.Def_ChenOutlierPricing_General_MetaPolicy

open MeasureTheory ProbabilityTheory

namespace ChenOutlierPricing.General

/-- The displayed fixed-model polynomial parameters in Theorem 4. -/
noncomputable def parameterScale (m : Model) : ℝ :=
  1 + |optimum m| + |clearance m| + |m.band.lo| + |m.band.hi| +
    |m.LpLower| + |m.LpUpper| + |m.MSq| + |m.sigmaSq|

noncomputable def rateEnvelope (m : Model) (C : ℝ) (d k T : ℕ) (E : ℝ) (H : ℕ) : ℝ :=
  C * parameterScale m ^ d * (1 + Real.log T)^k * (E + Real.sqrt H)

/-- Uniformity is over all causal demand/noise laws, not a selected experiment.
The public initial stock is x₀H; E is the absolute corruption budget. -/
def UniformRegret (m : Model) (π : Policy) (H : ℕ) (E bound : ℝ) : Prop :=
  ∀ {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (U : Ω → Tape) (V : Ω → Ξ) (e : Environment Ξ),
    RunAdmissible m π e H (m.x₀*H) E μ U V →
    regret m π e H (m.x₀*H) μ U V ≤ bound

/-- The two source input-policy contracts, with common constants chosen before
all global and eligible subroutine horizons, budgets, lower-price inputs and environments.
Nominal epoch horizons can exceed the final truncated epoch, but are at most 2T.
Every restart is a fresh execution with its own observed history. -/
def InputBounds (m : Model) (α : ℝ) (πo : ℝ → Policy) (πc : Policy) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d k Tstar : ℕ, ∀ T ≥ max 1 Tstar,
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (T : ℝ)^(-α) → ∀ H : ℕ, 0 < H → H ≤ 2*T →
      ((clearance m < optimum m → ∀ lower ∈ Set.Icc (clearance m) (optimum m),
        UniformRegret m (πo lower) H (ε*T) (rateEnvelope m C d k T (ε*T) H)) ∧
       (optimum m < clearance m →
        UniformRegret m πc H (ε*T) (rateEnvelope m C d k T (ε*T) H)))

/-- Fixed-model sufficiently-large-horizon bound; constants precede ε and all laws. -/
def MetaBound (m : Model) (α : ℝ) (πo : ℝ → Policy) (πc : Policy) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d k Tstar : ℕ, ∀ T ≥ max 1 Tstar,
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (T : ℝ)^(-α) →
      UniformRegret m (metaPolicy m.band πo πc) T (ε*T)
        (rateEnvelope m C d k T (ε*T) T)

noncomputable def corollaryThreshold (m : Model) : ℝ :=
  (1/3 : ℝ) * max (|optimum m - clearance m|/(40*m.LdUpper))
    ((1/(2*m.band.hi)) * (m.sigmaSq*|optimum m-clearance m|/(40*m.LdUpper))^2)

noncomputable def corollaryParameters (m : Model) (T : ℕ) : Fin 5 → ℝ :=
  ![Real.log T, m.LdUpper, m.LpUpper, m.band.hi, 1/|optimum m-clearance m|]

end ChenOutlierPricing.General


