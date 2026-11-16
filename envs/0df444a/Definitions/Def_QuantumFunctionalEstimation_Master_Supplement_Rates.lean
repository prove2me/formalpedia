-- Prove2me | Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
-- name    : QuantumFunctionalEstimation_Master_Supplement_Rates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:58:17.159199+00:00
-- url     : https://prove2.me/theorems/c25bb521-e676-4232-9a16-896e06088333
-- title:
--   Explicit rates and operational sample and query lower bounds
-- statement:
--   For $d\ge2$ and $t>0$, let
--   $$B(d,t)=\frac{d^2}{t\log^2d\,\max\{1,t\log^2d\}}.$$
--   The entropy rate is $B(d,\varepsilon)+\log^2d/\varepsilon^2$. The fractional-power term is $d^{1+1/\alpha}/(\varepsilon^{1/\alpha}\log^2d\max\{1,\varepsilon^{1/\alpha}\log^2d\})$. The Rényi and Tsallis rates retain both source regimes and every classical second term. For noninteger $\alpha>1$, $\kappa_\alpha=4\lceil\alpha\rceil/(\lceil\alpha\rceil-\alpha)$.
--
--   An operational sample bound $L$ says that every collective estimator uniformly successful at additive error $\varepsilon$ and probability at least $2/3$ uses a natural copy budget $N\ge L$. A query bound quantifies over every finite environment capable of purifying all states and every operational adaptive query algorithm. The combined predicate asserts sample bound $kR$ and query bound $k\sqrt R$, using a common positive multiplier that can be chosen as the minimum of the two source multipliers. No infimum over a potentially empty set of algorithms is used.
--
--   Theorems quantify all multipliers and independent dimension/error thresholds before varying data and algorithms. The square-root rates fix the logarithmic factors suppressed in the introductory query announcements and are equivalent up to constant factors to the announced sums.
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed pp. 3–8, 21, 25–36 (PDF pp. 5–10, 23, 27–38), Theorems 1.2–1.11 and their Section 5 counterparts

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Queries
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Testing
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

def transitionRate (d : ℕ) (t : ℝ) : ℝ :=
  (d : ℝ)^2 / (t * Real.log d ^ 2 * max 1 (t * Real.log d ^ 2))

def entropyRate (d : ℕ) (ε : ℝ) : ℝ := transitionRate d ε + Real.log d ^ 2 / ε^2

def fractionalRate (α : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ)^(1 + 1 / α) / (ε^(1 / α) * Real.log d ^ 2 * max 1 (ε^(1 / α) * Real.log d ^ 2))

def kappa (α : ℝ) : ℝ := 4 * (⌈α⌉₊ : ℝ) / ((⌈α⌉₊ : ℝ) - α)

def renyiRate (α : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  if α < 1 then fractionalRate α d ε + (d : ℝ)^(1 / α - 1) / ε^2
  else (d : ℝ)^2 / (ε^(1 / α) * (Real.log d)^(kappa α)) + (d : ℝ)^(1 - 1 / α) / ε^2

def tsallisRate (α : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  if α < 1 then fractionalRate α d ε + (d : ℝ)^(2 - 2 * α) / ε^2
  else ε^(-2 / (α - 1)) / Real.log (1 / ε)^4

/-- Operational lower bound, against every collective real-outcome POVM. -/
def SampleBound {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ → ℝ) (ε B : ℝ) : Prop :=
  ∀ N : ℕ, ∀ E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Fin d) ℝ,
    Successful F ε N E → B ≤ N

/-- Every environment large enough to purify all states, and every finite adaptive interaction.
A known second state can be prepared within the input-independent operations. -/
def QueryBound {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ → ℝ) (ε B : ℝ) : Prop :=
  ∀ e : ℕ, d ≤ e → ∀ Q : ℕ, ∀ A : QueryAlgorithm e d Q,
    QuerySuccessful F ε A → B ≤ Q

def EstimationBounds {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ → ℝ) (ε k R : ℝ) : Prop :=
  SampleBound F ε (k * R) ∧ QueryBound F ε (k * Real.sqrt R)

def Noninteger (α : ℝ) : Prop := ∀ m : ℕ, α ≠ (m : ℝ)

end QuantumFunctionalEstimation.Master.Supplement


