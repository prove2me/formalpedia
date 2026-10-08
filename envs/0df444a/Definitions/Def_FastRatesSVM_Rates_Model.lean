-- Prove2me | Definitions.Def_FastRatesSVM_Rates_Model
-- name    : FastRatesSVM_Rates_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:04.15161+00:00
-- url     : https://prove2.me/theorems/d1a56c6d-4522-4e80-802d-ae7b14b24fcf
-- title:
--   Binary classification distribution, hinge risk, and classification risk
-- statement:
--   Fix a dimension $d$ and let $X$ be the closed unit ball in $\mathbb R^d$. A binary classification distribution is represented by a probability marginal $\mu$ supported on $X$ and a measurable regression function $\eta:\mathbb R^d\to[0,1]$. Its joint law puts conditional mass $\eta(x)$ on label $+1$ and $1-\eta(x)$ on label $-1$.
--
--   The hinge loss is $\ell(y,t)=\max\{0,1-yt\}$. Classification uses the sign convention $\operatorname{sign}(0)=+1$. The risks are the nonnegative extended integrals of these losses under the joint law. Each Bayes risk is the infimum over all measurable real-valued decision functions.
--
--   This model keeps the marginal and the regression function explicit for the paper's two noise assumptions. **Formalization Note** Functions are represented on all of $\mathbb R^d$; only their values on $X$ affect risks.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, pp. 2–4 and 6, (1)–(3), classification and hinge risks

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics_v2

open MeasureTheory

namespace FastRatesSVM.Rates

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def X (d : ℕ) : Set (E d) := Metric.closedBall 0 1

/-- The marginal law and a fixed measurable version of the regression function. -/
structure BinaryDistribution (d : ℕ) where
  μ : Measure (E d)
  prob : IsProbabilityMeasure μ
  support : μ (X d)ᶜ = 0
  η : E d → ℝ
  measurable_eta : Measurable η
  eta_nonneg : ∀ x, 0 ≤ η x
  eta_le_one : ∀ x, η x ≤ 1

/-- Joint law on inputs and labels +1 and -1. -/
noncomputable def jointLaw {d : ℕ} (D : BinaryDistribution d) : Measure (E d × ℝ) :=
  D.μ.bind (fun x =>
    ENNReal.ofReal (D.η x) • Measure.dirac (x, (1 : ℝ)) +
    ENNReal.ofReal (1 - D.η x) • Measure.dirac (x, (-1 : ℝ)))

/-- Hinge loss from §2.1. -/
def hingeLoss {d : ℕ} : SupportVectorMachines.Classification.Loss (E d) where
  toFun := fun _ y t => max 0 (1 - y * t)
  measurable := by fun_prop
  nonneg := by intro x y t; exact le_max_left _ _

/-- Zero-one loss with sign(0) = +1. -/
noncomputable def classLoss {d : ℕ} : SupportVectorMachines.Classification.Loss (E d) where
  toFun := fun _ y t => if t < 0 then (if y = -1 then 0 else 1) else (if y = 1 then 0 else 1)
  measurable := by
    have ht : MeasurableSet {p : E d × ℝ × ℝ | p.2.2 < 0} := by measurability
    have hn : MeasurableSet {p : E d × ℝ × ℝ | p.2.1 = -1} := by measurability
    have hp : MeasurableSet {p : E d × ℝ × ℝ | p.2.1 = 1} := by measurability
    exact (measurable_const.ite hn measurable_const).ite ht
      (measurable_const.ite hp measurable_const)
  nonneg := by intro x y t; split <;> split <;> norm_num

noncomputable def hingeRisk {d : ℕ} (D : BinaryDistribution d) (f : E d → ℝ) : ENNReal :=
  SupportVectorMachines.Classification.risk hingeLoss (jointLaw D) f

noncomputable def bayesHingeRisk {d : ℕ} (D : BinaryDistribution d) : ENNReal :=
  SupportVectorMachines.Classification.bayesRisk hingeLoss (jointLaw D)

noncomputable def classRisk {d : ℕ} (D : BinaryDistribution d) (f : E d → ℝ) : ENNReal :=
  SupportVectorMachines.Classification.risk classLoss (jointLaw D) f

noncomputable def bayesClassRisk {d : ℕ} (D : BinaryDistribution d) : ENNReal :=
  SupportVectorMachines.Classification.bayesRisk classLoss (jointLaw D)

end FastRatesSVM.Rates


