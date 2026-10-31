-- Prove2me | Definitions.Def_FiniteStateContract_Equivalence_Integration
-- name    : FiniteStateContract_Equivalence_Integration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:13:31.806248+00:00
-- url     : https://prove2.me/theorems/00f02dc2-0f65-4ea6-bd94-2c4b0eefee11
-- title:
--   Signed extended integrals, partial inverse, and infima of partial families
-- statement:
--   For a measure $\mu$ and a measurable extended-real function $f$, the relation $\operatorname{IntegralValue}(\mu,f,v)$ says that at least one of the integrals of its positive and negative parts is finite and $v$ is their difference. Thus $+\infty$ and $-\infty$ are allowed, while $\infty-\infty$ has no value. Measurability is required modulo $\mu$-null sets.
--
--   For a family of partially defined costs, its infimum has a value only when each eligible index has exactly one defined cost. Its value is the extended-real infimum of those costs, including $+\infty$ for an empty family and $-\infty$ for a family unbounded below. An inverse $U^{-1}(y)=x$ is represented by $U(x)=y$ together with uniqueness of that preimage. These are general evaluation conventions; they assume none of the paper's claimed solvability or equivalences.
-- source:
--   Carmona and Wang, Finite-State Contract Theory with a Principal and a Field of Agents, held PDF arXiv:1808.07942v1 (23 Aug 2018), §§2.3–2.6, (7)–(11), PDF pp. 4–5 = printed pp. 4–5; §3.3, (34), PDF p. 9 = printed p. 9; catalog DOI 10.1287/mnsc.2020.3760 (metadata basis published).

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FiniteStateContract.Equivalence
noncomputable section

/-- Graph of the signed extended Lebesgue integral. The indeterminate form
`∞ - ∞` and nonmeasurable integrands have no value; neither is assigned zero. -/
def IntegralValue {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → EReal) (v : EReal) : Prop :=
  AEMeasurable f μ ∧
  ((∫⁻ x, (f x).toENNReal ∂μ) ≠ ∞ ∨ (∫⁻ x, (-f x).toENNReal ∂μ) ≠ ∞) ∧
  v = (∫⁻ x, (f x).toENNReal ∂μ).toEReal -
    (∫⁻ x, (-f x).toENNReal ∂μ).toEReal

/-- An infimum of a partial family is defined only if every indexed value is
uniquely defined. Empty families have value `⊤`; unbounded-below families have `⊥`. -/
def InfimumValue {ι : Type*} (eligible : ι → Prop) (cost : ι → EReal → Prop)
    (v : EReal) : Prop :=
  (∀ i, eligible i → ∃! c, cost i c) ∧
    v = sInf {c | ∃ i, eligible i ∧ cost i c}

/-- Graph of a genuine inverse at a point: there must be exactly one preimage. -/
def InverseValue (U : ℝ → ℝ) (y x : ℝ) : Prop :=
  U x = y ∧ ∀ x', U x' = y → x' = x

end
end FiniteStateContract.Equivalence


