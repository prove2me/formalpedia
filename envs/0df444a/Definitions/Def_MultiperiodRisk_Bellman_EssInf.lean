-- Prove2me | Definitions.Def_MultiperiodRisk_Bellman_EssInf
-- name    : MultiperiodRisk_Bellman_EssInf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:01:35.300012+00:00
-- url     : https://prove2.me/theorems/4633693d-258c-436e-8d71-cd9ac9817a91
-- title:
--   Essential infimum of a family of random variables
-- statement:
--   Let $\mu$ be a measure on $(\Omega,\mathcal F)$, let $\mathcal H\subseteq\mathcal F$ be a sub-σ-algebra and let $S$ be a family of real random variables. A function $g$ is an **essential infimum** of $S$ (relative to $\mathcal H$ and $\mu$) if
--
--   1. $g$ is $\mathcal H$-measurable;
--   2. $g\le h$ $\mu$-a.e. for every $h\in S$;
--   3. every $\mathcal H$-measurable $g'$ with $g'\le h$ $\mu$-a.e. for all $h\in S$ satisfies $g'\le g$ $\mu$-a.e.
--
--   It is written
--   $$
--   \operatorname*{ess.inf}_{h\in S} h ,
--   $$
--   and is unique up to $\mu$-null sets. The file also fixes one choice of it: $\operatorname{essInfFamily}(\mu,\mathcal H,S)$ is an essential infimum when one exists.
--
--   The paper uses this notion (Neveu 1972, Proposition VI-1-1, cited on p. 10) in both constructions of risk-adjusted values: $\Psi_\sigma(X)$ of Theorem 4.2 and the recursion for $\bar\Psi(X)$ of Theorem 4.1.
--
--   **Formalization Note** Mathlib's `essInf` is the essential infimum of one function, not of a family, so the family version is defined here. When no essential infimum exists the chosen value is the junk value $0$; in every use in this mission the family is nonempty and a.e. bounded below, so an essential infimum exists (the item `psi_isEssInf` states this for $\Psi$).
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 10, §4.1 (reference to Neveu 1972, Propositions VI.1.1 and VI-1-2, for the essential infimum)

import Mathlib

namespace MultiperiodRisk.Bellman

open MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- `g` is an essential infimum of the family `S` of real functions, relative to the
sub-σ-algebra `m'` and the measure `μ`: the greatest `m'`-measurable function that is
`μ`-a.e. below every member of `S`. -/
def IsEssInf (μ : Measure Ω) (m' : MeasurableSpace Ω) (S : Set (Ω → ℝ)) (g : Ω → ℝ) : Prop :=
  StronglyMeasurable[m'] g ∧ (∀ h ∈ S, g ≤ᵐ[μ] h) ∧
    ∀ g' : Ω → ℝ, StronglyMeasurable[m'] g' → (∀ h ∈ S, g' ≤ᵐ[μ] h) → g' ≤ᵐ[μ] g

/-- A chosen essential infimum of the family `S` (unique up to `μ`-null sets). The fallback
value `0` is used only when no essential infimum exists. -/
noncomputable def essInfFamily (μ : Measure Ω) (m' : MeasurableSpace Ω) (S : Set (Ω → ℝ)) :
    Ω → ℝ := by
  classical
  exact if h : ∃ g, IsEssInf μ m' S g then h.choose else 0

end MultiperiodRisk.Bellman


