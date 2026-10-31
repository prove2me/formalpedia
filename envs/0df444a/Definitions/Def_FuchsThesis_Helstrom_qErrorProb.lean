-- Prove2me | Definitions.Def_FuchsThesis_Helstrom_qErrorProb
-- name    : FuchsThesis_Helstrom_qErrorProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:31.391438+00:00
-- url     : https://prove2.me/theorems/b330abce-1631-4bba-9ae7-b2f210bdf0bf
-- title:
--   Quantum error probability $P_e(\hat\rho_0|\hat\rho_1)$ (eq. 3.9)
-- statement:
--   A quantum system is secretly prepared in the state $\hat\rho_0$ with prior probability $\pi_0$ or in the state $\hat\rho_1$ with prior probability $\pi_1$. An observer performs any measurement, described by a POVM $\{\hat E_b\}$ (positive semidefinite operators with $\sum_b \hat E_b = \hat{\mathbb 1}$, any finite number of outcomes), and then guesses the state. The **quantum error probability** is the smallest achievable expected probability of a wrong guess:
--
--   $$
--   P_e(\hat\rho_0|\hat\rho_1) \equiv \min_{\{\hat E_b\}} \sum_b \min\big\{\pi_0\,\mathrm{tr}(\hat\rho_0\hat E_b),\ \pi_1\,\mathrm{tr}(\hat\rho_1\hat E_b)\big\}.
--   $$
--
--   It is the measure of distinguishability of two quantum states based on the probability of error; the smaller it is, the more distinguishable the states.
--
--   **Formalization Note** The minimum is formalized as the infimum (`sInf` in $\mathbb R$) of the set of values over every POVM `E : Fin m → Matrix n n ℂ` with any number $m$ of outcomes. The set is nonempty (it contains the value $\min\{\pi_0,\pi_1\}$ of the one-outcome POVM $\{\hat{\mathbb 1}\}$) and, for nonnegative priors and density operators, bounded below by $0$, so the infimum is not a junk value. That the infimum is attained is asserted in the theorems, not built into the definition.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.9), p.44 (PDF p.53); POVM definition (1.33)–(1.34), p.11 (PDF p.20)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Helstrom_bayesError

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.9), p.44 (PDF p.53): the **quantum error probability**
`P_e(ρ̂₀|ρ̂₁) ≡ min_{Ê_b} ∑_b min{π₀ tr(ρ̂₀Ê_b), π₁ tr(ρ̂₁Ê_b)}`, the minimum over all POVMs `{Ê_b}`
(p.11, PDF p.20: `Ê_b ≥ 0`, `∑_b Ê_b = 1̂`, "there can be arbitrarily many" outcomes).

**Formalization Note.** The source's `min` is the infimum (`sInf` in `ℝ`) of the *set* of values
`bayesError π₀ π₁ ρ₀ ρ₁ E` over every POVM `E : Fin m → Matrix n n ℂ` (`FuchsVdGraaf.IsPOVM`) with any
number `m` of outcomes. The set contains the value of the one-outcome POVM `![1]`, so it is
nonempty, and for nonnegative priors and density matrices its elements are nonnegative, so the
`sInf` is the true infimum. That the infimum is attained (the source's "min") is asserted
separately in the theorems. -/
noncomputable def qErrorProb {n : Type} [Fintype n] [DecidableEq n] (π0 π1 : ℝ)
    (ρ0 ρ1 : Matrix n n ℂ) : ℝ :=
  sInf {v : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ),
    FuchsVdGraaf.IsPOVM E ∧ v = bayesError π0 π1 ρ0 ρ1 E}

end FuchsThesis.Helstrom


