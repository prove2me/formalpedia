-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_Efficiency
-- name    : ProcurementPoA_DeterministicCap_Efficiency
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:27.712016+00:00
-- url     : https://prove2.me/theorems/64549528-8b02-46de-aa1c-b9de75a8808f
-- title:
--   Worst-case equilibrium price of anarchy
-- statement:
--   For real endpoints $L,U$ and a deterministic cap $T$, let $\mathcal Q_{L,U,T}$ contain exactly the ratios $\mathrm{SC}/\mathrm{SC}_{\mathrm{OPT}}$ obtained from independent private-cost instances on $[L,U]$, all their no-underbidding mixed Bayes–Nash equilibria, and every admissible measurable tie rule. Every nonempty finite supplier population is included. Define
--
--   $$\operatorname{PoA}_{[L,U]}(M_T)=\sup\mathcal Q_{L,U,T},\qquad \operatorname{PoA}_R(M_T)=\operatorname{PoA}_{[1,R]}(M_T).$$
--
--   Instances with no equilibrium contribute no ratio. The cap is fixed before taking this supremum and cannot depend on the private-cost laws. This is a ratio of expectations, and tightness may be approached rather than attained.
--
--   **Formalization Note** The supremum and ratios use the complete ordered nonnegative extended reals. An unbounded supremum is $+\infty$ and the empty supremum is $0$, without the real supremum's unbounded-set default. On the theorem domain, nonemptiness, positive denominators and finiteness are consequences of the actual probability model and the stated identities, rather than assumptions built into this definition.
-- source:
--   Simone Palazzotto, Andrés Cristi, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, §2, printed p. 4 (PDF p. 6); Definition 5.1 and following PoA display, printed p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Auction

namespace ProcurementPoA.DeterministicCap

/-- All equilibrium ratios over every nonempty finite population, independent
cost laws in [L,U], mixed BNE, and all measurable lowest-bid tie rules.
An instance without an equilibrium contributes no element. -/
def equilibriumRatios (L U T : ℝ) : Set ENNReal :=
  {q | ∃ (n : ℕ) (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n),
    InCostInterval D L U ∧ IsBNE D τ σ T ∧
      q = socialCost D τ σ U T / optimalSocialCost D}

/-- A complete-lattice supremum, so unbounded sets retain +∞ rather than 0.
For positive cost intervals the finiteness and nonemptiness are mathematical
facts, not hypotheses built into the definition. -/
noncomputable def poaOn (L U T : ℝ) : ENNReal := sSup (equilibriumRatios L U T)

/-- The source's normalization c = 1, outside-option cost R. -/
noncomputable def poa (R T : ℝ) : ENNReal := poaOn 1 R T

end ProcurementPoA.DeterministicCap


