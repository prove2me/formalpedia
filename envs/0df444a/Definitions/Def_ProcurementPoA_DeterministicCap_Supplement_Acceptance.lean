-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Acceptance
-- name    : ProcurementPoA_DeterministicCap_Supplement_Acceptance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:32:56.617477+00:00
-- url     : https://prove2.me/theorems/73daed97-9d96-4e0a-970b-14b7324c27ac
-- title:
--   Acceptance functions and their procurement auction
-- statement:
--   An acceptance function for an outside-option cost $R$ is the survival function of a Borel probability law $\mu$ on real phantom bids, with $\mu((R,\infty))=0$:
--   $$S(b)=\mu([b,\infty)).$$
--   This includes atoms and accepts equality with the phantom bid. Monotonicity, left continuity, the bounds $0\le S\le1$, and vanishing above $R$ follow from this definition.
--
--   A supplier with cost $c$ and bid $b$ earns $(b-c)x_i(b)S(b)$, where $x_i(b)$ is the published interim probability of winning among the real suppliers. Equilibrium means no underbidding and typewise best response against every real deviation. Conditional on the real bids and costs, the expected outcome cost is
--   $$S(b_{\min})\sum_i c_i\tau_i(b)+(1-S(b_{\min}))R.$$
--   Its expectation under the published independent type-and-bid law is the social cost. The outside option is used upon rejection, independently of the identity selected in a tie.
--
--   This definition is shared by the secret, announced, and partially disclosed phantom mechanisms. It contains no equilibrium-existence assumption or efficiency certificate.
--
--   **Formalization Note** The social-cost formula is used with costs in $[1,R]$ and is encoded by a nonnegative Lebesgue integral. The acceptance-function predicate requires an actual probability law rather than replacing the source's class with a continuity or density assumption.
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Definition 5.1 and §5.2, printed pp. 8–10 (PDF pp. 10–12)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

/-- The survival function of an arbitrary Borel phantom law bounded above by R.
Atoms are allowed and equality with the phantom bid is accepted. -/
def IsAcceptance (R : ℝ) (S : ℝ → ℝ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Ioi R) = 0 ∧
    ∀ b, S b = (μ (Set.Ici b)).toReal

noncomputable def acceptUtility {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (S : ℝ → ℝ) (i : Suppliers n) (c b : ℝ) : ℝ :=
  standardUtility D τ σ i c b * S b

/-- Every real deviation is tested; no efficiency promise is an equilibrium field. -/
def IsAcceptBNE {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (S : ℝ → ℝ) : Prop :=
  NoUnderbidding D σ ∧ IsTypewiseBestResponse D σ (acceptUtility D τ σ S)

noncomputable def acceptSocialCost {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (R : ℝ) (S : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, winnerCost τ x * ENNReal.ofReal (S (lowest (fun i => (x i).2))) +
    ENNReal.ofReal R * ENNReal.ofReal (1 - S (lowest (fun i => (x i).2)))
    ∂(playLaw D σ)

end ProcurementPoA.DeterministicCap.Supplement


