-- Prove2me | Definitions.Def_ReferencePricing_Myopic_myopicPrice
-- name    : ReferencePricing_Myopic_myopicPrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:23:22.757713+00:00
-- url     : https://prove2.me/theorems/fc93885d-d5bf-47cd-9d0e-33dd30b7f47f
-- title:
--   Myopic price p̃(r) (largest maximizer of the single-period profit) and the myopic firm's state and price paths
-- statement:
--   The **myopic price** is the largest single-period profit maximizer,
--   $$\tilde p(r) = \max\,\operatorname*{arg\,max}_{p \in P} \Pi(p, r).$$
--   A myopic firm starting from reference price $r_0$ charges $p^M_t = \tilde p(r^M_t)$, and consumers' memory evolves by (1):
--   $$r^M_0 = r_0, \qquad r^M_{t+1} = \alpha\, r^M_t + (1 - \alpha)\, \tilde p(r^M_t).$$
--
--   This is the firm that ignores the effect of today's price on future reference prices; it is compared with the strategic firm of the optimal policy.
--
--   **Formalization Note.** As for $p^*$, "argmax" is the largest maximizer, encoded as the `sSup` of the set of maximizers of $\Pi(\cdot, r)$ over $P$ (nonempty under Assumption 1, to be proved). The paper remarks that the myopic problem is problem (2) with $\beta = 0$; that remark is motivation, and $\tilde p$ is defined directly as the argmax of $\Pi$, as the paper's Lemma 1 does.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 418, Section 4.1 (Lemma 1 and the following paragraph)

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Model

namespace ReferencePricing.Myopic

/-- The single-period profit-maximizing (myopic) price `p̃(r) = argmax_{p ∈ P} Π(p, r)` (p. 418),
with the paper's convention (p. 417) that `argmax` is the largest maximizer: the supremum of the
set of maximizers of `Π(·, r)` over `P = [0, p̄]`. -/
noncomputable def myopicPrice (prof : ℝ → ℝ → ℝ) (pbar r : ℝ) : ℝ :=
  sSup {p | p ∈ Set.Icc (0 : ℝ) pbar ∧ ∀ p' ∈ Set.Icc (0 : ℝ) pbar, prof p' r ≤ prof p r}

/-- The myopic firm's state path (p. 418): `r^M_0 = r₀`,
`r^M_{t+1} = α r^M_t + (1 - α) p̃(r^M_t)`, i.e. memory (1) driven by the myopic prices. -/
noncomputable def myopicState (prof : ℝ → ℝ → ℝ) (α pbar r₀ : ℝ) : ℕ → ℝ
  | 0 => r₀
  | t + 1 => α * myopicState prof α pbar r₀ t + (1 - α) * myopicPrice prof pbar (myopicState prof α pbar r₀ t)

/-- The myopic firm's price path (p. 418): `p^M_t = p̃(r^M_t)`. -/
noncomputable def myopicPricePath (prof : ℝ → ℝ → ℝ) (α pbar r₀ : ℝ) (t : ℕ) : ℝ :=
  myopicPrice prof pbar (myopicState prof α pbar r₀ t)

end ReferencePricing.Myopic


