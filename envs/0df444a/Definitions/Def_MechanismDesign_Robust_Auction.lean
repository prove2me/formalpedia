-- Prove2me | Definitions.Def_MechanismDesign_Robust_Auction
-- name    : MechanismDesign_Robust_Auction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T05:05:19.258594+00:00
-- url     : https://prove2.me/theorems/abaf07ef-5a6f-4fcf-b954-07b76127c6a8
-- title:
--   The single unit auction problem: values, outcomes and quasi-linear utilities
-- statement:
--   In the single unit auction problem (§3.2.1) a seller has one indivisible good and there are $N$ potential buyers $i \in I$. Buyer $i$'s payoff type is her value $\theta_i \in [\underline\theta, \overline\theta]$, where $0 \le \underline\theta < \overline\theta$. An outcome is a pair $(a, t)$ where $a \in \{0\} \cup I$ says who receives the good ($0$: the seller keeps it) and $t = (t_1,\dots,t_N) \in \mathbb R^N$ are the transfers paid by the buyers (§3.2.2). Buyer $i$'s utility is
--
--   $$u_i((a,t),\theta) = \begin{cases} \theta_i - t_i & \text{if } a = i,\\ -t_i & \text{otherwise.}\end{cases}$$
--
--   This is the environment of Propositions 10.10 and 10.11.
--
--   **Formalization Note** The payoff type set of every buyer is the subtype `Set.Icc lo hi`; the hypotheses `0 ≤ lo < hi` are stated in the theorems. Outcomes are `Option ι × (ι → ℝ)` with `none` for "not sold".
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.31–33, §§3.2.1–3.2.2; p.194, §10.10

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

namespace MechanismDesign.Robust

variable {ι : Type} [DecidableEq ι]

/-- The payoff types of the single unit auction problem (§3.2.1, p.31): buyer `i`'s value
`θ_i ∈ [θ̲, θ̄]`, where `0 ≤ θ̲ < θ̄` (the hypotheses on `lo`, `hi` are stated where used). -/
abbrev AuctionValue (ι : Type) (lo hi : ℝ) : ι → Type := fun _ => Set.Icc lo hi

/-- Outcomes of the single unit auction problem (§3.2.2, p.33): who receives the good
(`none`: the seller keeps it) and the vector of transfers `t_i` paid by the buyers. -/
abbrev AuctionOutcome (ι : Type) : Type := Option ι × (ι → ℝ)

/-- Buyer `i`'s utility `θ_i − t_i` if she receives the good and `−t_i` otherwise (p.31). -/
def auctionUtility (lo hi : ℝ) : ι → AuctionOutcome ι → (∀ i, AuctionValue ι lo hi i) → ℝ :=
  fun i x θ => (if x.1 = some i then ((θ i : Set.Icc lo hi) : ℝ) else 0) - x.2 i

end MechanismDesign.Robust


