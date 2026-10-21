-- Prove2me | Definitions.Def_IncompleteProc_English_Auction
-- name    : IncompleteProc_English_Auction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:35.013668+00:00
-- url     : https://prove2.me/theorems/b2cf9ed7-e6fe-41c2-add8-937c0ba6e4f9
-- title:
--   §4, p. 10 and App. A.3, p. 18 — English auction with reserve c⋆1, the offer p2(ω, p1) = min{k(p1, ω), k(c⋆2(ω), ω)}, buyer surplus, winner payoff, eq. (9) objective
-- statement:
--   The incomplete-contract implementation of Proposition 3, built on the model definitions (the environment, $c^\star_1$, $c^\star_2$, $F$).
--
--   **English auction.** The price starts at the reserve $r^\star = c^\star_1$ and falls continuously. Suppliers exit at their costs ($\beta^E(c) = c$), and the last remaining supplier wins at the price at which his final opponent quit. So supplier $i$ wins iff his cost $c^i$ is the lowest and $c^i \le c^\star_1$, with ties going to the lowest index. His first-period price is
--   $$p_1 = \min\{c^\star_1, \min_{j \ne i} c^j\},$$
--   which is the reserve when $n = 1$.
--
--   **Take-it-or-leave-it offer.** After observing $p_1$ and the state $\omega$, the buyer offers the winner
--   $$p_2(\omega, p_1) = \min\{k(p_1, \omega), k(c^\star_2(\omega), \omega)\},$$
--   and the winner with cost $c$ accepts iff $p_2(\omega, p_1) \ge k(c, \omega)$.
--
--   **Derived quantities.**
--   1. The buyer's expected surplus in the English auction is $\mathbb E\big[(R - p_1) + \int_\Omega \mathbf 1\{k(c^{\mathrm{win}}, \omega) \le p_2\}\, Q\,(R - p_2(\omega, p_1))\, dG(\omega)\big]$, counted only when there is a winner.
--   2. A supplier with cost $c$ who wins at price $x$ and then best-responds to the offer earns
--   $$\mathrm{winPayoff}(c, x) = x - c + \int_\Omega Q \max\{0, p_2(\omega, x) - k(c, \omega)\}\, dG(\omega).$$
--   3. The buyer's second-period objective (9), for an auction that ended at price $p$ and a cutoff type $c \in [\underline c, p]$, is $Q\,(R - k(c, \omega))\, F(c)/F(p)$: the offer $k(c, \omega)$ is accepted by the types below $c$, and the buyer's belief is $F(c)/F(p)$ on $[\underline c, p]$.
--   4. The interim profit $U(c)$ of supplier $i$ with cost $c$ is the expectation of $\mathrm{winPayoff}(c, p_1)$ over the event that he wins, the others exiting truthfully.
--
--   **Formalization Note** Ties have probability zero (footnote 12). The lowest-index rule replaces the page's random selection, and no statement depends on it. The first-period price is the minimum of the reserve and the others' costs, computed by a fold, so it equals the reserve when $n = 1$ (no infimum over an empty set).
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), p. 10 (PDF 11), §4 (English auction, timing (1)–(6), footnote 12), Proposition 3; p. 18 (PDF 19), proof of Proposition 3, eq. (9) and U(c)

import Mathlib
import Definitions.Def_IncompleteProc_English_Model

namespace IncompleteProc.English

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- In the English auction with reserve price `r⋆ = c⋆₁` and truthful exit `β^E(c) = c` (p. 10),
supplier `i` wins iff his cost is at most the reserve and is the lowest (ties to the lowest
index; ties have probability zero). -/
def Env.wins (E : Env Ω) (C : Fin E.n → ℝ) (i : Fin E.n) : Prop :=
  C i ≤ E.cStar1 ∧ isLowest C i

/-- The first-period price `p₁` paid to supplier `i` when he wins: the price at which his final
opponent quits under truthful exit, i.e. the lowest cost among the other suppliers, capped at the
reserve `c⋆₁` (with one supplier, the reserve itself). -/
noncomputable def Env.p1 (E : Env Ω) (C : Fin E.n → ℝ) (i : Fin E.n) : ℝ :=
  (Finset.univ.erase i).fold min E.cStar1 C

/-- The take-it-or-leave-it offer of Proposition 3 (p. 10):
`p₂(ω, p₁) = min{k(p₁, ω), k(c⋆₂(ω), ω)}`. -/
noncomputable def Env.offer (E : Env Ω) (ω : Ω) (p : ℝ) : ℝ :=
  min (E.k p ω) (E.k (E.cStar2 ω) ω)

open Classical in
/-- The buyer's expected surplus in the English auction followed by the offer `p₂`: when supplier
`i` with cost `cⁱ` wins at price `p₁`, the buyer gets `R − p₁` in period 1 and, in state `ω`,
`Q (R − p₂(ω, p₁))` if the winner accepts, which he does iff `p₂(ω, p₁) ≥ k(cⁱ, ω)`. -/
noncomputable def Env.englishSurplus (E : Env Ω) : ℝ :=
  ∫ C, ∑ i, (if E.wins C i then
      (E.R - E.p1 C i) + ∫ ω, (if E.k (C i) ω ≤ E.offer ω (E.p1 C i)
                                then E.Q * (E.R - E.offer ω (E.p1 C i)) else 0) ∂E.G
    else 0) ∂E.profileLaw

/-- The payoff of a supplier with cost `c` who wins the auction at price `x` and then accepts the
offer `p₂(ω, x)` iff it covers his second-period cost:
`x − c + ∫_Ω Q max{0, p₂(ω, x) − k(c, ω)} dG(ω)`. -/
noncomputable def Env.winPayoff (E : Env Ω) (c x : ℝ) : ℝ :=
  x - c + ∫ ω, E.Q * max 0 (E.offer ω x - E.k c ω) ∂E.G

/-- The objective of the buyer's second-period problem (9) (p. 18): offering `k(c, ω)`, accepted
by the types below `c`, against the right-truncated belief `F(c)/F(p)` on `[c̲, p]`:
`Q (R − k(c, ω)) F(c)/F(p)`. -/
noncomputable def Env.offerValue (E : Env Ω) (ω : Ω) (p c : ℝ) : ℝ :=
  E.Q * (E.R - E.k c ω) * (E.F c / E.F p)

open Classical in
/-- The interim expected profit `U(c)` of supplier `i` with cost `c` in the English auction when the
other suppliers exit truthfully (pp. 18–19). -/
noncomputable def Env.englishU (E : Env Ω) (i : Fin E.n) (c : ℝ) : ℝ :=
  ∫ C, (if E.wins (Function.update C i c) i then
      E.winPayoff c (E.p1 (Function.update C i c) i) else 0) ∂E.profileLaw

end IncompleteProc.English


