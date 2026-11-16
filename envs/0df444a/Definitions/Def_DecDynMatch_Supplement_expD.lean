-- Prove2me | Definitions.Def_DecDynMatch_Supplement_expD
-- name    : DecDynMatch_Supplement_expD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:24:18.963239+00:00
-- url     : https://prove2.me/theorems/81b628cd-9f08-4ece-9037-441cb3c1e6bc
-- title:
--   Expected cumulative POSM mismatch $\mathbb E[D_\Pi(T;I)]$ of a randomized protocol
-- statement:
--   Run a randomized protocol $\Pi$ on an instance $I$: in each round $t=1,2,\dots$ every active player draws its proposal from its rule, independently of the others, given its own local history; each arm accepts its most preferred current proposer (by $\pi$); every active player appends its proposal and outcome to its history, and a player enters at round $b_i$ with an empty history. With $M_t$ the realized matching and $m^*_t$ the player-optimal stable matching of round $t$,
--   $$
--   \mathbb E[D_\Pi(T;I)]=\sum_{t=1}^{T}\Pr\bigl[M_t\neq m^*_t\bigr].
--   $$
--   This is the expected cost in the lower bounds (Theorem 3).
--
--   **Formalization Note** The law of round $t$ is built from finite products of probability mass functions (`pmfPi`) composed round by round (`histLaw`), so no measure theory is needed; the sum of probabilities is the expectation by linearity. "$M_t\ne m^*_t$" is "$M_t$ is not a POSM" (`IsPOSM`), as in the base mission. Acceptance is the base `acceptedBy`.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (1), p.5; §2.2, p.4

import Mathlib
import Definitions.Def_DecDynMatch_IsPOSM
import Definitions.Def_DecDynMatch_exec
import Definitions.Def_DecDynMatch_Supplement_Protocol

namespace DecDynMatch.Supplement

open DecDynMatch

/-- The independent product of finitely many probability mass functions on a finite type. -/
noncomputable def pmfPi {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (p : ι → PMF α) : PMF (ι → α) :=
  PMF.ofFintype (fun x => ∏ i, p i (x i)) (by
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    refine Finset.prod_eq_one (fun i _ => ?_)
    have h := PMF.tsum_coe (p i)
    rwa [tsum_fintype] at h)

variable {K : ℕ} {ι : Type*} [Fintype ι]

open Classical in
/-- The law of the proposal profile of a round, given every player's history: players draw their
proposals independently (private randomness). Proposals of inactive players are drawn but never
used (they do not reach any arm). -/
noncomputable def propLaw (P : Protocol K) (I : Instance K ι) (h : ι → History K) :
    PMF (ι → Fin K) :=
  pmfPi (fun i => P.rule (I.μ i) (h i))

open Classical in
/-- The realized matching of round `t` under the proposal profile `x`: player `i` is matched to
`x i` iff it is active and preferred by arm `x i` to every other active proposer (`acceptedBy`
of the base mission: "each arm accepts its most preferred current proposer"). -/
noncomputable def realized (I : Instance K ι) (t : ℕ) (x : ι → Fin K) : ι → Option (Fin K) :=
  fun i => if acceptedBy I t x i then some (x i) else none

open Classical in
/-- Histories after round `t`: an active player appends its proposal and outcome (with realized
utility `μᵢ,ₖ` on acceptance); an inactive player holds the empty history, so a player enters at
`bᵢ` with an empty history and local clock 0. -/
noncomputable def nextHist (I : Instance K ι) (t : ℕ) (h : ι → History K) (x : ι → Fin K) :
    ι → History K :=
  fun i => if i ∈ active I t then
      h i ++ [(x i, if acceptedBy I t x i then some (I.μ i (x i)) else none)]
    else []

/-- The law of the history profile before round `t` (rounds are `1, 2, …`; round `0` has no active
player since `bᵢ ≥ 1`). -/
noncomputable def histLaw (P : Protocol K) (I : Instance K ι) : ℕ → PMF (ι → History K)
  | 0 => PMF.pure (fun _ => [])
  | t + 1 => (histLaw P I t).bind (fun h => (propLaw P I h).map (nextHist I t h))

/-- `Pr[Mₜ ≠ m*ₜ]`: the probability that the realized matching of round `t` is not the POSM. -/
noncomputable def mismatchProb (P : Protocol K) (I : Instance K ι) (t : ℕ) : ENNReal :=
  ((histLaw P I t).bind (propLaw P I)).toOuterMeasure
    {x | ¬ IsPOSM I t (realized I t x)}

/-- **Expected cumulative POSM mismatch of a randomized protocol.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), eq. (1), p.5:
"D_Π(T; I) = Σ_{t=1}^{T} 1{Mₜ ≠ m*ₜ}", and p.5: "When protocol decisions … are randomized, we
consider the expected mismatch cost E[D_Π(T; I)]."

`expD P I T = Σ_{t=1}^{T} Pr[¬ IsPOSM I t Mₜ]` for the execution of protocol `P` on instance `I`:
every active player draws its proposal from its rule independently, arms accept their most preferred
current proposer, and players append their own proposal and outcome to their local history.

**Formalization Note.** By linearity, `E[D] = Σₜ Pr[Mₜ ≠ m*ₜ]`; the law of round `t` is a finite
product of PMFs composed `t` times, so no measure theory is needed. "`Mₜ ≠ m*ₜ`" is
"`Mₜ` is not a POSM" as in the base mission (the POSM is unique). -/
noncomputable def expD (P : Protocol K) (I : Instance K ι) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (mismatchProb P I t).toReal

end DecDynMatch.Supplement


