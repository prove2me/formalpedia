-- Prove2me | Definitions.Def_DecDynMatch_IsPOSM
-- name    : DecDynMatch_IsPOSM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:04.418571+00:00
-- url     : https://prove2.me/theorems/467fd976-9989-454d-aec1-bb3c4ce6fa40
-- title:
--   Stability and the player-optimal stable matching (unbalanced market)
-- statement:
--   Fix a round $t$. A **matching** $m$ assigns to each player $i$ either an arm $m(i)\in\mathcal K$ or $m(i)=\bot$, such that only active players ($i\in P_t$) are matched and no arm is assigned to two players. Player $i$ **prefers** arm $k$ to its partner if $i$ is unmatched or $\mu_{i,k}>\mu_{i,m(i)}$; arm $k$ **prefers** player $i$ to its partner if no player holds $k$ or $\pi_{k,i}>\pi_{k,j}$ for the player $j$ holding $k$. A pair $(i,k)\in P_t\times\mathcal K$ **blocks** $m$ if both prefer each other to their partners.
--
--   A matching is **stable** at $t$ if every active player is matched and no pair blocks it. A **player-optimal stable matching** (POSM) is a stable matching $m^*_t$ such that
--   $$
--   \mu_{i,m^*_t(i)}\ \ge\ \mu_{i,m(i)}\qquad\text{for every } i\in P_t \text{ and every stable matching } m .
--   $$
--   Since $|P_t|\le K$, arms may stay unmatched; this is the unbalanced setting of the paper. The POSM is unique, and the mismatch cost of the mission counts the rounds in which the realized matching is not the POSM.
--
--   **Formalization Note** Matchings are maps `ι → Option (Fin K)`. `IsPOSM I t m` is a predicate (no matching is chosen); uniqueness, proved separately, makes "$M_t\ne m^*_t$" the same as "$M_t$ is not a POSM".
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.1, p.4

import Mathlib
import Definitions.Def_DecDynMatch_Instance

namespace DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- `m` is a matching at round `t`: only active players are matched, and no arm is matched to two
players (§2.1, p.4: "a matching m consists of disjoint player-arm pairs from Pₜ × 𝒦"). A matching
is a map `m : ι → Option (Fin K)`, `m i = none` meaning `m(i) = ⊥`. -/
def IsMatchingAt (I : Instance K ι) (t : ℕ) (m : ι → Option (Fin K)) : Prop :=
  (∀ i, m i ≠ none → i ∈ active I t) ∧ (∀ i j k, m i = some k → m j = some k → i = j)

/-- Player `i` prefers arm `k` to its partner under `m` (an unmatched player prefers every arm). -/
def PlayerPrefers (I : Instance K ι) (i : ι) (k : Fin K) (m : ι → Option (Fin K)) : Prop :=
  ∀ k', m i = some k' → I.μ i k' < I.μ i k

/-- Arm `k` prefers player `i` to its partner under `m` (an unmatched arm prefers every player). -/
def ArmPrefers (I : Instance K ι) (k : Fin K) (i : ι) (m : ι → Option (Fin K)) : Prop :=
  ∀ j, m j = some k → I.π k j < I.π k i

/-- Stability at round `t` (§2.1, p.4): "A pair (i, k) is a blocking pair of m if player i and arm k
prefer each other to their respective partners under m. A matching is stable if all active players
are matched and no blocking pair exists." Blocking pairs range over `Pₜ × 𝒦`. -/
def IsStable (I : Instance K ι) (t : ℕ) (m : ι → Option (Fin K)) : Prop :=
  IsMatchingAt I t m ∧ (∀ i ∈ active I t, m i ≠ none) ∧
    ∀ i ∈ active I t, ∀ k, ¬ (PlayerPrefers I i k m ∧ ArmPrefers I k i m)

/-- **Player-optimal stable matching (POSM).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic
Stable Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.1, p.4: "Among all stable
matchings at round t, the player-optimal stable matching (POSM), denoted by m*ₜ, assigns each
active player its most preferred arm attainable in any stable matching:
μ_{i,m*ₜ(i)} ≥ μ_{i,m(i)} for every i ∈ Pₜ and stable matching m."

`IsPOSM I t m` says that `m` is stable at round `t` and every active player weakly prefers its arm
under `m` to its arm under every stable matching.

**Formalization Note.** The POSM is a predicate rather than a chosen matching. Strict rankings make
it unique (two POSMs agree at every player), so "`Mₜ ≠ m*ₜ`" is "`Mₜ` is not a POSM at `t`". -/
def IsPOSM (I : Instance K ι) (t : ℕ) (m : ι → Option (Fin K)) : Prop :=
  IsStable I t m ∧
    ∀ m', IsStable I t m' → ∀ i ∈ active I t, ∀ k k', m i = some k → m' i = some k' →
      I.μ i k' ≤ I.μ i k

end DecDynMatch


