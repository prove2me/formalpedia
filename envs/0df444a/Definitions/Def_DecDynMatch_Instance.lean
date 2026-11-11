-- Prove2me | Definitions.Def_DecDynMatch_Instance
-- name    : DecDynMatch_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:10.915555+00:00
-- url     : https://prove2.me/theorems/e1cd3350-eb10-4d6c-924f-c97f5f18f708
-- title:
--   Dynamic matching instance with $K\ge 2$ arms and unannounced arrivals and departures
-- statement:
--   A **dynamic matching instance** on $K\ge 2$ arms $\mathcal K=\{0,1,\dots,K-1\}$ consists of a finite set $\iota$ of players (every player that is ever active), and for each player $i$ an entry round $b_i\ge 1$ and a departure round $d_i\in\{b_i+1,b_i+2,\dots\}\cup\{\infty\}$. Player $i$ is **active** in round $t$ when $b_i\le t<d_i$, and the active set is
--   $$
--   P_t=\{\,i : b_i\le t<d_i\,\},\qquad |P_t|\le K\ \text{ for every } t .
--   $$
--   Each player $i$ has utilities $\mu_{i,k}$ for the arms and each arm $k$ has utilities $\pi_{k,i}$ for the players; both are injective, so they encode complete strict rankings ($k\succ_i \ell \iff \mu_{i,k}>\mu_{i,\ell}$, $i\succ_k j\iff \pi_{k,i}>\pi_{k,j}$). An arm ranks every player ever active.
--
--   Round $t$ has a **population event** if some player arrives ($b_i=t$) or departs ($d_i=t$) at $t$; round $1$ always counts as an event. The **last population-event time** is
--   $$
--   t^*=\max\bigl(\{1\}\cup\{b_i\}\cup\{d_i : d_i<\infty\}\bigr).
--   $$
--   Arm $0$ plays the role BUS and arm $1$ the role PARK in the protocol.
--
--   This is the market of every statement of the mission; the final market $P_{t^*}$ may be empty.
--
--   **Formalization Note** Players are a `Fintype`, departures are in `ℕ∞` (`⊤` for $\infty$), and $K\ge 2$ is a field of the structure. The paper's range $[0,1]$ for utilities is not imposed: only the rankings matter, and every $[0,1]$-valued instance is an instance here. `active`, `IsEvent`, `NoEventIn` (no event in a range of rounds), `tstar`, `bus` and `park` are defined alongside.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.1, p.4; §2.3, p.5

import Mathlib

namespace DecDynMatch

/-- **Dynamic matching instance (known preferences).** J. Chen, M. Gao, Z. Zhang, *Decentralized
Dynamic Stable Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.1, p.4, and §2.3,
p.5: "We consider a dynamic two-sided matching market with K ≥ 2 fixed arms, indexed by
𝒦 = {0, 1, …, K − 1} … Each player i enters at round bᵢ ≥ 1 and departs at round dᵢ > bᵢ, with
dᵢ = ∞ if the player never leaves. The set of active players at round t is
Pₜ = {i : bᵢ ≤ t < dᵢ}, and |Pₜ| ≤ K for all t. We consider markets with finitely many player
arrivals and departures. … For each player i, the utility of arm k is μᵢ,ₖ …; for each arm k, the
utility of player i is πₖ,ᵢ … Moreover, an arm's ranking is over all players who are ever active
at any time in the instance."

An instance on `K` arms (`Fin K`, arm `k` is the paper's arm `k`) and the type `ι` of every player
ever active consists of entry rounds `b`, departure rounds `d` (`⊤` = never departs), the player
utilities `μ i k` and the arm utilities `π k i`.

**Formalization Note.**
* `K ≥ 2` is a field: arm 0 (BUS) and arm 1 (PARK) of the protocol need it.
* "Finitely many arrivals and departures" is the finiteness of `ι` (`[Fintype ι]`); each player
  enters once and departs at most once.
* `d i : ℕ∞`, with `⊤` for `dᵢ = ∞`.
* Strict rankings are injectivity of `μ i` and of `π k`. The paper's range `[0, 1]` for the
  utilities is not imposed: only the rankings they induce enter any definition, and every
  `[0, 1]`-valued instance is an instance here.
* `|Pₜ| ≤ K` is required for every `t : ℕ` (at `t = 0` the set is empty since `bᵢ ≥ 1`). -/
structure Instance (K : ℕ) (ι : Type*) [Fintype ι] where
  /-- entry round `bᵢ` -/
  b : ι → ℕ
  /-- departure round `dᵢ` (`⊤` if the player never leaves) -/
  d : ι → ℕ∞
  /-- player utilities `μᵢ,ₖ` -/
  μ : ι → Fin K → ℝ
  /-- arm utilities `πₖ,ᵢ` -/
  π : Fin K → ι → ℝ
  two_le : 2 ≤ K
  one_le_b : ∀ i, 1 ≤ b i
  b_lt_d : ∀ i, (b i : ℕ∞) < d i
  μ_injective : ∀ i, Function.Injective (μ i)
  π_injective : ∀ k, Function.Injective (π k)
  card_active_le : ∀ t : ℕ, (Finset.univ.filter (fun i => b i ≤ t ∧ (t : ℕ∞) < d i)).card ≤ K

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- The active set `Pₜ = {i : bᵢ ≤ t < dᵢ}` (§2.1, p.4). -/
def active (I : Instance K ι) (t : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => I.b i ≤ t ∧ (t : ℕ∞) < I.d i)

/-- Round `t` has a population event (§2.1, p.4): "Round t has a population event if some players
arrive or depart at t. The initial market is considered as a population event in round 1." -/
def IsEvent (I : Instance K ι) (t : ℕ) : Prop :=
  t = 1 ∨ ∃ i, I.b i = t ∨ I.d i = (t : ℕ∞)

/-- No population event occurs in the rounds `a ≤ t < e`. -/
def NoEventIn (I : Instance K ι) (a e : ℕ) : Prop :=
  ∀ t, a ≤ t → t < e → ¬ IsEvent I t

/-- The last population-event time `t*` (§2.1, p.4): the largest of `1`, the entry rounds `bᵢ`
and the finite departure rounds `dᵢ`. (`ENat.toNat ⊤ = 0`, so a player that never departs
contributes only its entry round.) -/
def tstar (I : Instance K ι) : ℕ :=
  max 1 (max (Finset.univ.sup I.b) (Finset.univ.sup fun i => (I.d i).toNat))

/-- Arm `0`, the protocol's BUS (§3.1, p.5). -/
def bus (I : Instance K ι) : Fin K := ⟨0, by have := I.two_le; omega⟩

/-- Arm `1`, the protocol's PARK (§3.1, p.5). -/
def park (I : Instance K ι) : Fin K := ⟨1, by have := I.two_le; omega⟩

end DecDynMatch


