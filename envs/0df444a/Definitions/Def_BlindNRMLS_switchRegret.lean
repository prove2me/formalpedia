-- Prove2me | Definitions.Def_BlindNRMLS_switchRegret
-- name    : BlindNRMLS_switchRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:20.71945+00:00
-- url     : https://prove2.me/theorems/350a7d96-a2e6-404c-860e-5a5112ccb519
-- title:
--   §2, §4, pp.8–9, 13–14, ec22 — revenue, switches, $\Phi[s]$, $\Pi_Q[s]$, $R^\phi_s(T)$, $R^\phi(T)$
-- statement:
--   On a history, cumulative consumption of resource $i$ through period $u$ is $\sum_{v\le u}\sum_j a_{ij}Q^v_j$. Period $t$ is **in the selling horizon** when no period up to $t$ stopped and no resource's cumulative consumption through any such period exceeds its inventory. Revenue is the sum of $\sum_j p_{j,z_t}Q^t_j$ over the selling horizon, and $\mathrm{Rev}_Q(\phi)$ is its expectation. A **switch** is a selling period $t$ with $z_t\ne z_{t+1}$ whose successor posts a price vector.
--
--   - $\Phi[s]$ is the set of learning policies with at most $s$ switches almost surely under **every** $Q$.
--   - $\Pi_Q[s]$ is the set of clairvoyant policies with at most $s$ switches almost surely under **that** $Q$.
--
--   The regrets are
--   $$
--   R^\phi_s(T)=\sup_Q\Big(\sup_{\pi\in\Pi_Q[s]}\mathrm{Rev}_Q(\pi)-\mathrm{Rev}_Q(\phi)\Big),\qquad R^\phi(T)=\sup_Q\Big(\sup_{\pi}\mathrm{Rev}_Q(\pi)-\mathrm{Rev}_Q(\phi)\Big).
--   $$
--   The **optimal regret** of §4.3 is the minimax value $\inf_{\phi\in\Phi[s]}R^\phi_s(T)$, and we also define $\inf_{\phi\in\Phi[s]}R^\phi(T)$.
--
--   **Formalization Note** The period that first exceeds an inventory earns nothing. All suprema and infima are over nonempty sets (the policy that always stops is in every class) and are bounded by $T\sum_{k,j}p_{j,k}$; revenue is integrable. A switch into the violating period counts, since the price is posted before demand is seen.
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, §2, pp.8–9; §4, pp.13–14; effective horizon, p.ec22; §4.3, p.21

import Mathlib
import Definitions.Def_BlindNRMLS_Policy

open MeasureTheory

namespace BlindNRMLS

variable {d n K : ℕ}

/-- Cumulative consumption of resource `i` through period `u`: `∑_{v ≤ u} ∑_j a_{ij} Q_j^v`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, p.8 and the display of the effective horizon, p.ec22. -/
def consumed (P : Problem d n K) {m : ℕ} (h : History n K m) (u : Fin m) (i : Fin d) : ℝ :=
  ∑ v ∈ Finset.Iic u, ∑ j, P.A i j * (h v).2 j

/-- Period `t` lies in the selling horizon: no earlier or current period stopped, and no resource's
cumulative consumption through any such period exceeds its inventory (pp.8, ec22).

**Formalization Note.** The period in which consumption first exceeds an inventory is not selling.
It earns no revenue: the page's effective horizon `τ` ends just before it. -/
def Sells (P : Problem d n K) {m : ℕ} (h : History n K m) (t : Fin m) : Prop :=
  ∀ u ≤ t, (h u).1 ≠ none ∧ ∀ i, consumed P h u i ≤ P.B i

/-- The revenue `∑_j p_{j,k} Q_j` of one period under action `some k`; `0` under `none`. -/
def periodRevenue (P : Problem d n K) (a : Action K) (q : Fin n → ℝ) : ℝ :=
  match a with
  | none => 0
  | some k => ∑ j, P.p k j * q j

open Classical in
/-- Total revenue of a history: the sum over the selling horizon. -/
noncomputable def revenue (P : Problem d n K) {m : ℕ} (h : History n K m) : ℝ :=
  ∑ t, if Sells P h t then periodRevenue P (h t).1 (h t).2 else 0

open Classical in
/-- The number of switches of a history (p.9): `z_t ≠ z_{t+1}` for a selling period `t` whose
successor posts a price vector.

**Formalization Note.** Passing to `none` is a stop, not a switch. A switch into the period in
which an inventory is exceeded counts, because the price is posted before demand is seen. -/
noncomputable def switches (P : Problem d n K) {m : ℕ} (h : History n K m) : ℕ :=
  (Finset.univ.filter fun t : Fin m =>
    ∃ ht : t.val + 1 < m, Sells P h t ∧ (h t).1 ≠ (h ⟨t.val + 1, ht⟩).1 ∧
      (h ⟨t.val + 1, ht⟩).1 ≠ none).card

/-- The expected revenue `Rev_Q(ϕ)` (p.13).

**Formalization Note.** A Bochner integral. Revenue is measurable and bounded by `n p_max T` almost
surely, because demands lie in `[0,1]`, so the integral is not a junk value. -/
noncomputable def Rev (P : Problem d n K) (Q : DemandLaw n K) (φ : Policy n K) : ℝ :=
  ∫ h, revenue P h ∂(historyLaw Q φ P.T)

/-- `π ∈ Π_Q[s]`: at most `s` switches almost surely under the true distributions `Q` (p.13).

**Formalization Note.** Clairvoyant policies are all history-dependent policies with this property
under this `Q`, a class containing the policies the page writes down. -/
def IsSwitchLimited (P : Problem d n K) (Q : DemandLaw n K) (s : ℕ) (φ : Policy n K) : Prop :=
  ∀ᵐ h ∂(historyLaw Q φ P.T), switches P h ≤ s

/-- `Φ[s]`: the learning policies with at most `s` switches almost surely under every `Q` (p.13). -/
def LearningClass (P : Problem d n K) (s : ℕ) : Set (Policy n K) :=
  {φ | ∀ Q, IsSwitchLimited P Q s φ}

/-- `Rev_Q(π*_Q[s])`, the optimal clairvoyant revenue with switching budget `s` (p.13).

**Formalization Note.** `arg sup` is written as a supremum. The index type is nonempty, since it
contains the policy that always stops, and `Rev` is bounded by `n p_max T`, so it is a true
supremum. -/
noncomputable def optRev (P : Problem d n K) (Q : DemandLaw n K) (s : ℕ) : ℝ :=
  ⨆ π : {π : Policy n K // IsSwitchLimited P Q s π}, Rev P Q π.1

/-- `Rev_Q(π*_Q)`, the optimal clairvoyant revenue with an infinite switching budget (p.13). -/
noncomputable def optRevInf (P : Problem d n K) (Q : DemandLaw n K) : ℝ :=
  ⨆ π : Policy n K, Rev P Q π

/-- The `s`-switch regret `R^ϕ_s(T) = sup_Q (Rev_Q(π*_Q[s]) - Rev_Q(ϕ))` (p.13).

**Formalization Note.** The supremum is over nonempty and bounded data. -/
noncomputable def switchRegret (P : Problem d n K) (s : ℕ) (φ : Policy n K) : ℝ :=
  ⨆ Q : DemandLaw n K, (optRev P Q s - Rev P Q φ)

/-- The overall regret `R^ϕ(T) = sup_Q (Rev_Q(π*_Q) - Rev_Q(ϕ))` (p.14). -/
noncomputable def regret (P : Problem d n K) (φ : Policy n K) : ℝ :=
  ⨆ Q : DemandLaw n K, (optRevInf P Q - Rev P Q φ)

/-- The minimax `s`-switch regret, `inf_{ϕ ∈ Φ[s]} R^ϕ_s(T)`: the "optimal regret" of §4.3, p.21.

**Formalization Note.** `Φ[s]` is nonempty (the policy that always stops) and `R^ϕ_s ≥ 0` for
`ϕ ∈ Φ[s]`, so this is a true infimum. -/
noncomputable def minimaxSwitchRegret (P : Problem d n K) (s : ℕ) : ℝ :=
  ⨅ φ : {φ : Policy n K // φ ∈ LearningClass P s}, switchRegret P s φ.1

/-- The minimax overall regret over `s`-switch policies, `inf_{ϕ ∈ Φ[s]} R^ϕ(T)`. -/
noncomputable def minimaxRegret (P : Problem d n K) (s : ℕ) : ℝ :=
  ⨅ φ : {φ : Policy n K // φ ∈ LearningClass P s}, regret P φ.1

end BlindNRMLS


