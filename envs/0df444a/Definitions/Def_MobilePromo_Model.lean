-- Prove2me | Definitions.Def_MobilePromo_Model
-- name    : MobilePromo_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:09.915806+00:00
-- url     : https://prove2.me/theorems/344d9006-c51d-4cc6-ba0a-dae122c83e55
-- title:
--   The model: locations, arrival probabilities, bid interval, penalty and win curves
-- statement:
--   A mobile-promotion platform buys ad impressions by bidding. Impressions arrive from a finite set of locations $\mathcal L=\{1,\dots,L\}$: in each period, at most one impression arrives, and it comes from location $l$ with probability $q_l>0$, where $\sum_{l}q_l\le 1$. A bid lies in the interval $B=[b^{\min},b^{\max}]$ with $0<b^{\min}<b^{\max}$, and each unmet impression costs the platform a penalty $e>b^{\min}$, the same for all campaigns.
--
--   At location $l$, a bid $b_l\in B$ wins an arriving impression with probability $p_l(\gamma_l,b_l)$, the **win curve**, where $\gamma_l\in\Gamma_l\subset\mathbb R^{n_l}$ is a parameter vector and $\Gamma_l$ is open. The true parameter lies in a nonempty compact convex set $\Gamma_l^{(0)}\subset\Gamma_l$. We write $\gamma=(\gamma_1,\dots,\gamma_L)$, with
--
--   $$
--   \Gamma^{(0)}=\Gamma_1^{(0)}\times\dots\times\Gamma_L^{(0)},\qquad \|\gamma\|^2=\sum_{l}\|\gamma_l\|^2 .
--   $$
--
--   These are the data that every result of the mission fixes first.
--
--   **Formalization Note** Locations are `Fin L`. The parameter vector lives in the $L^2$ product `PiLp 2`, so $\|\gamma\|$ is the Euclidean norm of the concatenated vector, the norm of Lemma 1. The conditions $L\ge 1$, $q_l>0$, $\sum_l q_l\le 1$ and $\Gamma_l^{(0)}\ne\emptyset$ are implicit in the paper.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, §2, pp.7–8; Remark 2, p.11; p.11 (common penalty)

import Mathlib

set_option autoImplicit false

namespace MobilePromo

/-- The parameter space `ℝⁿ` of one win curve, with its Euclidean norm. -/
abbrev Param (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The data of the mobile-promotion model that is fixed before any season: the locations with their
arrival probabilities, the bid interval, the common penalty and the win curves (Feng, Dawande,
Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms,
SSRN 3523491, §2, pp.7–8; e common to all campaigns, pp.10–11; e > bmin, Remark 2, p.11).

**Formalization Note** Locations are `Fin L`, so location `l` of the paper is `l - 1` here. The fields
`L_pos`, `q_pos`, `q_sum_le` and `Γ₀_nonempty` are the paper's implicit hypotheses: `q_pos` is forced
because `K̂` divides by `q_l` (p.19), `q_sum_le` because at most one impression arrives per period
(p.7), and `Γ₀_nonempty` because the true parameter lies in `Γ⁽⁰⁾` (p.8). The win curve is a total
function; only its values on `Γ_l × B` matter. -/
structure Model where
  /-- The number of locations. -/
  L : ℕ
  L_pos : 0 < L
  /-- `q l` is the probability that an impression arrives from location `l` in a period. -/
  q : Fin L → ℝ
  q_pos : ∀ l, 0 < q l
  q_sum_le : ∑ l, q l ≤ 1
  /-- `n l` is the number of parameters of the win curve at location `l`. -/
  n : Fin L → ℕ
  /-- The lower end of the bid interval. -/
  bmin : ℝ
  /-- The upper end of the bid interval. -/
  bmax : ℝ
  /-- The unit penalty for an unmet impression, the same for all campaigns. -/
  e : ℝ
  bmin_pos : 0 < bmin
  bmin_lt_bmax : bmin < bmax
  bmin_lt_e : bmin < e
  /-- The win curve: `p l γ b` is the probability that bid `b` wins an impression from `l`. -/
  p : (l : Fin L) → Param (n l) → ℝ → ℝ
  /-- The open parameter set `Γ_l`. -/
  Γ : (l : Fin L) → Set (Param (n l))
  /-- The compact convex parameter set `Γ_l⁽⁰⁾`, which contains the true parameter. -/
  Γ₀ : (l : Fin L) → Set (Param (n l))
  isOpen_Γ : ∀ l, IsOpen (Γ l)
  Γ₀_subset : ∀ l, Γ₀ l ⊆ Γ l
  isCompact_Γ₀ : ∀ l, IsCompact (Γ₀ l)
  convex_Γ₀ : ∀ l, Convex ℝ (Γ₀ l)
  Γ₀_nonempty : ∀ l, (Γ₀ l).Nonempty

/-- The bid interval `B = [bmin, bmax]` (SSRN 3523491, p.8). -/
abbrev Model.B (M : Model) : Set ℝ := Set.Icc M.bmin M.bmax

/-- The vector `γ = (γ₁, …, γ_L)` of all parameters (SSRN 3523491, p.8).

**Formalization Note** The `L²` product, so that `‖γ‖² = ∑ l, ‖γ l‖²`: this is the Euclidean norm of the
concatenated vector, the norm of Lemma 1 (p.14). -/
abbrev Model.ParamVec (M : Model) := PiLp 2 (fun l : Fin M.L => Param (M.n l))

/-- The set `Γ⁽⁰⁾ = Γ₁⁽⁰⁾ × ⋯ × Γ_L⁽⁰⁾` (SSRN 3523491, p.8). -/
def Model.Gamma0 (M : Model) : Set M.ParamVec := {γ | ∀ l, γ l ∈ M.Γ₀ l}

end MobilePromo


