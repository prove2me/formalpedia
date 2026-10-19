-- Prove2me | Definitions.Def_CoProdBundle_Equil_Setting
-- name    : CoProdBundle_Equil_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:59.08131+00:00
-- url     : https://prove2.me/theorems/93b7dd23-ae66-4515-99d3-97a198e0e125
-- title:
--   §3.2–§4.2, pp. 10–17 — demand √(AQ^θ − bP), retailer profit (3a), sharable surplus S(Q), payoffs γ(Q_i/Q)S(Q) − c_iQ_i, Nash equilibrium, K (2a), Q* (2c), Q*_i (2b), P* (2d)
-- statement:
--   This file sets up the co-produced bundle economy of Bhargava's model and the closed forms of its equilibrium.
--
--   **Parameters.** Fix real numbers $A, b, w, \theta, \gamma$. Here $b>0$ is the price sensitivity of demand, $w$ is the coefficient of the retailer's distribution cost $w^R(Q) = wQ^\theta$ (the paper writes this coefficient as $c$), $\theta$ is the bundle-size elasticity, and $\gamma$ is the producers' share of the sharable surplus. There are $I$ producers; producer $i$ has unit production cost $c_i$.
--
--   **Retailer.** For a bundle of $Q \ge 0$ value units and a price $P \in \mathbb R$, demand is
--   $$D(P,Q) = \sqrt{AQ^\theta - bP},$$
--   which is $0$ when $AQ^\theta - bP < 0$ (no buyer above the choke price). The surplus at price $P$ is $(P - wQ^\theta)\,D(P,Q)$ and the retailer's profit (3a) is
--   $$\Pi_R(P,Q) = (1-\gamma)(P - wQ^\theta)\sqrt{AQ^\theta - bP}.$$
--   A price $P$ is *retailer-optimal* at $Q$ if it maximizes $\Pi_R(\cdot, Q)$ over all real prices. The **sharable surplus** is the largest surplus over all prices,
--   $$S(Q) = \sup_{P\in\mathbb R}\,(P - wQ^\theta)\,D(P,Q).$$
--
--   **Producers' game.** Producer $i$ chooses an output $Q_i \ge 0$; the aggregate is $Q = \sum_j Q_j$. Its profit is
--   $$\pi_i = \gamma\,\frac{Q_i}{Q}\,S(Q) - c_iQ_i .$$
--   A profile $(Q_1,\dots,Q_I)$ is a (pure) **Nash equilibrium** if every $Q_i \ge 0$ and no producer can raise its profit by switching to another output $x \ge 0$ while the others keep theirs.
--
--   **Closed forms of Lemma 1.** Write $\alpha = 1 - 3\theta/2$ and $c_1 + \dots + c_k$ for the sum of the first $k$ costs.
--   1. $K$ is the largest $k \in \{1,\dots,I\}$ with $c_k \le (c_1+\dots+c_k)/(k - \alpha)$ (condition (2a)), and $0$ if there is none.
--   2. For $1 \le k \le I$, with the average $\bar c_k = (c_1+\dots+c_k)/k$, the closed form (5c) is $\bigl[\tfrac{\gamma}{b\bar c_k}\bigl(2 - \tfrac{2-3\theta}{k}\bigr)\bigr]^{2/(2-3\theta)}\bigl(\tfrac{A-bw}{3}\bigr)^{3/(2-3\theta)}$.
--   3. $Q^* = \bigl[\tfrac{2\gamma}{b}\,\tfrac{K-\alpha}{c_1+\dots+c_K}\bigr]^{2/(2-3\theta)}\bigl(\tfrac{A-bw}{3}\bigr)^{3/(2-3\theta)}$ (2c).
--   4. $Q^*_i = \bigl[1 - c_i\,\tfrac{K-\alpha}{c_1+\dots+c_K}\bigr]\tfrac{2Q^*}{2-3\theta}$ for $i \le K$ (2b), and $Q^*_i = 0$ for $i > K$.
--   5. $P^*(Q) = \tfrac{2A + bw}{3b}\,Q^\theta$ (2d).
--   6. The right side of the first-order condition (4c), $\bigl[2 - \tfrac{bc_iQ}{\gamma}\bigl(\tfrac{1}{Q^\theta}\tfrac{3}{A-bw}\bigr)^{3/2}\bigr]\tfrac{Q}{2-3\theta}$.
--
--   These objects are the model of §3 and the candidate solution of Lemma 1. The theorems of the mission state that the candidate is the equilibrium.
--
--   **Formalization Note** The paper's distribution-cost coefficient $c$ is named `w`, so that it is not confused with the producers' costs `c i`; every $A - bc$ of the paper is `A - b * w`. Producers are `Fin I`, so Lean's producer `i` is the paper's producer $i+1$, and `psum c k` sums the first $k$ costs. All powers are real powers (`Real.rpow`). `Real.sqrt` of a negative number is $0$, which is the zero demand above the choke price. $S$ is a supremum over prices, not the closed form (3e); that it equals (3e) is a theorem of the mission. At the all-zero profile the share $Q_i/Q$ is $0/0$, which Lean evaluates to $0$, so all profits are $0$ there; this profile is not an equilibrium, since a producer gains by a small positive output. The retailer's optimal price is folded into $S$, which is the subgame-perfect reading of the paper's backward solution. The Nash equilibrium is the published predicate `CachonCoord.Proportional.IsNash` (nonnegative real strategies, unilateral deviations to any $x \ge 0$) applied to the payoffs above. $K$ is `Nat.findGreatest` over $\{0,\dots,I\}$ with classical decidability.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), §3.2 p. 10, §3.3 p. 11, §3.4 p. 13, Lemma 1 (2a)–(2d) p. 14, (3a) p. 15, (4c) p. 16, (5c) p. 17

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Nash

namespace CoProdBundle.Equil

noncomputable section

/-- Bundle demand `D(P, Q) = √(A Q^θ − b P)` (Bhargava, §3.4, p. 13). `Real.sqrt` of a negative
number is `0`: no demand above the choke price. -/
def demand (A b θ P Q : ℝ) : ℝ := Real.sqrt (A * Q ^ θ - b * P)

/-- Sharable surplus at price `P` for a bundle of `Q` value units: `(P − w^R(Q)) D(P, Q)` with
distribution cost `w^R(Q) = w Q^θ` (the page's `c Q^θ`; §3.2, p. 10, §3.4, p. 13). -/
def surplus (A b w θ Q P : ℝ) : ℝ := (P - w * Q ^ θ) * demand A b θ P Q

/-- The retailer's profit (3a): `Π_R(P, Q) = (1 − γ)(P − w Q^θ) √(A Q^θ − b P)` (p. 15). -/
def retailerProfit (γ A b w θ Q P : ℝ) : ℝ := (1 - γ) * surplus A b w θ Q P

/-- `P` maximizes the retailer's profit (3a) at bundle size `Q`, over all real prices. -/
def IsRetailerOptimal (γ A b w θ Q P : ℝ) : Prop :=
  ∀ P' : ℝ, retailerProfit γ A b w θ Q P' ≤ retailerProfit γ A b w θ Q P

/-- The sharable industry surplus `S(Q)` at the retailer's optimal price: the supremum over all
real prices of the surplus `(P − w Q^θ) D(P, Q)` (§3.2, p. 10). -/
def S (A b w θ Q : ℝ) : ℝ := ⨆ P : ℝ, surplus A b w θ Q P

/-- Aggregate output `Q = Σ_i Q_i` of a profile of producer outputs. -/
def total {I : ℕ} (q : Fin I → ℝ) : ℝ := ∑ j, q j

/-- Producer `i`'s profit `π_i = γ (Q_i / Q) S(Q) − c_i Q_i`, with `Q` the aggregate output of the
profile (§3.3, p. 11). Lean's `x / 0 = 0` makes it `0` at the all-zero profile. -/
def payoff (γ A b w θ : ℝ) {I : ℕ} (c q : Fin I → ℝ) (i : Fin I) : ℝ :=
  γ * (q i / total q) * S A b w θ (total q) - c i * q i

/-- Pure Nash equilibrium of the producers' output game: outputs `Q_i ≥ 0`, and no producer gains
by a unilateral deviation to any output `x ≥ 0` (§4.2, pp. 15–16). The retailer's optimal price is
folded into `S`, so this is the subgame-perfect reading of the backward sequence of §4. -/
def IsNashEq (γ A b w θ : ℝ) {I : ℕ} (c q : Fin I → ℝ) : Prop :=
  CachonCoord.Proportional.IsNash (fun i q' => payoff γ A b w θ c q' i) q

/-- `α = 1 − 3θ/2`, the constant of (2a)–(2c). -/
def alpha (θ : ℝ) : ℝ := 1 - 3 * θ / 2

/-- `c_1 + … + c_k`: the sum of the costs of the first `k` producers (Lean indices `< k`). -/
def psum {I : ℕ} (c : Fin I → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin I => (j : ℕ) < k), c j

/-- The set condition of (2a) at the page's index `k` (Lean producer `k − 1`):
`c_k ≤ (c_1 + … + c_k) / (k − (1 − 3θ/2))`. -/
def Feasible {I : ℕ} (c : Fin I → ℝ) (θ : ℝ) (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ h : k - 1 < I, c ⟨k - 1, h⟩ ≤ psum c k / ((k : ℝ) - alpha θ)

open Classical in
/-- `K = max{i : c_i ≤ (c_1 + … + c_i)/(i − (1 − 3θ/2))}` of (2a), the largest `k ≤ I`
satisfying the condition (`0` if none does). -/
def Kstar {I : ℕ} (c : Fin I → ℝ) (θ : ℝ) : ℕ := Nat.findGreatest (Feasible c θ) I

/-- The right side of (5c) for the first `k` producers:
`[(γ/(b c̄_k))(2 − (2 − 3θ)/k)]^{2/(2−3θ)} ((A − b w)/3)^{3/(2−3θ)}`, with the average
`c̄_k = (c_1 + … + c_k)/k`. -/
def Q5c (γ A b w θ : ℝ) {I : ℕ} (c : Fin I → ℝ) (k : ℕ) : ℝ :=
  ((γ / (b * (psum c k / k))) * (2 - (2 - 3 * θ) / k)) ^ (2 / (2 - 3 * θ)) *
    ((A - b * w) / 3) ^ (3 / (2 - 3 * θ))

/-- `Q*` of (2c): `[(2γ/b)((K − (1 − 3θ/2))/(c_1 + … + c_K))]^{2/(2−3θ)} ((A − b w)/3)^{3/(2−3θ)}`. -/
def Qstar (γ A b w θ : ℝ) {I : ℕ} (c : Fin I → ℝ) : ℝ :=
  ((2 * γ / b) * (((Kstar c θ : ℝ) - alpha θ) / psum c (Kstar c θ))) ^ (2 / (2 - 3 * θ)) *
    ((A - b * w) / 3) ^ (3 / (2 - 3 * θ))

/-- The outputs of Lemma 1: (2b) for the first `K` producers,
`Q*_i = [1 − c_i (K − (1 − 3θ/2))/(c_1 + … + c_K)] · 2Q*/(2 − 3θ)`, and `0` for the others. -/
def qstar (γ A b w θ : ℝ) {I : ℕ} (c : Fin I → ℝ) (i : Fin I) : ℝ :=
  if (i : ℕ) < Kstar c θ then
    (1 - c i * (((Kstar c θ : ℝ) - alpha θ) / psum c (Kstar c θ))) *
      (2 * Qstar γ A b w θ c / (2 - 3 * θ))
  else 0

/-- The retailer's price (2d) = (3b): `P*(Q) = ((2A + b w)/(3b)) Q^θ`. -/
def Pstar (A b w θ Q : ℝ) : ℝ := (2 * A + b * w) / (3 * b) * Q ^ θ

/-- The right side of (4c) for a producer with unit cost `ci` at aggregate output `Q`:
`[2 − (b ci Q/γ)((1/Q^θ)(3/(A − b w)))^{3/2}] Q/(2 − 3θ)`. -/
def br4c (γ A b w θ ci Q : ℝ) : ℝ :=
  (2 - (b * ci * Q / γ) * ((1 / Q ^ θ) * (3 / (A - b * w))) ^ (3 / 2 : ℝ)) * (Q / (2 - 3 * θ))

end

end CoProdBundle.Equil


