-- Prove2me | Definitions.Def_SubstitutePricing_Dynamic_Model
-- name    : SubstitutePricing_Dynamic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:04.146989+00:00
-- url     : https://prove2.me/theorems/5ac4b95f-cfce-449a-9095-77ab91ed76b1
-- title:
--   The substitute-product MNL dynamic pricing model of §2
-- statement:
--   Consider $n$ product variates with qualities $a_i$, outside-option utility $u_0$, logit scale $\mu>0$, and one-customer arrival probability $0<\lambda\leq1$ per period. Inventory $x_i$ is a nonnegative integer; $S(x)=\{i:x_i>0\}$. In-stock variates may receive finite nonnegative prices $r_i$. An out-of-stock variate is removed from the choice set, which represents the paper's infinite null price.
--
--   The purchase probabilities are
--
--   $$
--   P_i(x,r)=\frac{\exp((a_i-r_i)/\mu)}{\sum_{j\in S(x)}\exp((a_j-r_j)/\mu)+\exp(u_0/\mu)},\qquad P_0(x,r)=\frac{\exp(u_0/\mu)}{\sum_{j\in S(x)}\exp((a_j-r_j)/\mu)+\exp(u_0/\mu)}.
--   $$
--
--   The model defines the one-period revenue and continuation objective, the Bellman value $\pi_t(x)$ with $\pi_0(x)=0$, the marginal inventory value $\Delta^i\pi_t(x)=\pi_t(x)-\pi_t(x-e^i)$, the price objective $\xi$, and the margin equation and its candidate prices. The probability-domain functions express equations (8), (19), and (20).
--
--   **Formalization Note** The no-sale continuation term in (3) is counted once, as required by (5) and (22), despite the printed bracket placement. Off-stock purchase probabilities and candidate prices are zero. Inventory subtraction is used for in-stock coordinates, where it is exact.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), pp. 321–323, §2, (1)–(5), (7)–(10); p. 335, (8), (19)–(20)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

noncomputable section

namespace SubstitutePricing.Dynamic

/-- Data of the finite-horizon substitute-product pricing model in §2. -/
structure Model where
  n : ℕ
  a : Fin n → ℝ
  u0 : ℝ
  μ : ℝ
  lam : ℝ

/-- The scale and arrival probability assumptions in §2. -/
structure Model.Assumptions (M : Model) : Prop where
  mu_pos : 0 < M.μ
  lam_pos : 0 < M.lam
  lam_le_one : M.lam ≤ 1

/-- Variates with positive remaining inventory. -/
def Model.S (M : Model) (x : Fin M.n → ℕ) : Finset (Fin M.n) :=
  Finset.univ.filter (fun i => 0 < x i)

/-- Remove one unit of an in-stock variate. -/
def Model.sell (M : Model) (x : Fin M.n → ℕ) (i : Fin M.n) : Fin M.n → ℕ :=
  Function.update x i (x i - 1)

/-- The denominator of the MNL probabilities (1)–(2). -/
def Model.den (M : Model) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : ℝ :=
  (∑ j ∈ M.S x, Real.exp ((M.a j - r j) / M.μ)) + Real.exp (M.u0 / M.μ)

/-- The purchase probability (1), set to zero outside the in-stock set. -/
def Model.P (M : Model) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) (i : Fin M.n) : ℝ :=
  if i ∈ M.S x then Real.exp ((M.a i - r i) / M.μ) / M.den x r else 0

/-- The no-purchase probability (2). -/
def Model.P0 (M : Model) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : ℝ :=
  Real.exp (M.u0 / M.μ) / M.den x r

/-- The paper's allowable price vectors, with finite nonnegative coordinates. -/
def Model.feasible (M : Model) : Set (Fin M.n → ℝ) :=
  {r | ∀ i, 0 ≤ r i}

/-- One-period objective of (3), with the no-sale term counted once. -/
def Model.obj (M : Model) (V : (Fin M.n → ℕ) → ℝ)
    (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : ℝ :=
  M.lam * (∑ i ∈ M.S x, r i * M.P x r i) +
  M.lam * (∑ i ∈ M.S x, M.P x r i * V (M.sell x i)) +
  (M.lam * M.P0 x r + 1 - M.lam) * V x

/-- Bellman revenue (3)–(4), with `t` periods remaining. -/
def Model.pi (M : Model) : ℕ → (Fin M.n → ℕ) → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun x => sSup ((M.obj (M.pi t) x) '' M.feasible)

/-- Marginal value Δⁱπₜ(x), used only for an in-stock `i`. -/
def Model.delta (M : Model) (t : ℕ) (i : Fin M.n) (x : Fin M.n → ℕ) : ℝ :=
  M.pi t x - M.pi t (M.sell x i)

/-- The price objective ξ in (5), for an arbitrary continuation value. -/
def Model.xi (M : Model) (V : (Fin M.n → ℕ) → ℝ)
    (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : ℝ :=
  M.lam * ChoiceCDLP.MNL.mnlObjective
    (fun i => Real.exp ((M.a i - r i) / M.μ))
    (fun i => r i - (V x - V (M.sell x i)))
    (Real.exp (M.u0 / M.μ)) (M.S x)

/-- The right side of the margin equation (10). -/
def Model.sigma (M : Model) (t : ℕ) (x : Fin M.n → ℕ) : ℝ :=
  ∑ i ∈ M.S x, Real.exp ((M.a i - M.delta (t - 1) i x) / M.μ)

/-- The left side of the margin equation (10). -/
def Model.marginLHS (M : Model) (m : ℝ) : ℝ :=
  (m / M.μ - 1) * Real.exp ((m + M.u0) / M.μ)

/-- Candidate prices (9); off-stock coordinates are irrelevant and set to zero. -/
def Model.rstar (M : Model) (t : ℕ) (x : Fin M.n → ℕ) (m : ℝ) : Fin M.n → ℝ :=
  fun i => if i ∈ M.S x then M.delta (t - 1) i x + m else 0

/-- The expanded positive probability domain of Step 3. -/
def Model.positiveProbDomain (M : Model) (S : Finset (Fin M.n)) :
    Set ((Fin M.n → ℝ) × ℝ) :=
  {q | (∀ i ∈ S, q.1 i ∈ Set.Ioo (0 : ℝ) 1) ∧ q.2 ∈ Set.Ioo (0 : ℝ) 1}

/-- The MNL probability simplex for the stocked variates. -/
def Model.choiceDomain (M : Model) (S : Finset (Fin M.n)) :
    Set ((Fin M.n → ℝ) × ℝ) :=
  {q | (∀ i ∈ S, 0 < q.1 i) ∧ 0 < q.2 ∧ (∑ i ∈ S, q.1 i) + q.2 = 1}

/-- The price objective (8), rewritten in choice probabilities. -/
def Model.probObjective (M : Model) (S : Finset (Fin M.n)) (δ : Fin M.n → ℝ)
    (q : (Fin M.n → ℝ) × ℝ) : ℝ :=
  ∑ i ∈ S, M.lam * q.1 i *
    (M.a i - M.u0 - M.μ * Real.log (q.1 i) + M.μ * Real.log q.2 - δ i)

/-- The Step 4 candidate purchase probability (20). -/
def Model.pstar (M : Model) (δ : Fin M.n → ℝ) (m : ℝ) (i : Fin M.n) : ℝ :=
  (M.μ / m) * Real.exp ((M.a i - δ i - M.u0 - m) / M.μ)

end SubstitutePricing.Dynamic


