-- Prove2me | Definitions.Def_ReserveLP_ProLPR_Model
-- name    : ReserveLP_ProLPR_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:45.536709+00:00
-- url     : https://prove2.me/theorems/7005ad43-551e-4ac1-bc4d-4c1ab2079fe9
-- title:
--   §2, §4, §5, pp. 5–11 — eager second-price auctions with personalized reserves, valid profiles, Profile-LP, Pro-LPR rounding, Problem (10)
-- statement:
--   This file fixes the model of Derakhshan, Golrezaei and Paes Leme.
--
--   **Data-set (§2, p. 5; §4, p. 7).** There is a finite set $\mathsf A$ of auctions and a finite set $\mathsf B$ of buyers. Buyer $b$ bids $\beta_{a,b}\ge 0$ in auction $a$. Two distinct auxiliary buyers $b_0\neq b_{00}$ bid zero in every auction: $\beta_{a,b_0}=\beta_{a,b_{00}}=0$. In particular $|\mathsf B|\ge 2$.
--
--   **Eager second-price revenue (p. 5).** Given personalized reserves $r=(r_b)_{b\in\mathsf B}$, the cleared set of auction $a$ is $S_a=\{b:\beta_{a,b}\ge r_b\}$. If $S_a=\emptyset$, then $\mathrm{Rev}_a(r)=0$. Otherwise a highest bidder $b^\star_a$ of $S_a$ wins and pays
--
--   $$\mathrm{Rev}_a(r)=\max\Big(r_{b^\star_a},\ \max_{b\in S_a,\ b\neq b^\star_a}\beta_{a,b}\Big),$$
--
--   where an empty inner maximum counts as $0$. The value is the same whichever highest bidder wins. The total revenue is $\mathrm{Rev}(r)=\sum_{a\in\mathsf A}\mathrm{Rev}_a(r)$, and $\mathsf{ESP}^\star$ is its maximum over reserve vectors. The **second highest bid** $\beta^{(2)}_a$ is the largest value of $\min(\beta_{a,b},\beta_{a,b'})$ over pairs $b\neq b'$.
--
--   **Reserves and valid profiles (p. 5; Definition 4.1, p. 7).** The reserve set is $\mathsf R=\{0,\infty\}\cup\{\beta_{a,b}\}$. A valid profile of auction $a$ is a tuple $p=(b_1,b_2,r_1,r_2)\in\mathsf B\times\mathsf B\times\mathsf R\times\mathsf R$ with $b_1\neq b_2$, $\beta_{a,b_1}\ge\beta_{a,b_2}$, $\beta_{a,b_1}\ge r_1$ and $\beta_{a,b_2}\ge r_2$. Its revenue is $\mathrm{Rev}_a(p)=\max(\beta_{a,b_2},r_1)$. The set $\mathcal Q_{b,r,a}$ of equation (1) contains the valid profiles of auction $a$ that assign reserve $r$ to buyer $b$, either as $b_1$ or as $b_2$.
--
--   **Profile-LP (p. 8).** The variables are $s_{a,p}$ for $p\in\mathcal P_a$ and $q_{b,r}$ for $r\in\mathsf R$. The LP is
--
--   $$\max\ \sum_{a}\sum_{p\in\mathcal P_a}s_{a,p}\,\mathrm{Rev}_a(p)\quad\text{s.t.}\quad \sum_{p\in\mathcal P_a}s_{a,p}\le1,\quad \sum_{p\in\mathcal Q_{b,r,a}}s_{a,p}\le q_{b,r},\quad \sum_{r\in\mathsf R}q_{b,r}=1,\quad s_{a,p}\ge0,\quad q_{b,r}\ge 0.$$
--
--   An optimal solution is a feasible pair whose objective is at least that of every feasible pair.
--
--   **Pro-LPR (p. 8).** Given an optimal $(s^\star,q^\star)$, draw a reserve $r^{\mathcal R}_b\in\mathsf R$ for every buyer independently with $\Pr[r^{\mathcal R}_b=r]=q^\star_{b,r}$. Output whichever of $r^{\mathcal R}$ and the zero vector $z$ earns more. The file defines $\Pr[\mathrm{Rev}_a(r^{\mathcal R})\ge t]$, the profile mass $\sum_{p\in\mathcal P_a,\ \mathrm{Rev}_a(p)\ge t}s_{a,p}$, and the expected revenue of the output,
--
--   $$\mathbb E[\mathrm{Rev}(r^{\rm out})]=\mathbb E\big[\max(\mathrm{Rev}(r^{\mathcal R}),\mathrm{Rev}(z))\big].$$
--
--   **Problem (10) and its constants (pp. 11, 16).** For $n$ variables and $\theta\in\mathbb R$,
--
--   $$\mathsf{OPT}(\theta)=\sup_{x\ge0,\ \frac12\sum_i x_i=\theta,\ x_i\le\theta}\ e^{\theta-1}\Big[\prod_{i}(1-x_i)+\sum_i x_i\prod_{j\neq i}(1-x_j)\Big],$$
--
--   and $c=\max_{\theta\in[0,1]}\mathsf{OPT}(\theta)$. The file also defines $\mathsf{OPT}^1(\theta,k)=e^{\theta-1}(1-\tfrac{2\theta}{k})^{k-1}(1-\tfrac{2\theta}{k}+2\theta)$, $\mathsf{OPT}^2(\theta,k)=e^{\theta-1}\big[(1-\tfrac\theta k)^k+\theta(1-\theta)(1-\tfrac\theta k)^{k-1}\big]$ and $c^\star=2(\sqrt2-1)e^{\sqrt2-2}\approx0.4612$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.**
--   1. All quantities are real numbers.
--   2. The reserve $\infty$ is encoded by the sentinel $1+\sum_{a,b}\beta_{a,b}$. It lies strictly above every bid, so a buyer given this reserve never clears, which is all that $\infty$ does in the paper.
--   3. Valid profiles additionally require $b_1\neq b_2$. Definition 4.1 omits this, but the paper reads $b_1, b_2$ as the highest and second highest cleared buyers (Definition 4.2). Without it, the main theorem fails on one auction with bids $(1,0,0)$.
--   4. The paper states $q_{b,r}\ge0$ on p. 7 and omits it from the p. 8 display; it is included here.
--   5. Probabilities and expectations are finite sums over $\mathsf R^{\mathsf B}$ with product weights $\prod_b q_{b,\rho_b}$.
--   6. $\mathsf{OPT}$ and $c$ are real suprema. For $n\ge2$ and $\theta\in[0,1]$ the feasible set of Problem (10) is nonempty (take $x=(\theta,\theta,0,\dots)$) and the objective lies in $[0,1]$, so these suprema are not junk values.
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, pp. 5–11, 16, §2 (ESP-OPT), §4 Definition 4.1, eq. (1), Profile-LP, Pro-LPR (p. 8), Problem (10) (p. 11), Corollary 5.6 (p. 16)

import Mathlib

namespace ReserveLP.ProLPR

open Finset

/-- A data-set of bids (§2, p. 5) with the two auxiliary zero-bid buyers `b0`, `b00` of §4, p. 7. -/
structure DataSet (A B : Type) where
  bid : A → B → ℝ
  bid_nonneg : ∀ a b, 0 ≤ bid a b
  b0 : B
  b00 : B
  b0_ne_b00 : b0 ≠ b00
  bid_b0 : ∀ a, bid a b0 = 0
  bid_b00 : ∀ a, bid a b00 = 0

noncomputable section

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]

/-- `S_a(r)`: the buyers who clear their reserve in auction `a` (p. 5). -/
def cleared (D : DataSet A B) (a : A) (r : B → ℝ) : Finset B :=
  univ.filter (fun b => r b ≤ D.bid a b)

/-- The highest bidders among the cleared buyers (the possible winners `b⋆_a`). -/
def topBidders (D : DataSet A B) (a : A) (r : B → ℝ) : Finset B :=
  (cleared D a r).filter (fun w => ∀ b ∈ cleared D a r, D.bid a b ≤ D.bid a w)

/-- The highest bid among the cleared buyers other than `w`; `0` if there is none. -/
def otherMax (D : DataSet A B) (a : A) (r : B → ℝ) (w : B) : ℝ :=
  (insert 0 (((cleared D a r).erase w).image (D.bid a))).max' (insert_nonempty _ _)

/-- Eager second-price revenue `Rev_a(r)` of auction `a` (p. 5): `0` if nobody clears, otherwise
`max(r_{b⋆}, max_{b ∈ S_a, b ≠ b⋆} β_{a,b})`. The value does not depend on how ties among top
bidders are broken; it is written as the maximum over all top bidders. -/
def revA (D : DataSet A B) (a : A) (r : B → ℝ) : ℝ :=
  if h : (topBidders D a r).Nonempty then
    (topBidders D a r).sup' h (fun w => max (r w) (otherMax D a r w))
  else 0

/-- `Rev(r) = Σ_a Rev_a(r)` (ESP-OPT, p. 5). -/
def rev (D : DataSet A B) (r : B → ℝ) : ℝ := ∑ a, revA D a r

/-- The second highest bid `β^{(2)}_a`: the largest `min(β_{a,b}, β_{a,b'})` over `b ≠ b'`. -/
def secondBid (D : DataSet A B) (a : A) : ℝ :=
  (univ.offDiag : Finset (B × B)).sup' ⟨(D.b0, D.b00), by simp [D.b0_ne_b00]⟩
    (fun bb => min (D.bid a bb.1) (D.bid a bb.2))

/-- The sentinel standing for the reserve `∞`: strictly above every bid. -/
def topReserve (D : DataSet A B) : ℝ := 1 + ∑ a, ∑ b, D.bid a b

/-- The reserve set `R = {0, ∞} ∪ {β_{a,b}}` (p. 5), with `∞` encoded by `topReserve D`. -/
def reserves (D : DataSet A B) : Finset ℝ :=
  insert 0 (insert (topReserve D) (univ.image (fun ab : A × B => D.bid ab.1 ab.2)))

/-- A profile `(b₁, b₂, r₁, r₂)`. -/
abbrev Profile (B : Type) := B × B × ℝ × ℝ

/-- Valid profiles `P_a` (Definition 4.1, p. 7), with the added requirement `b₁ ≠ b₂`. -/
def validProfiles (D : DataSet A B) (a : A) : Finset (Profile B) :=
  ((univ : Finset B) ×ˢ (univ : Finset B) ×ˢ reserves D ×ˢ reserves D).filter (fun p =>
    p.1 ≠ p.2.1 ∧ D.bid a p.2.1 ≤ D.bid a p.1 ∧ p.2.2.1 ≤ D.bid a p.1 ∧
      p.2.2.2 ≤ D.bid a p.2.1)

/-- `Rev_a(p) = max(β_{a,b₂}, r₁)` (Definition 4.1, p. 7). -/
def revProfile (D : DataSet A B) (a : A) (p : Profile B) : ℝ := max (D.bid a p.2.1) p.2.2.1

/-- `Q_{b,r,a}` (equation (1), p. 7): valid profiles assigning reserve `r` to buyer `b`. -/
def Qset (D : DataSet A B) (a : A) (b : B) (r : ℝ) : Finset (Profile B) :=
  (validProfiles D a).filter (fun p => (p.2.1 = b ∧ p.2.2.2 = r) ∨ (p.1 = b ∧ p.2.2.1 = r))

/-- Feasibility for Profile-LP (p. 8), with `q_{b,r} ≥ 0` from p. 7. -/
def LPFeasible (D : DataSet A B) (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) : Prop :=
  (∀ a, ∀ p ∈ validProfiles D a, 0 ≤ s a p) ∧
  (∀ a, ∑ p ∈ validProfiles D a, s a p ≤ 1) ∧
  (∀ a b, ∀ r ∈ reserves D, ∑ p ∈ Qset D a b r, s a p ≤ q b r) ∧
  (∀ b, ∑ r ∈ reserves D, q b r = 1) ∧
  (∀ b, ∀ r ∈ reserves D, 0 ≤ q b r)

/-- The Profile-LP objective `Σ_a Σ_{p ∈ P_a} s_{a,p} Rev_a(p)`. -/
def LPObj (D : DataSet A B) (s : A → Profile B → ℝ) : ℝ :=
  ∑ a, ∑ p ∈ validProfiles D a, s a p * revProfile D a p

/-- `(s, q)` is an optimal solution of Profile-LP. -/
def LPOptimal (D : DataSet A B) (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) : Prop :=
  LPFeasible D s q ∧ ∀ s' q', LPFeasible D s' q' → LPObj D s' ≤ LPObj D s

/-- The reserve vectors the rounding can produce: `R^B`. -/
def roundings (D : DataSet A B) : Finset (B → ℝ) := Fintype.piFinset (fun _ : B => reserves D)

/-- Probability of the reserve vector `ρ` under independent rounding with marginals `q`. -/
def roundProb (q : B → ℝ → ℝ) (ρ : B → ℝ) : ℝ := ∏ b, q b (ρ b)

/-- `Pr[Rev_a(r^R) ≥ t]` under the Pro-LPR rounding with marginals `q`. -/
def probRevGe (D : DataSet A B) (q : B → ℝ → ℝ) (a : A) (t : ℝ) : ℝ :=
  ∑ ρ ∈ roundings D, roundProb q ρ * (if t ≤ revA D a ρ then 1 else 0)

/-- `Σ_{p ∈ P_a, Rev_a(p) ≥ t} s_{a,p}`. -/
def profileMassGe (D : DataSet A B) (s : A → Profile B → ℝ) (a : A) (t : ℝ) : ℝ :=
  ∑ p ∈ (validProfiles D a).filter (fun p => t ≤ revProfile D a p), s a p

/-- `E[Rev(r^out)] = E[max(Rev(r^R), Rev(z))]`, the expected revenue of the Pro-LPR output. -/
def expRevOut (D : DataSet A B) (q : B → ℝ → ℝ) : ℝ :=
  ∑ ρ ∈ roundings D, roundProb q ρ * max (rev D ρ) (rev D (fun _ => 0))

/-- The objective of Problem (10), p. 11. -/
def Fobj {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) : ℝ :=
  Real.exp (θ - 1) * (∏ i, (1 - x i) + ∑ i, x i * ∏ j ∈ univ.erase i, (1 - x j))

/-- The constraints of Problem (10): `x ≥ 0`, `(1/2) Σ x_i = θ`, `x_i ≤ θ`. -/
def OPTFeasible (n : ℕ) (θ : ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (1 / 2 : ℝ) * ∑ i, x i = θ ∧ ∀ i, x i ≤ θ

/-- `OPT(θ)`, the optimal value of Problem (10) with `n` variables. -/
def OPT (n : ℕ) (θ : ℝ) : ℝ := sSup {v | ∃ x, OPTFeasible n θ x ∧ v = Fobj x θ}

/-- `c = max_{θ ∈ [0,1]} OPT(θ)` (Lemma 5.3, p. 11). -/
def cOPT (n : ℕ) : ℝ := sSup (OPT n '' Set.Icc 0 1)

/-- `OPT¹(θ, k)` (Corollary 5.6, p. 16). -/
def OPT1 (θ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (θ - 1) * (1 - 2 * θ / k) ^ (k - 1) * (1 - 2 * θ / k + 2 * θ)

/-- `OPT²(θ, k)` (Corollary 5.6, p. 16). -/
def OPT2 (θ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (θ - 1) * ((1 - θ / k) ^ k + θ * (1 - θ) * (1 - θ / k) ^ (k - 1))

/-- `c⋆ = 2(√2 − 1)e^{√2−2} ≈ 0.4612`. -/
def cStar : ℝ := 2 * (Real.sqrt 2 - 1) * Real.exp (Real.sqrt 2 - 2)

end

end ReserveLP.ProLPR


