-- Prove2me | Definitions.Def_HubSpokePricing_Lagrangian_Model
-- name    : HubSpokePricing_Lagrangian_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:49.564477+00:00
-- url     : https://prove2.me/theorems/6bea9245-b68a-49ff-b284-3314b8961cda
-- title:
--   §2–§4, pp. 6–21 — hub-and-spoke relocation pricing: Assumption 2.1, problem (1), relaxation (3), spoke problem (6), duals (9)/(11), Lagrangian policy, chains
-- statement:
--   **Network** (§2.2, pp. 8–9). One hub, location $0$, and $n$ spokes $i\in[n]$ share $m$ resources. In each period one request arrives: it is of type $(i,0)$ (relocate a resource from spoke $i$ to the hub) with probability $q_{i0}$ and of type $(0,i)$ (from the hub to spoke $i$) with probability $q_{0i}$, independently across periods. The provider chooses a demand level $d\in[0,1]$; the request is fulfilled with probability $d$ and yields expected revenue $r_{ij}(d)$. The **standing assumptions** are: $n\ge1$; $q_{i0},q_{0i}>0$ with $\sum_i(q_{i0}+q_{0i})=1$; $\bar r,\bar\omega>0$; and **Assumption 2.1** for every revenue function $r=r_{ij}$: $r$ is strictly concave on $[0,1]$, $r(0)=0$, $\max_{[0,1]}r\le\bar r$, $r$ is differentiable on $[0,1]$ with $\max_{[0,1]}|r'|\le\bar\omega$, and its maximum on $[0,1]$ is attained in $(0,1)$.
--
--   **States.** The spoke levels $x=(x_i)_{i\in[n]}$ lie in $\mathcal X=\{x\in\mathbb N^n:\sum_i x_i\le m\}$; the hub holds $x_0=m-\sum_i x_i$.
--
--   **Problem (1).** A non-anticipative policy chooses the demand level from the observed history (past request types and whether each was fulfilled) and the current request type. It is *feasible* from $x^0\in\mathcal X$ if every level lies in $[0,1]$ and is $0$ when the origin of the request holds no resource. With $J_T(\pi)$ the expected revenue of the first $T$ periods,
--   $$V^{\mathrm{OPT}}(x^0)=\sup_{\pi\text{ feasible from }x^0}\ \limsup_{T\to\infty}\frac1T\,J_T(\pi).$$
--
--   **Spoke problem (6)** (p. 12). For a dual variable $\lambda$ and spoke $i$, $h_i^\lambda$ is the maximum of
--   $$\sum_{x=0}^m p_i(x)\big[q_{i0}\,r_{i0}(d_i(x,i,0))+q_{0i}\,r_{0i}(d_i(x,0,i))\big]-\lambda\sum_{x=0}^m x\,p_i(x)$$
--   over $p_i(x)\ge0$ with $\sum_x p_i(x)=1$ and $d_i(x,i,0),d_i(x,0,i)\in[0,1]$ subject to the balance equations $p_i(x)\,q_{0i}\,d_i(x,0,i)=p_i(x+1)\,q_{i0}\,d_i(x+1,i,0)$ for $x\in[0:m-1]$ and $d_i(0,i,0)=0$, $d_i(m,0,i)=0$.
--
--   **Lagrangian relaxation (3)** (p. 11). The relaxation drops the hub's non-negativity: spoke levels range over $\bar{\mathcal X}=\{x\in\mathbb N^n:x_i\le m\ \forall i\}$, a request $(i,0)$ cannot be fulfilled at $x_i=0$ nor a request $(0,i)$ at $x_i=m$, and in every period the reward $\lambda\,(m-\sum_i x_{i,t})$ is added to the revenue. $\bar V^\lambda_{(3)}(x^0)$ is the supremum over feasible non-anticipative policies of the $\limsup$ of the average of revenue plus this reward from $x^0\in\bar{\mathcal X}$.
--
--   **Duals** (4), (9), (11). $\bar V^\lambda=m\lambda+\sum_i h_i^\lambda$, $\;V^{\mathrm R}(\delta)=\min_{\lambda\ge0}\bar V^\lambda-\delta\lambda$, $\;V^{\mathrm R}=V^{\mathrm R}(0)$; $\lambda^*(\delta)$ denotes a minimizer of (11).
--
--   **Lagrangian policy** (Definition 3.1, p. 14). From optimal solutions of (6), let $H_i$ be the largest level in the support $I_i=\{x:p_i(x)>0\}$. In state $x$ the policy uses $d_i(x_i,i,0)$ for a request $(i,0)$ and $d_i(x_i,0,i)$ for a request $(0,i)$, with $d_i(x,i,0)=1$ and $d_i(x,0,i)=0$ for $x>H_i$; in the original system it drops a request $(0,i)$ when the hub is empty.
--
--   **Chains.** Under this policy the spoke levels form a Markov chain on $\mathcal X$ (original system) and on $\bar{\mathcal X}=\{x:x_i\le m\ \forall i\}$ (relaxed system, hub level allowed negative). For a stationary distribution $\mu$ of the original chain, $V^{\pi(\delta)}=\sum_x\mu(x)R(x)$ with $R(x)$ the expected one-period revenue (37), and $\mathbb P[X_0(\delta)=0]=\mu\{x:\sum_ix_i=m\}$. In the relaxed system the stationary law is $\prod_ip_i(x_i)$ (Corollary B.10); $\mathbb P[\tilde X_0(\delta)\le0]$ is its mass on $\{\sum_ix_i\ge m\}$ and $\mathbb E[\tilde X_i(\delta)]=\sum_x x\,p_i(x)$. Finally $v_{i,t}(x)$ are the finite-horizon spoke values (35) of the Lagrangian controls, $v_{i,0}=0$.
--
--   **Formalization Note** Request types are `Fin n ⊕ Fin n` (`inl i` = $(i,0)$, `inr i` = $(0,i)$). The revenue functions $r_{ij}$ are primitives satisfying Assumption 2.1; the private-value distributions enter the paper only through $r_{ij}(d)=d\,G_{ij}(d)$. Policies are deterministic functions of the observed history (request types and fulfilment outcomes); the expected revenue $J_T$ is a finite recursion. The paper's $\lim$ in (1) and (3) is a `limsup` (the sequence $J_T/T$ is bounded by $\bar\omega$ and $\bar r$). $h_i^\lambda$ is defined by (6) (Proposition 3.2 identifies it with the spoke DP's optimal revenue), as an `sSup` over a nonempty set bounded above by $\bar r$; $V^{\mathrm R}(\delta)$ is an infimum over $\lambda\ge0$, bounded below by $0$ for $\delta\le m$. Stationary distributions are finite probability vectors, via the published definition `MarkovChain.IsStationary`. The hub is empty when $\sum_i x_i = m$; feasibility forbids fulfilling a hub request when $\sum_i x_i\ge m$.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, pp. 6–21 and 48: §2.2, Assumption 2.1, problem (1), (3)–(6), (9), (11), Definition 3.1, §4.2 (relaxed system), (35), (37)

import Mathlib
import Definitions.Def_MarkovChain

namespace HubSpokePricing.Lagrangian

open Finset

/-! # Hub-and-spoke relocation pricing (Balseiro, Brown & Chen, SSRN 3313737, May 23, 2020)

§2.2 (pp. 8–9): one hub (location 0) and `n` spokes `Fin n`, `m` resources. Request types are
`Fin n ⊕ Fin n`: `Sum.inl i` is the type `(i, 0)` (spoke `i` → hub, probability `qOut i = q_{i0}`)
and `Sum.inr i` is the type `(0, i)` (hub → spoke `i`, probability `qIn i = q_{0i}`).
`rOut i = r_{i0}` and `rIn i = r_{0i}` are the one-period expected revenue functions of the
demand level `d ∈ [0, 1]` (Assumption 2.1, p. 7). -/

/-- A hub-and-spoke network instance (§2.2, pp. 8–9; Assumption 2.1, p. 7). -/
structure Network where
  /-- number of spokes -/
  n : ℕ
  /-- number of resources -/
  m : ℕ
  /-- `qOut i = q_{i0}`: probability that the request is of type `(i, 0)` -/
  qOut : Fin n → ℝ
  /-- `qIn i = q_{0i}`: probability that the request is of type `(0, i)` -/
  qIn : Fin n → ℝ
  /-- `rOut i = r_{i0}` -/
  rOut : Fin n → ℝ → ℝ
  /-- `rIn i = r_{0i}` -/
  rIn : Fin n → ℝ → ℝ
  /-- the revenue bound `r̄` -/
  rbar : ℝ
  /-- the derivative bound `ω̄` -/
  omega : ℝ

/-- Assumption 2.1 (p. 7) for one revenue function `r`: strictly concave on `[0, 1]`, `r 0 = 0`,
`max_{[0,1]} r ≤ r̄`, `max_{[0,1]} |r'| ≤ ω̄`, and the maximum is attained in the interior `(0, 1)`. -/
def RevenueAssumption (rbar omega : ℝ) (r : ℝ → ℝ) : Prop :=
  StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) r ∧ r 0 = 0 ∧
  (∀ d ∈ Set.Icc (0 : ℝ) 1, r d ≤ rbar) ∧
  DifferentiableOn ℝ r (Set.Icc (0 : ℝ) 1) ∧
  (∀ d ∈ Set.Icc (0 : ℝ) 1, |derivWithin r (Set.Icc (0 : ℝ) 1) d| ≤ omega) ∧
  ∃ d ∈ Set.Ioo (0 : ℝ) 1, ∀ d' ∈ Set.Icc (0 : ℝ) 1, r d' ≤ r d

/-- The standing assumptions of §2.2 and Assumption 2.1: at least one spoke, `q_{i0}, q_{0i} > 0`
summing to one, `r̄, ω̄ > 0`, and every revenue function satisfies Assumption 2.1. -/
def Network.Standing (N : Network) : Prop :=
  1 ≤ N.n ∧ (∀ i, 0 < N.qOut i) ∧ (∀ i, 0 < N.qIn i) ∧
  ∑ i, (N.qOut i + N.qIn i) = 1 ∧ 0 < N.rbar ∧ 0 < N.omega ∧
  ∀ i, RevenueAssumption N.rbar N.omega (N.rOut i) ∧ RevenueAssumption N.rbar N.omega (N.rIn i)

/-- Request types: `Sum.inl i` is `(i, 0)`, `Sum.inr i` is `(0, i)`. -/
abbrev Req (N : Network) : Type := Fin N.n ⊕ Fin N.n

/-- Probability of each request type. -/
def Network.q (N : Network) : Req N → ℝ := Sum.elim N.qOut N.qIn

/-- Revenue function of each request type. -/
def Network.r (N : Network) : Req N → ℝ → ℝ := Sum.elim N.rOut N.rIn

/-! ## Problem (1): the optimal average revenue `V^OPT` (p. 9) -/

/-- An observed history: past request types and whether each was fulfilled. -/
abbrev History (N : Network) : Type := List (Req N × Bool)

/-- Spoke levels after one observed period. A fulfilled `(i, 0)` request moves one resource from
spoke `i` to the hub, a fulfilled `(0, i)` request moves one from the hub to spoke `i`. -/
def stepState (N : Network) (x : Fin N.n → ℕ) : Req N × Bool → Fin N.n → ℕ
  | (_, false) => x
  | (Sum.inl i, true) => Function.update x i (x i - 1)
  | (Sum.inr i, true) => Function.update x i (x i + 1)

/-- Spoke levels after an observed history, from initial spoke levels `x0`. -/
def stateAfter (N : Network) (x0 : Fin N.n → ℕ) (h : History N) : Fin N.n → ℕ :=
  h.foldl (stepState N) x0

/-- The origin of request `s` holds no resource at spoke levels `x` (hub level `m − ∑ x_i`). -/
def originEmpty (N : Network) (x : Fin N.n → ℕ) : Req N → Prop
  | Sum.inl i => x i = 0
  | Sum.inr _ => N.m ≤ ∑ j, x j

/-- A non-anticipative (history-dependent) pricing policy: the demand level chosen after an
observed history for the current request type. -/
abbrev Policy (N : Network) : Type := History N → Req N → ℝ

/-- Feasibility from initial spoke levels `x0` (constraints of (1)): every demand level lies in
`[0, 1]` and is `0` whenever the origin of the request is empty. -/
def Feasible (N : Network) (x0 : Fin N.n → ℕ) (π : Policy N) : Prop :=
  ∀ h s, 0 ≤ π h s ∧ π h s ≤ 1 ∧ (originEmpty N (stateAfter N x0 h) s → π h s = 0)

/-- Expected revenue over the next `T` periods after history `h`. The request is fulfilled with
probability `d` (the private value exceeds the price iff `ξ ≤ d`, `ξ ~ U[0, 1]`), earning
`r(d)` in expectation. -/
noncomputable def J (N : Network) (π : Policy N) : ℕ → History N → ℝ
  | 0, _ => 0
  | T + 1, h => ∑ s : Req N, N.q s *
      (N.r s (π h s) + π h s * J N π T (h ++ [(s, true)]) +
        (1 - π h s) * J N π T (h ++ [(s, false)]))

/-- The initial spoke levels lie in `𝒳 = {x ∈ ℕⁿ : ∑ x_i ≤ m}`. -/
def InX (N : Network) (x : Fin N.n → ℕ) : Prop := ∑ i, x i ≤ N.m

/-- `V^OPT` of problem (1), from initial spoke levels `x0`: the supremum over feasible
non-anticipative policies of the long-run (`limsup`) average expected revenue. -/
noncomputable def VOPT (N : Network) (x0 : Fin N.n → ℕ) : ℝ :=
  ⨆ π : {π : Policy N // Feasible N x0 π},
    Filter.limsup (fun T : ℕ => J N π.1 T [] / (T : ℝ)) Filter.atTop

/-! ## The spoke problem (6) (p. 12) and the dual problems (4), (9), (11) -/

/-- A candidate solution of the spoke problem (6): `p x = p_i(x)`, `dOut x = d_i(x, i, 0)`,
`dIn x = d_i(x, 0, i)` for resource levels `x ∈ [0 : m]`. -/
structure SpokeSol (m : ℕ) where
  p : Fin (m + 1) → ℝ
  dOut : Fin (m + 1) → ℝ
  dIn : Fin (m + 1) → ℝ

/-- The constraints of (6) for spoke `i`. -/
def SpokeFeasible (N : Network) (i : Fin N.n) (s : SpokeSol N.m) : Prop :=
  (∀ x, 0 ≤ s.p x) ∧ ∑ x, s.p x = 1 ∧
  (∀ x, 0 ≤ s.dOut x ∧ s.dOut x ≤ 1) ∧ (∀ x, 0 ≤ s.dIn x ∧ s.dIn x ≤ 1) ∧
  (∀ x : Fin N.m, s.p x.castSucc * N.qIn i * s.dIn x.castSucc =
      s.p x.succ * N.qOut i * s.dOut x.succ) ∧
  s.dOut 0 = 0 ∧ s.dIn (Fin.last N.m) = 0

/-- The objective of (6) for spoke `i` and dual variable `lam`. -/
noncomputable def spokeObj (N : Network) (lam : ℝ) (i : Fin N.n) (s : SpokeSol N.m) : ℝ :=
  ∑ x, s.p x * (N.qOut i * N.rOut i (s.dOut x) + N.qIn i * N.rIn i (s.dIn x)) -
    lam * ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x

/-- `h_i^λ`, the optimal value of (6). -/
noncomputable def h (N : Network) (lam : ℝ) (i : Fin N.n) : ℝ :=
  sSup (spokeObj N lam i '' {s | SpokeFeasible N i s})

/-- An optimal solution of (6). -/
def SpokeOptimal (N : Network) (lam : ℝ) (i : Fin N.n) (s : SpokeSol N.m) : Prop :=
  SpokeFeasible N i s ∧ spokeObj N lam i s = h N lam i

/-- `V̄^λ = mλ + ∑ᵢ h_i^λ`, (4). -/
noncomputable def Vbar (N : Network) (lam : ℝ) : ℝ := N.m * lam + ∑ i, h N lam i

/-- `V^R(δ) = min_{λ ≥ 0} V̄^λ − δλ`, (11). -/
noncomputable def VR (N : Network) (δ : ℝ) : ℝ := ⨅ lam : {lam : ℝ // 0 ≤ lam}, Vbar N lam - δ * lam

/-- `V^R = V^R(0) = min_{λ ≥ 0} V̄^λ`, (9). -/
noncomputable def VRstar (N : Network) : ℝ := VR N 0

/-- `lam` is an optimal solution `λ*(δ)` of (11). -/
def IsDualOpt (N : Network) (δ lam : ℝ) : Prop :=
  0 ≤ lam ∧ ∀ lam' : ℝ, 0 ≤ lam' → Vbar N lam - δ * lam ≤ Vbar N lam' - δ * lam'

/-! ## The Lagrangian relaxation (3) (p. 11) -/

/-- The initial spoke levels lie in `𝒳̄ = {x ∈ ℕⁿ : x_i ≤ m for all i}` (p. 11). -/
def InXbar (N : Network) (x : Fin N.n → ℕ) : Prop := ∀ i, x i ≤ N.m

/-- In the relaxation (3) a request cannot be fulfilled when it would take a spoke level outside
`[0, m]`: an `(i, 0)` request at `x_i = 0`, or a `(0, i)` request at `x_i = m`
(constraints `0 ≤ x_{i,t} ≤ m` of (3); the hub level may be negative). -/
def relaxBlocked (N : Network) (x : Fin N.n → ℕ) : Req N → Prop
  | Sum.inl i => x i = 0
  | Sum.inr i => N.m ≤ x i

/-- Feasibility in the relaxation (3) from initial spoke levels `x0`: every demand level lies in
`[0, 1]` and is `0` whenever the request is blocked. -/
def FeasibleRelax (N : Network) (x0 : Fin N.n → ℕ) (π : Policy N) : Prop :=
  ∀ h s, 0 ≤ π h s ∧ π h s ≤ 1 ∧ (relaxBlocked N (stateAfter N x0 h) s → π h s = 0)

/-- Expected revenue plus Lagrangian reward `λ (m − ∑ᵢ x_{i,t})` over the next `T` periods after
history `h`, in the relaxation (3) from initial spoke levels `x0`; the penalty of a period is
charged on the spoke levels at its beginning. -/
noncomputable def JRelax (N : Network) (lam : ℝ) (x0 : Fin N.n → ℕ) (π : Policy N) :
    ℕ → History N → ℝ
  | 0, _ => 0
  | T + 1, h => lam * ((N.m : ℝ) - ∑ i, ((stateAfter N x0 h i : ℕ) : ℝ)) +
      ∑ s : Req N, N.q s *
        (N.r s (π h s) + π h s * JRelax N lam x0 π T (h ++ [(s, true)]) +
          (1 - π h s) * JRelax N lam x0 π T (h ++ [(s, false)]))

/-- `V̄^λ` as the optimal value of the Lagrangian relaxation (3), from initial spoke levels `x0`:
the supremum over feasible non-anticipative policies of the long-run (`limsup`) average of
revenue plus `λ (m − ∑ᵢ x_{i,t})`. -/
noncomputable def VbarRelax (N : Network) (lam : ℝ) (x0 : Fin N.n → ℕ) : ℝ :=
  ⨆ π : {π : Policy N // FeasibleRelax N x0 π},
    Filter.limsup (fun T : ℕ => JRelax N lam x0 π.1 T [] / (T : ℝ)) Filter.atTop

/-! ## The Lagrangian policy (Definition 3.1, p. 14) -/

/-- `p_i(x)` extended by `0` beyond `m`. -/
def SpokeSol.pN {m : ℕ} (s : SpokeSol m) (x : ℕ) : ℝ :=
  if hx : x ≤ m then s.p ⟨x, Nat.lt_succ_of_le hx⟩ else 0

/-- `d_i(x, i, 0)` read at a natural number (`0` beyond `m`; never used there). -/
def SpokeSol.dOutN {m : ℕ} (s : SpokeSol m) (x : ℕ) : ℝ :=
  if hx : x ≤ m then s.dOut ⟨x, Nat.lt_succ_of_le hx⟩ else 0

/-- `d_i(x, 0, i)` read at a natural number (`0` beyond `m`; never used there). -/
def SpokeSol.dInN {m : ℕ} (s : SpokeSol m) (x : ℕ) : ℝ :=
  if hx : x ≤ m then s.dIn ⟨x, Nat.lt_succ_of_le hx⟩ else 0

/-- `H_i`, the largest resource level in the support `I_i = {x : p_i(x) > 0}`. -/
noncomputable def SpokeSol.top {m : ℕ} (s : SpokeSol m) : ℕ := by
  classical
  exact ((Finset.univ.filter fun x : Fin (m + 1) => 0 < s.p x).image (fun x => (x : ℕ))).sup id

/-- Lagrangian control for an `(i, 0)` request at spoke level `x`: the stored `d_i(x, i, 0)` for
`x ≤ H_i`, and `1` for `x > H_i` (Definition 3.1, step 2). -/
noncomputable def lagOut {m : ℕ} (s : SpokeSol m) (x : ℕ) : ℝ :=
  if x ≤ s.top then s.dOutN x else 1

/-- Lagrangian control for a `(0, i)` request at spoke level `x`: the stored `d_i(x, 0, i)` for
`x ≤ H_i`, and `0` for `x > H_i` (Definition 3.1, step 2). -/
noncomputable def lagIn {m : ℕ} (s : SpokeSol m) (x : ℕ) : ℝ :=
  if x ≤ s.top then s.dInN x else 0

/-! ## The original and relaxed systems under the Lagrangian policy -/

/-- States of the original system: spoke levels in `𝒳 = {x : ∑ x_i ≤ m}`
(the hub holds `m − ∑ x_i`). -/
abbrev OrigState (N : Network) : Type :=
  {x : Fin N.n → Fin (N.m + 1) // ∑ i, ((x i : ℕ)) ≤ N.m}

/-- States of the relaxed system: `𝒳̄ = {x : x_i ≤ m for all i}` (p. 11). -/
abbrev RelaxState (N : Network) : Type := Fin N.n → Fin (N.m + 1)

/-- Spoke levels as natural numbers. -/
def lv {N : Network} (x : Fin N.n → Fin (N.m + 1)) : Fin N.n → ℕ := fun i => (x i : ℕ)

/-- Demand level chosen by the Lagrangian policy in the original system: as in the relaxation,
except that a `(0, i)` request is dropped when the hub is empty. -/
noncomputable def origAccept (N : Network) (sol : Fin N.n → SpokeSol N.m) (x : Fin N.n → ℕ) :
    Req N → ℝ
  | Sum.inl i => lagOut (sol i) (x i)
  | Sum.inr i => if ∑ j, x j < N.m then lagIn (sol i) (x i) else 0

/-- Demand level chosen by the Lagrangian policy in the relaxed system. -/
noncomputable def relaxAccept (N : Network) (sol : Fin N.n → SpokeSol N.m) (x : Fin N.n → ℕ) :
    Req N → ℝ
  | Sum.inl i => lagOut (sol i) (x i)
  | Sum.inr i => lagIn (sol i) (x i)

/-- One-step transition probability `x → y` when request `s` is fulfilled with probability
`acc x s`. -/
noncomputable def kernelOf (N : Network) (acc : (Fin N.n → ℕ) → Req N → ℝ)
    (x y : Fin N.n → ℕ) : ℝ :=
  ∑ s : Req N, N.q s *
    (acc x s * (if stepState N x (s, true) = y then 1 else 0) +
      (1 - acc x s) * (if x = y then 1 else 0))

/-- Transition matrix of the original system under the Lagrangian policy, on `𝒳`. -/
noncomputable def origKernel (N : Network) (sol : Fin N.n → SpokeSol N.m) :
    Matrix (OrigState N) (OrigState N) ℝ :=
  fun x y => kernelOf N (origAccept N sol) (lv x.1) (lv y.1)

/-- Transition matrix of the relaxed system under the Lagrangian policy, on `𝒳̄`. -/
noncomputable def relaxKernel (N : Network) (sol : Fin N.n → SpokeSol N.m) :
    Matrix (RelaxState N) (RelaxState N) ℝ :=
  fun x y => kernelOf N (relaxAccept N sol) (lv x) (lv y)

/-- Expected one-period revenue of the Lagrangian policy in the original system at `x`, (37). -/
noncomputable def origReward (N : Network) (sol : Fin N.n → SpokeSol N.m) (x : OrigState N) : ℝ :=
  ∑ s : Req N, N.q s * N.r s (origAccept N sol (lv x.1) s)

/-- `V^π(δ)`: average revenue of the Lagrangian policy in the original system under the
stationary distribution `μ`. -/
noncomputable def Vpi (N : Network) (sol : Fin N.n → SpokeSol N.m) (μ : OrigState N → ℝ) : ℝ :=
  ∑ x, μ x * origReward N sol x

/-- `ℙ[X₀(δ) = 0]`: stationary probability that the hub is empty in the original system. -/
noncomputable def hubEmptyProb (N : Network) (μ : OrigState N → ℝ) : ℝ :=
  ∑ x : OrigState N, if ∑ i, ((x.1 i : ℕ)) = N.m then μ x else 0

/-- The product law `q(x) = ∏ᵢ p_i(x_i)` on `𝒳̄`. -/
def prodLaw (N : Network) (sol : Fin N.n → SpokeSol N.m) (x : RelaxState N) : ℝ :=
  ∏ i, (sol i).p (x i)

/-- `ℙ[X̃₀(δ) ≤ 0]` in the relaxed system, whose stationary law is `∏ᵢ p_i(x_i)`
(Corollary B.10): the probability that `∑ᵢ X̃ᵢ ≥ m`. -/
noncomputable def relaxDepletionProb (N : Network) (sol : Fin N.n → SpokeSol N.m) : ℝ :=
  ∑ x : RelaxState N, if N.m ≤ ∑ i, ((x i : ℕ)) then prodLaw N sol x else 0

/-- `∑ₓ x p(x)`, the mean of a spoke's stationary distribution (`= 𝔼[X̃ᵢ(δ)]`). -/
def spokeMean {m : ℕ} (s : SpokeSol m) : ℝ := ∑ x : Fin (m + 1), ((x : ℕ) : ℝ) * s.p x

/-- Finite-horizon average value `v_{i,t}(x)` of spoke `i` under the Lagrangian controls, (35)
(p. 48), averaged over request types; `v_{i,0} = 0`. -/
noncomputable def spokeValue (N : Network) (i : Fin N.n) (s : SpokeSol N.m) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t + 1, x =>
      N.qOut i * (N.rOut i (lagOut s x) +
          lagOut s x * (spokeValue N i s t (x - 1) - spokeValue N i s t x)) +
        N.qIn i * (N.rIn i (lagIn s x) +
          lagIn s x * (spokeValue N i s t (x + 1) - spokeValue N i s t x)) +
        spokeValue N i s t x

end HubSpokePricing.Lagrangian


