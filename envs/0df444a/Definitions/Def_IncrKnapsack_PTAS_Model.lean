-- Prove2me | Definitions.Def_IncrKnapsack_PTAS_Model
-- name    : IncrKnapsack_PTAS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:13:36.502258+00:00
-- url     : https://prove2.me/theorems/def16d09-853f-4908-8ff4-69d0b16a949b
-- title:
--   §1.2, §2.2, §3.2–§3.5 — incremental knapsack, profit classes, clusters, uncrossing stars, the exact and approximate cluster DPs, the glued solution
-- statement:
--   This file sets up the incremental knapsack problem of Aouad and Segev and every object of the general approximation scheme of their Section 3.
--
--   **Instances and solutions (§1.2).** An instance has $n$ items, item $i$ with profit $p_i$ and weight $w_i$, and $T$ periods, period $t$ with a coefficient $\lambda_t$ and a capacity $W_t$. The standing assumptions are: $n \ge 1$, $T \ge 1$; $p_i > 0$ and $w_i > 0$; $W_1 \le \dots \le W_T$; $\lambda_t \ge 0$ and $\lambda_T > 0$. Two further conventions are added and disclosed below: capacities are nonnegative, and every item fits into the last capacity, $w_i \le W_T$. A solution $\mathcal S = \langle S_1, \dots, S_T\rangle$ is a nested sequence $S_1 \subseteq \dots \subseteq S_T$; it is recorded by the period $\nu(i,\mathcal S)$ in which each item of $S_T$ is introduced. It is feasible when $w(S_t) \le W_t$ for every $t$. With $\lambda^{t+} = \sum_{\tau = t}^{T} \lambda_\tau$, the objective and the item contributions are
--
--   $$\Psi(\mathcal S) = \sum_{t \in [T]} \lambda_t \, p(S_t), \qquad \Psi_i(\mathcal S) = p_i \, \lambda^{\nu(i,\mathcal S)+}.$$
--
--   **Profit classes (§2.2).** For an accuracy $\epsilon = 1/K$, profits are scaled so that $\min_i p_i = 1$ and rounded down to a power of $1+\epsilon$. Item $i$ then has the profit $(1+\epsilon)^{\ell(i)}$ and lies in the class $\mathcal P_{\ell(i)}$. $L$ is the largest class index and $p_{\max}$ the largest rounded profit.
--
--   **Intervals and clusters (§3.2).** The interval $I_m$ collects the periods with $\lambda^{t+} \in ((\epsilon/n)^m \lambda^{1+}, (\epsilon/n)^{m-1}\lambda^{1+}]$. For a shift $\xi \in \{0, \dots, 1/\epsilon - 1\}$ the interval $I_m$ is bad when $m \bmod (1/\epsilon) = \xi$ and good otherwise. A period of a good interval belongs to the cluster $\mathcal C_c$, where $c - 1$ is the number of bad intervals before its own. $M$ is the index of the last non-empty cluster.
--
--   **Filtering and uncrossing stars (§3.3).** $\mathcal S_\xi$ keeps only the items introduced in good periods. Filtering removes every item with $\Psi_i(\mathcal S) \le (\epsilon/n)\Psi(\mathcal S)$. A solution is a collection of *uncrossing stars* when every profit class is introduced in at most one cluster, and a lower class is never introduced in a later cluster than a higher class.
--
--   **Exact program (§3.4).** $F(m, \ell, \varphi)$ is the least weight $w(S_T)$ of a feasible uncrossing-stars solution with three properties: it introduces items only in good periods of $\mathcal C_1, \dots, \mathcal C_m$; it uses only the classes $\mathcal P_0, \dots, \mathcal P_\ell$; and its profit is at least $\varphi$. The value is $\infty$ when no such solution exists. $\mathrm{OPT}(\mathcal I^{\phi,\omega}_{\mathrm{single}}[m, a, b])$ is the least weight of a solution with the following properties: it uses only the classes $\mathcal P_a, \dots, \mathcal P_b$; it introduces items only in periods of $\mathcal C_m$, each with the adjusted capacity $[W_t - \omega]^+$; and its profit is at least $\phi$.
--
--   **Approximate program and output (§3.5).** A *subroutine* returns, for $\phi, \omega \ge 0$, a solution of the single-cluster instance's constraints with weight at most $\mathrm{OPT}$ (super-optimality, (8)) and profit at least $(1-\epsilon)\phi$. It returns something whenever the instance is feasible; this is the guarantee of Theorem 3. Put $\delta = (\epsilon/M)\lambda_T p_{\max}$. A *profit grid* $\Phi$ is a finite set of nonnegative reals containing $0$ such that every $\varphi \in [0, \lambda^{1+}\sum_i p_i]$ has a grid point $x \le \varphi \le (1+\epsilon/M)x + \delta$. The approximate program is
--
--   $$\tilde F(m, \ell_m, \varphi_m) = \min_{\ell_{m-1} \in \{-1,\dots,\ell_m\},\ \varphi_{m-1} \in [0,\varphi_m] \cap \Phi} \Big\{ \tilde F(m-1, \ell_{m-1}, \varphi_{m-1}) + w\big(\mathcal A(\mathcal I^{\phi,\omega}_{\mathrm{single}}[m, \ell_{m-1}+1, \ell_m])\big) \Big\},$$
--
--   with $\phi = [\varphi_m - (1+\epsilon/M)\varphi_{m-1} - \delta]^+$ and $\omega = \tilde F(m-1, \ell_{m-1}, \varphi_{m-1})$. Terminal states ($m = 0$ or $\ell_m = -1$) have value $0$ at $\varphi = 0$ and $\infty$ otherwise. A *traceback* is a sequence of states $(m, \tilde\ell_m, \tilde\varphi_m)$, $m = 0, \dots, M$, with three properties: $\tilde\ell_M = L$; $\tilde\varphi_M$ is the largest grid point with $\tilde F(M, L, \tilde\varphi_M) < \infty$; and each predecessor attains the minimum defining its successor. The output $\bar{\mathcal S}$ glues the subroutine's solutions along a traceback: in the periods of $\mathcal C_m$ it introduces exactly the items that the $m$-th single-cluster solution introduces there.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Periods are 0-based (`Fin T`): the paper's period $t$ is Lean's `t - 1`. Class bounds are shifted by one, so the Lean index `j = ℓ + 1` runs over $0, \dots, L+1$ and "classes $< j$" means $\mathcal P_0, \dots, \mathcal P_{\ell}$. The value $\infty$ is `⊤ : WithTop ℝ`, and minima over finite sets are `Finset.inf` (empty set ↦ `⊤`). Profits are a parameter of $\Psi$; `pr` are the scaled rounded profits $(1+\epsilon)^{\ell(i)}$. Disclosed additions and corrections, each discussed in the mission description:
--   1. `W_nonneg` and `fits` ($w_i \le W_T$, used in the last step of the proof of Lemma 11, p. 29) are added to the standing assumptions.
--   2. The profit of a multi- or single-cluster solution is the sum of item contributions with the full-horizon $\lambda^{t+}$. Page 23 truncates it at $\max\mathcal C_m$, which breaks the additivity used in Lemma 9.
--   3. $\ell_{m-1}$ may be $-1$; page 25 prints $[\ell_m]_0$.
--   4. The printed grid (7) is replaced by the property (15) that the proofs use, on $[0, \lambda^{1+}\sum_i p_i]$, the range page 22 gives $\varphi_m$. The coverage clause is guarded by $M > 0$.
--   5. The subroutine and the traceback's choices among minimizers are the only abstracted components.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, pp. 5–8, 20–27, §1.2, §2.2, §3.2–§3.5, eqs. (7), (8), (15)

import Mathlib

open Classical
open Finset BigOperators

noncomputable section

namespace IncrKnapsack.PTAS

/-! ## §1.2 — the incremental knapsack problem -/

/-- An instance of incremental knapsack (§1.2, p. 5): `n` items with profits `p i` and weights
`w i`, `T` periods with coefficients `lam t` (the paper's `λ_t`) and capacities `W t`.
Periods are 0-based: the paper's period `t` is `⟨t - 1, _⟩ : Fin T`. -/
structure Instance where
  n : ℕ
  T : ℕ
  p : Fin n → ℝ
  w : Fin n → ℝ
  lam : Fin T → ℝ
  W : Fin T → ℝ

/-- `λ_T`, the coefficient of the last period (`0` when `T = 0`). -/
def lamLast (I : Instance) : ℝ :=
  if h : 0 < I.T then I.lam ⟨I.T - 1, by omega⟩ else 0

/-- `W_T`, the capacity of the last period (`0` when `T = 0`). -/
def WLast (I : Instance) : ℝ :=
  if h : 0 < I.T then I.W ⟨I.T - 1, by omega⟩ else 0

/-- The standing assumptions of §1.2 (p. 5). `W_nonneg` (capacities are nonnegative) and
`fits` (`w_i ≤ W_T`) are disclosed additions, see the natural-language statement. -/
structure Instance.Standing (I : Instance) : Prop where
  n_pos : 0 < I.n
  T_pos : 0 < I.T
  p_pos : ∀ i, 0 < I.p i
  w_pos : ∀ i, 0 < I.w i
  W_mono : Monotone I.W
  W_nonneg : ∀ t, 0 ≤ I.W t
  lam_nonneg : ∀ t, 0 ≤ I.lam t
  lam_last_pos : 0 < lamLast I
  fits : ∀ i, I.w i ≤ WLast I

/-- A solution, recorded by introduction period: `S i = some t` means item `i` is introduced in
period `t` (`ν(i, S) = t`), `S i = none` means `i ∉ S_T`. Nestedness `S_1 ⊆ ⋯ ⊆ S_T` is built in. -/
abbrev Sol (I : Instance) := Fin I.n → Option (Fin I.T)

/-- The item set `S_t`: items introduced in some period `s ≤ t`. -/
def Sol.set {I : Instance} (S : Sol I) (t : Fin I.T) : Finset (Fin I.n) :=
  univ.filter (fun i => ∃ s, S i = some s ∧ s ≤ t)

/-- Capacity feasibility: `w(S_t) ≤ W_t` for every period `t`. -/
def Feasible (I : Instance) (S : Sol I) : Prop :=
  ∀ t, ∑ i ∈ Sol.set S t, I.w i ≤ I.W t

/-- `λ^{t+} = ∑_{τ = t}^{T} λ_τ`. -/
def lamPlus (I : Instance) (t : Fin I.T) : ℝ :=
  ∑ τ ∈ univ.filter (fun τ => t ≤ τ), I.lam τ

/-- `λ^{1+} = ∑_{t ∈ [T]} λ_t`. -/
def lamTotal (I : Instance) : ℝ :=
  ∑ t, I.lam t

/-- The objective `Ψ(S) = ∑_{t ∈ [T]} λ_t · p(S_t)`, with the profit vector `p` as a parameter. -/
def Psi (I : Instance) (p : Fin I.n → ℝ) (S : Sol I) : ℝ :=
  ∑ t, I.lam t * ∑ i ∈ Sol.set S t, p i

/-- The item contribution `Ψ_i(S) = p_i · λ^{ν(i,S)+}` (and `0` for `i ∉ S_T`). -/
def psiItem (I : Instance) (p : Fin I.n → ℝ) (S : Sol I) (i : Fin I.n) : ℝ :=
  match S i with
  | some t => p i * lamPlus I t
  | none => 0

/-- The sum of item contributions `∑_{i ∈ S_T} Ψ_i(S)` (right-hand side of (1), p. 6). -/
def contrib (I : Instance) (p : Fin I.n → ℝ) (S : Sol I) : ℝ :=
  ∑ i, psiItem I p S i

/-- The total weight `w(S_T)` of the items a solution ever introduces. -/
def weight (I : Instance) (S : Sol I) : ℝ :=
  ∑ i ∈ univ.filter (fun i => (S i).isSome), I.w i

/-- `S` is an optimal solution for the profit vector `p`. -/
def IsOptimal (I : Instance) (p : Fin I.n → ℝ) (S : Sol I) : Prop :=
  Feasible I S ∧ ∀ S' : Sol I, Feasible I S' → Psi I p S' ≤ Psi I p S

/-! ## §2.2 — profit classes, with accuracy `ε = 1/K` -/

/-- The accuracy level `ε = 1/K`. -/
def eps (K : ℕ) : ℝ := 1 / (K : ℝ)

/-- `min_i p_i` (junk value `1` when there are no items). -/
def pmin (I : Instance) : ℝ :=
  if h : (univ : Finset (Fin I.n)).Nonempty then univ.inf' h I.p else 1

/-- The profit class index of item `i`: after scaling so that `min p = 1`, its profit is rounded
down to `(1 + ε)^{cls i}`. -/
def cls (I : Instance) (K : ℕ) (i : Fin I.n) : ℕ :=
  ⌊Real.logb (1 + eps K) (I.p i / pmin I)⌋₊

/-- The scaled and rounded profit `(1 + ε)^{cls i}`; item `i` lies in the class `P_{cls i}`. -/
def pr (I : Instance) (K : ℕ) (i : Fin I.n) : ℝ :=
  (1 + eps K) ^ cls I K i

/-- `L`, the maximal index of a non-empty profit class. -/
def Lmax (I : Instance) (K : ℕ) : ℕ :=
  univ.sup (cls I K)

/-- `p_max`, the largest rounded profit (junk value `0` when there are no items). -/
def pmax (I : Instance) (K : ℕ) : ℝ :=
  if h : (univ : Finset (Fin I.n)).Nonempty then univ.sup' h (pr I K) else 0

/-! ## §3.2 — intervals and clusters for a shift `ξ ∈ {0, …, K - 1}` -/

/-- `ivl t = m - 1` when period `t` lies in the interval
`I_m = {t : λ^{t+} ∈ ((ε/n)^m λ^{1+}, (ε/n)^{m-1} λ^{1+}]}`, i.e. the least `k` with
`(ε/n)^{k+1} λ^{1+} < λ^{t+}` (junk value `0` if there is none). -/
def ivl (I : Instance) (K : ℕ) (t : Fin I.T) : ℕ :=
  if h : ∃ k : ℕ, (eps K / (I.n : ℝ)) ^ (k + 1) * lamTotal I < lamPlus I t then Nat.find h else 0

/-- Period `t` lies in a good interval: its interval index `m = ivl t + 1` has `m mod K ≠ ξ`. -/
def IsGood (I : Instance) (K ξ : ℕ) (t : Fin I.T) : Prop :=
  (ivl I K t + 1) % K ≠ ξ

/-- The cluster index of a period in a good interval: one plus the number of bad interval
indices `m' ≥ 1` below its own interval index. -/
def clus (I : Instance) (K ξ : ℕ) (t : Fin I.T) : ℕ :=
  1 + ((Finset.Ico 1 (ivl I K t + 1)).filter (fun m => m % K = ξ)).card

/-- `M`, the index of the last non-empty cluster (`0` if no period is good). -/
def Mcl (I : Instance) (K ξ : ℕ) : ℕ :=
  (univ.filter (IsGood I K ξ)).sup (clus I K ξ)

/-! ## §3.2–§3.3 — dropping bad periods, filtering, uncrossing stars -/

/-- `S_ξ`: keep only the items that `S` introduces in good periods (p. 20). -/
def restrictGood (I : Instance) (K ξ : ℕ) (S : Sol I) : Sol I :=
  fun i => (S i).filter (fun t => decide (IsGood I K ξ t))

/-- Filtering (p. 21): eliminate every item with `Ψ_i(S) ≤ (ε/n) · Ψ(S)`. -/
def filt (I : Instance) (K : ℕ) (p : Fin I.n → ℝ) (S : Sol I) : Sol I :=
  fun i => if psiItem I p S i ≤ eps K / (I.n : ℝ) * Psi I p S then none else S i

/-- The solution graph `G(S)` is a collection of uncrossing stars (p. 21): (1) every profit class
is joined to at most one cluster; (2) no edges `(C_{m₁}, P_{ℓ₁})`, `(C_{m₂}, P_{ℓ₂})` with
`ℓ₁ < ℓ₂` and `m₁ > m₂`. -/
def UncrossingStars (I : Instance) (K ξ : ℕ) (S : Sol I) : Prop :=
  (∀ i j t s, S i = some t → S j = some s → cls I K i = cls I K j →
      clus I K ξ t = clus I K ξ s) ∧
  (∀ i j t s, S i = some t → S j = some s → cls I K i < cls I K j →
      clus I K ξ t ≤ clus I K ξ s)

/-! ## §3.4 — the exact dynamic program. Class bounds are shifted: `j = ℓ + 1`. -/

/-- Feasibility for the multi-cluster instance `I^{ϕ}_multi[m, j - 1]` (p. 23): a feasible
uncrossing-stars solution introducing items only in good periods of the clusters `C_1, …, C_m`,
only from the classes `P_0, …, P_{j-1}`, with profit (sum of item contributions, rounded
profits) at least `ϕ`. -/
def MultiFeas (I : Instance) (K ξ : ℕ) (m j : ℕ) (ϕ : ℝ) (S : Sol I) : Prop :=
  Feasible I S ∧ UncrossingStars I K ξ S ∧
  (∀ i t, S i = some t → IsGood I K ξ t ∧ clus I K ξ t ≤ m ∧ cls I K i < j) ∧
  ϕ ≤ contrib I (pr I K) S

/-- The value function `F(m, j - 1, ϕ)` (p. 23): the least weight of a solution feasible for
`I^{ϕ}_multi[m, j - 1]`, and `⊤ = ∞` when there is none. -/
def F (I : Instance) (K ξ : ℕ) (m j : ℕ) (ϕ : ℝ) : WithTop ℝ :=
  (univ.filter (MultiFeas I K ξ m j ϕ)).inf (fun S => ((weight I S : ℝ) : WithTop ℝ))

/-- The constraints of the single-cluster instance `I^{φ,ω}_single[m, a, b]` (p. 23) other than
the profit requirement: items only from the classes `P_a, …, P_b`, introduced only in periods
of the cluster `C_m`, each such period with the adjusted capacity `[W_t - ω]⁺`. -/
def SingleAdm (I : Instance) (K ξ : ℕ) (m a b : ℕ) (ω : ℝ) (S : Sol I) : Prop :=
  (∀ i t, S i = some t →
      IsGood I K ξ t ∧ clus I K ξ t = m ∧ a ≤ cls I K i ∧ cls I K i ≤ b) ∧
  (∀ t, IsGood I K ξ t → clus I K ξ t = m → ∑ i ∈ Sol.set S t, I.w i ≤ max (I.W t - ω) 0)

/-- Feasibility for `I^{φ,ω}_single[m, a, b]`: the constraints above and profit at least `φ`
(sum of item contributions with the full-horizon `λ^{t+}`, rounded profits). -/
def SingleFeas (I : Instance) (K ξ : ℕ) (m a b : ℕ) (φ ω : ℝ) (S : Sol I) : Prop :=
  SingleAdm I K ξ m a b ω S ∧ φ ≤ contrib I (pr I K) S

/-- `OPT(I^{φ,ω}_single[m, a, b])`: the least weight `w(S_{max C_m})`, `⊤ = ∞` if infeasible. -/
def OPTsingle (I : Instance) (K ξ : ℕ) (m a b : ℕ) (φ ω : ℝ) : WithTop ℝ :=
  (univ.filter (SingleFeas I K ξ m a b φ ω)).inf (fun S => ((weight I S : ℝ) : WithTop ℝ))

/-- Items introduced by `S` in clusters `≤ m` (the solution `S^{<m+1}` of p. 24). -/
def lowPart (I : Instance) (K ξ : ℕ) (S : Sol I) (m : ℕ) : Sol I :=
  fun i => (S i).filter (fun t => decide (clus I K ξ t ≤ m))

/-- Items introduced by `S` in clusters `> m` (the marginal solution `S^{m+1}` of p. 24). -/
def highPart (I : Instance) (K ξ : ℕ) (S : Sol I) (m : ℕ) : Sol I :=
  fun i => (S i).filter (fun t => decide (m < clus I K ξ t))

/-- One plus the largest class index used by `S` (`0` if `S` is empty): the shifted `ℓ_{m-1} + 1`. -/
def classTop (I : Instance) (K : ℕ) (S : Sol I) : ℕ :=
  (univ.filter (fun i => (S i).isSome)).sup (fun i => cls I K i + 1)

/-! ## §3.5 — the approximate dynamic program and the glued solution -/

/-- A single-cluster subroutine: on input `(m, a, b, φ, ω)` it returns a solution or nothing. -/
abbrev Subroutine (I : Instance) := ℕ → ℕ → ℕ → ℝ → ℝ → Option (Sol I)

/-- The guarantee of Theorem 3 as §3.5 uses it (p. 26): for `φ ≥ 0` and `ω ≥ 0`, every returned
solution obeys the constraints of `I^{φ,ω}_single[m, a, b]`, is super-optimal (weight at most
`OPT`, (8)) and has profit at least `(1 - ε) φ`; and a solution is returned whenever the
instance is feasible. -/
def IsSubroutine (I : Instance) (K ξ : ℕ) (A : Subroutine I) : Prop :=
  ∀ m a b : ℕ, ∀ φ ω : ℝ, 0 ≤ φ → 0 ≤ ω →
    (∀ S, A m a b φ ω = some S →
        SingleAdm I K ξ m a b ω S ∧ (1 - eps K) * φ ≤ contrib I (pr I K) S ∧
        ((weight I S : ℝ) : WithTop ℝ) ≤ OPTsingle I K ξ m a b φ ω) ∧
    ((∃ S, SingleFeas I K ξ m a b φ ω S) → (A m a b φ ω).isSome)

/-- `δ = (ε/M) · λ_T · p_max` (p. 26). -/
def delta (I : Instance) (K ξ : ℕ) : ℝ :=
  eps K / (Mcl I K ξ : ℝ) * lamLast I * pmax I K

/-- An admissible profit grid: `0 ∈ Φ`, `Φ ⊆ [0, ∞)`, and, when `M > 0`, every
`ϕ ∈ [0, λ^{1+} ∑_i p_i]` has a grid point `x ≤ ϕ` with `ϕ ≤ (1 + ε/M) x + δ` (property (15),
p. 35). This replaces the printed grid (7), whose range is too short. -/
def IsProfitGrid (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) : Prop :=
  0 ∈ Φ ∧ (∀ x ∈ Φ, 0 ≤ x) ∧
  (0 < Mcl I K ξ → ∀ ϕ : ℝ, 0 ≤ ϕ → ϕ ≤ lamTotal I * ∑ i, pr I K i →
      ∃ x ∈ Φ, x ≤ ϕ ∧ ϕ ≤ (1 + eps K / (Mcl I K ξ : ℝ)) * x + delta I K ξ)

/-- Weight of a subroutine answer, `⊤` when it returns nothing. -/
def wOpt {I : Instance} : Option (Sol I) → WithTop ℝ
  | some S => ((weight I S : ℝ) : WithTop ℝ)
  | none => ⊤

/-- The discretized profit requirement `φ = [ϕ_m - (1 + ε/M) ϕ_{m-1} - δ]⁺` (p. 26). -/
def phiReq (I : Instance) (K ξ : ℕ) (ϕ ϕ' : ℝ) : ℝ :=
  max (ϕ - (1 + eps K / (Mcl I K ξ : ℝ)) * ϕ' - delta I K ξ) 0

/-- The approximate program `F̃(m, j - 1, ϕ)` (pp. 26–27), with class bound shifted `j = ℓ + 1`:
terminal states `m = 0` or `j = 0` have value `0` at `ϕ = 0` and `⊤` otherwise; otherwise the
minimum over `j' ≤ j` (`ℓ_{m-1} ∈ {-1, …, ℓ_m}`) and `ϕ' ∈ Φ ∩ (-∞, ϕ]` of
`F̃(m-1, j', ϕ') + w(A(m, j', j - 1, φ, ω))` with `ω = F̃(m-1, j', ϕ')`. -/
def Ftil (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I) : ℕ → ℕ → ℝ → WithTop ℝ
  | 0, _, ϕ => if ϕ = 0 then 0 else ⊤
  | _ + 1, 0, ϕ => if ϕ = 0 then 0 else ⊤
  | m + 1, j + 1, ϕ =>
      ((range (j + 2)) ×ˢ (Φ.filter (fun x => x ≤ ϕ))).inf fun q =>
        Ftil I K ξ Φ A m q.1 q.2 +
          wOpt (A (m + 1) q.1 j (phiReq I K ξ ϕ q.2) ((Ftil I K ξ Φ A m q.1 q.2).untopD 0))

/-- The real value `ω̃` passed to the subroutine (`⊤` read as `0`; it is used only where the
accompanying `F̃` term is finite). -/
def omegaOf (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I) (m j : ℕ) (ϕ : ℝ) : ℝ :=
  (Ftil I K ξ Φ A m j ϕ).untopD 0

/-- A traceback `(m, jt m - 1, ϕt m)`, `m = 0, …, M`, of the states traversed by `F̃` in
reaching `(M, L, ϕ̃_M)` (p. 27): `jt M = L + 1`; `ϕ̃_M = ϕt M` is the largest grid point with
`F̃(M, L, ϕ̃_M) < ∞`; at every `1 ≤ m ≤ M` with `jt m ≠ 0` the predecessor attains the minimum
defining `F̃(m, jt m - 1, ϕt m)`, and below a terminal state `jt m = 0` the states are
`(m - 1, -1, 0)`. Any choice among minimizers is allowed. -/
def IsTraceback (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I)
    (jt : ℕ → ℕ) (ϕt : ℕ → ℝ) : Prop :=
  jt (Mcl I K ξ) = Lmax I K + 1 ∧
  ϕt (Mcl I K ξ) ∈ Φ ∧
  Ftil I K ξ Φ A (Mcl I K ξ) (Lmax I K + 1) (ϕt (Mcl I K ξ)) < ⊤ ∧
  (∀ x ∈ Φ, Ftil I K ξ Φ A (Mcl I K ξ) (Lmax I K + 1) x < ⊤ → x ≤ ϕt (Mcl I K ξ)) ∧
  ∀ m : ℕ, 1 ≤ m → m ≤ Mcl I K ξ →
    (jt m = 0 → jt (m - 1) = 0 ∧ ϕt (m - 1) = 0) ∧
    (jt m ≠ 0 →
      jt (m - 1) ≤ jt m ∧ ϕt (m - 1) ∈ Φ ∧ ϕt (m - 1) ≤ ϕt m ∧
      Ftil I K ξ Φ A m (jt m) (ϕt m) =
        Ftil I K ξ Φ A (m - 1) (jt (m - 1)) (ϕt (m - 1)) +
          wOpt (A m (jt (m - 1)) (jt m - 1) (phiReq I K ξ (ϕt m) (ϕt (m - 1)))
            (omegaOf I K ξ Φ A (m - 1) (jt (m - 1)) (ϕt (m - 1)))))

/-- The single-cluster solution `S̃^m` generated at state `m` of the traceback (`none` at a
terminal state). -/
def outs (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I)
    (jt : ℕ → ℕ) (ϕt : ℕ → ℝ) (m : ℕ) : Option (Sol I) :=
  if jt m = 0 then none
  else A m (jt (m - 1)) (jt m - 1) (phiReq I K ξ (ϕt m) (ϕt (m - 1)))
    (omegaOf I K ξ Φ A (m - 1) (jt (m - 1)) (ϕt (m - 1)))

/-- The period, inside the cluster `C_m`, in which `S̃^m` introduces item `i` (if any). -/
def introAt (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I)
    (jt : ℕ → ℕ) (ϕt : ℕ → ℝ) (m : ℕ) (i : Fin I.n) : Option (Fin I.T) :=
  match outs I K ξ Φ A jt ϕt m with
  | some S => (S i).filter (fun t => decide (IsGood I K ξ t ∧ clus I K ξ t = m))
  | none => none

/-- The glued solution `S̄` (p. 27): at every period `t ∈ C_m` it introduces exactly the items
that `S̃^m` introduces at `t` (an item claimed by several clusters is taken from the first). -/
def algOut (I : Instance) (K ξ : ℕ) (Φ : Finset ℝ) (A : Subroutine I)
    (jt : ℕ → ℕ) (ϕt : ℕ → ℝ) : Sol I :=
  fun i => (List.range' 1 (Mcl I K ξ)).findSome? (fun m => introAt I K ξ Φ A jt ϕt m i)

end IncrKnapsack.PTAS


