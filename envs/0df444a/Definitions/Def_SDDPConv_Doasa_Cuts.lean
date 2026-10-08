-- Prove2me | Definitions.Def_SDDPConv_Doasa_Cuts
-- name    : SDDPConv_Doasa_Cuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:02:05.175209+00:00
-- url     : https://prove2.me/theorems/ea195272-5370-4923-a7cc-7c66b4b7effe
-- title:
--   [AP_t^k], cuts, the dual region 𝓗_t, optimal extreme-point duals and the CCA cut formula (§2, pp. 4–6)
-- statement:
--   This file defines the approximate stage problems of §2 (p. 4) and the ingredients of the Cut Calculation Algorithm (CCA, p. 5).
--
--   1. A **cut** on $\theta_{t+1}$ is a pair $(\alpha,\beta)$ with $\beta\in\mathbb R^{n_t}$; it stands for $\theta_{t+1}\ge\alpha-\beta^\top x_t$.
--   2. Given a set $\mathcal C$ of cuts and a right-hand side $h$, the approximate problem [AP$_t$] is
--   $$\min_{x_t,\theta_{t+1}}\ c_t^\top x_t+\theta_{t+1}\quad\text{s.t.}\quad A_tx_t=h,\ \ x_t\ge0,\ \ \theta_{t+1}\ge\alpha-\beta^\top x_t\ \ \forall(\alpha,\beta)\in\mathcal C.$$
--   Its optimal value is $C^k_t(x_{t-1},\omega_t)$ when $\mathcal C$ is the cut set of iteration $k$ and $h=\omega_t-B_{t-1}x_{t-1}$, and $C^k_1$ for $t=1$, $h=b_1$.
--   3. The **initial cut** ($j=0$) of stage $t<T$ is $\theta_{t+1}\ge L_t$ for a given number $L_t$; it is **valid** if $L_t\le\mathcal Q_{t+1}(x_t)$ for every reachable $x_t$. For stage $T$ the only cut is $\theta_{T+1}\ge 0$, so that [AP$_T$] coincides with [LP$_T$].
--   4. For a cut list $(\alpha_j,\beta_j)_{j=0,\dots,K-1}$, the **dual region** of [AP$_t$] is
--   $$\mathcal H_t=\Big\{(\pi,\rho)\;:\;A_t^\top\pi+\sum_{j}\rho_j\beta_j\le c_t,\ \ \sum_j\rho_j=1,\ \ \rho\ge0\Big\},$$
--   with dual objective $\pi^\top h+\sum_j\rho_j\alpha_j$. An **optimal extreme-point dual** is an extreme point of $\mathcal H_t$ maximizing it; a **best dual** in a collection $\mathcal D$ maximizes it over $\mathcal D$.
--   5. **CCA step 3**: from one dual $(\pi^i,\rho^i)$ of stage $t$ per outcome $\omega_{ti}$, the new cut on $\theta_t$ is
--   $$\beta=\sum_{i=1}^{q_t}p_{ti}B_{t-1}^\top\pi^i,\qquad \alpha=\sum_{i=1}^{q_t}p_{ti}\big(\omega_{ti}^\top\pi^i+\textstyle\sum_j\rho^i_j\alpha_j\big).$$
--
--   These are the building blocks of the DOASA run in the next definition file.
--
--   **Formalization Note** The paper's first cut is the trivial cut $\theta_{t+1}\ge-\infty$ (p. 4); with it [AP$_t^1$] is unbounded, contradicting the paper's own "hence an optimal solution" (p. 4). We replace it by the finite cut $(L_t,0)$, whose validity is a separate hypothesis (`ValidInit`). Stage $T$ is uniformized with the constant cut list $[(0,0)]$, valid since $\mathcal Q_{T+1}\equiv0$; its dual region is the paper's $\{\pi: A_T^\top\pi\le c_T\}$ with $\rho=e_0$. The dual multiplier $\rho$ is a sequence $\mathbb N\to\mathbb R$ indexed by the position in the cut list (including the initial cut $j=0$, which the paper's sums $j=1,\dots,k-1$ omit because its $j=0$ cut is vacuous) and zero beyond the list's length, so that duals collected at earlier iterations remain comparable as the list grows. Cut sets in [AP$_t$] are sets; the optimal value `apVal` is a real infimum and is used only where the feasible region is nonempty and bounded.
-- source:
--   Philpott & Guan, On the convergence of stochastic dual dynamic programming and related methods, authors' manuscript v24 (2008-02-25), p. 4, [AP^k_1], [AP^k_t]; p. 5, CCA steps 1–3; p. 6, the dual region 𝓗^k_t in the proof of Lemma 1

import Mathlib
import Definitions.Def_SDDPConv_Doasa_Model

open Matrix

namespace SDDPConv.Doasa

variable (I : Instance)

/-- A cut on `θ_{t+1}`, living on the stage-`t` decision: the pair `(α, β)` stands for the
inequality `θ_{t+1} ≥ α − βᵀ x_t`. -/
abbrev Cut (t : ℕ) := ℝ × (Fin (I.n t) → ℝ)

/-- The height `α − βᵀ x` of the cut `a = (α, β)` at `x`. -/
def Cut.eval {t : ℕ} (a : Cut I t) (x : Fin (I.n t) → ℝ) : ℝ := a.1 - a.2 ⬝ᵥ x

/-- The initial cut (`j = 0`) of the stage-`t` cut list. For `t < T` it is `θ_{t+1} ≥ L t`, a finite
lower bound replacing the paper's trivial cut `θ_{t+1} ≥ −∞`. For `t ≥ T` it is `θ_{T+1} ≥ 0`, which
is exact because `𝒬_{T+1} ≡ 0`; with it, [AP_T] is [LP_T] in the shape of the other stages. -/
def initCut (L : ℕ → ℝ) (t : ℕ) : Cut I t := (if t < I.T then L t else 0, 0)

/-- Validity of the initial cuts: `L t ≤ 𝒬_{t+1}(x_t)` for every stage `1 ≤ t ≤ T − 1` and every
reachable `x_t`. -/
def ValidInit (L : ℕ → ℝ) : Prop :=
  ∀ t, 1 ≤ t → t + 1 ≤ I.T → ∀ x ∈ Reach I t, L t ≤ V I t x

/-- `(y, θ)` is an optimal solution of the approximate problem [AP_t] with cut set `C` and
right-hand side `h` (p. 4): minimize `c_tᵀ y + θ` subject to `A_t y = h`, `y ≥ 0` and
`θ ≥ α − βᵀ y` for every cut `(α, β) ∈ C`. -/
def IsAPOpt (t : ℕ) (C : Set (Cut I t)) (h : Fin (I.m t) → ℝ) (y : Fin (I.n t) → ℝ) (θ : ℝ) :
    Prop :=
  y ∈ Feas I t h ∧ (∀ a ∈ C, a.eval I y ≤ θ) ∧
    ∀ z ∈ Feas I t h, ∀ θ' : ℝ, (∀ a ∈ C, a.eval I z ≤ θ') → I.c t ⬝ᵥ y + θ ≤ I.c t ⬝ᵥ z + θ'

/-- The optimal value of [AP_t] with cut set `C` and right-hand side `h`: the paper's
`C^k_t(x_{t−1}, ω_t)` when `C` is the iteration-`k` cut set and `h = ω_t − B_{t−1} x_{t−1}`, and
`C^k_1` for `t = 1`, `h = b_1`. (A real infimum: meaningful when the feasible region is nonempty
and bounded and `C` is finite and nonempty, as on reachable states under (A4).) -/
noncomputable def apVal (t : ℕ) (C : Set (Cut I t)) (h : Fin (I.m t) → ℝ) : ℝ :=
  sInf {v | ∃ y ∈ Feas I t h, ∃ θ : ℝ, (∀ a ∈ C, a.eval I y ≤ θ) ∧ v = I.c t ⬝ᵥ y + θ}

/-- A dual vector of [AP_t] with a cut list: `π` for the equality constraints and `ρ`, indexed by
the position `j` in the cut list and padded with zeros beyond its length, for the cut constraints. -/
abbrev Dual (t : ℕ) := (Fin (I.m t) → ℝ) × (ℕ → ℝ)

/-- The dual feasible region `𝓗_t` of [AP_t] for the cut list `l` (p. 6):
`A_tᵀ π + Σ_j ρ_j β_j ≤ c_t`, `Σ_j ρ_j = 1`, `ρ ≥ 0`, with `ρ_j = 0` for `j ≥ length l`. The sums
run over the whole list, including the initial cut `j = 0`. -/
def H (t : ℕ) (l : List (Cut I t)) : Set (Dual I t) :=
  {d | (I.A t)ᵀ *ᵥ d.1 + ∑ j : Fin l.length, d.2 j • (l.get j).2 ≤ I.c t ∧
    ∑ j : Fin l.length, d.2 j = 1 ∧ (∀ j, 0 ≤ d.2 j) ∧ ∀ j, l.length ≤ j → d.2 j = 0}

/-- The dual objective `πᵀ h + Σ_j ρ_j α_j` of [AP_t] with cut list `l` and right-hand side `h`. -/
def dualObj (t : ℕ) (l : List (Cut I t)) (h : Fin (I.m t) → ℝ) (d : Dual I t) : ℝ :=
  d.1 ⬝ᵥ h + ∑ j : Fin l.length, d.2 j * (l.get j).1

/-- `d` is an optimal extreme-point dual solution of [AP_t] with cut list `l` and right-hand side
`h` (CCA step 1): an extreme point of `𝓗_t` that maximizes the dual objective over `𝓗_t`. -/
def IsOptExtDual (t : ℕ) (l : List (Cut I t)) (h : Fin (I.m t) → ℝ) (d : Dual I t) : Prop :=
  d ∈ Set.extremePoints ℝ (H I t l) ∧ ∀ d' ∈ H I t l, dualObj I t l h d' ≤ dualObj I t l h d

/-- `d` is a best dual solution in the collection `D` for [AP_t] with cut list `l` and right-hand
side `h` (CCA step 2): it lies in `D` and maximizes the dual objective over `D`. -/
def IsBest (t : ℕ) (l : List (Cut I t)) (D : Set (Dual I t)) (h : Fin (I.m t) → ℝ)
    (d : Dual I t) : Prop :=
  d ∈ D ∧ ∀ d' ∈ D, dualObj I t l h d' ≤ dualObj I t l h d

/-- CCA step 3 (p. 5): the cut on `θ_{s+1}` at stage `s` computed from one chosen dual
`d i = (π^i, ρ^i)` of [AP_{s+1}] per outcome `i` of stage `s + 1`, where `l` is the stage-`(s+1)`
cut list:
`β = Σ_i p_{s+1,i} B_sᵀ π^i` and `α = Σ_i p_{s+1,i} (ω_{s+1,i}ᵀ π^i + Σ_j ρ^i_j α_j)`. -/
def cutOf (s : ℕ) (l : List (Cut I (s + 1))) (d : Fin (I.q (s + 1)) → Dual I (s + 1)) : Cut I s :=
  (∑ i, I.p (s + 1) i * (I.ω (s + 1) i ⬝ᵥ (d i).1 + ∑ j : Fin l.length, (d i).2 j * (l.get j).1),
   ∑ i, I.p (s + 1) i • ((I.B s)ᵀ *ᵥ (d i).1))

end SDDPConv.Doasa


