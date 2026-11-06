-- Prove2me | Definitions.Def_FullPathSCC_Model
-- name    : FullPathSCC_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:36.557355+00:00
-- url     : https://prove2.me/theorems/72ea901a-9f51-423d-8e8f-8f70e53a9ff8
-- title:
--   §3.1 — the climate–economy model with risk-sensitive preferences, its standing assumptions, the state box and admissible actions
-- statement:
--   The **general model with risk-sensitive preferences** of §3.1. The world capital stock is $K_t\in[0,\bar K]$ and the temperature rise is $T_t\in[0,\bar T]$, with $\bar K,\bar T>0$; the disaster state $\vartheta_t$ lies in a finite set $\mathcal S$. At time $t$ the planner chooses consumption $C_t\in[0,K_t]$ and abatement $\mu_t\in[0,1]$, and the state moves to
--
--   $$
--   K_{t+1}=g_{K,t}(K_t,T_t,\vartheta_t,C_t,\mu_t),\qquad T_{t+1}=g_{T,t}(K_t,T_t,\mu_t),
--   $$
--
--   while the disaster state moves from $\vartheta_t$ to $\hat\vartheta$ with probability $p_{\vartheta_t,\hat\vartheta}(T_t)$. The planner receives $U_t(C_t)$ at times $t=0,\dots,N-1$ and the terminal value $h$ at time $N$; $k>0$ is the robustness parameter, $0<\beta<1$ the discount factor and $k_t=k\beta^t$.
--
--   The **standing assumptions** are: $\bar K,\bar T,k>0$ and $0<\beta<1$; for every $T\in[0,\bar T]$, $(p_{\vartheta,\hat\vartheta}(T))_{\hat\vartheta}$ is a probability vector, and each $p_{\vartheta,\hat\vartheta}$ is continuous on $[0,\bar T]$; for $t<N$, $U_t$ is continuous on $[0,\bar K]$, $g_{K,t}(\cdot,\cdot,\vartheta,\cdot,\cdot)$ is continuous on $D_{K,t}=\{(K,T,C,\mu):K\in[0,\bar K],\,T\in[0,\bar T],\,C\in[0,K],\,\mu\in[0,1]\}$ with values in $[0,\bar K]$, and $g_{T,t}$ is continuous on $D_{T,t}=[0,\bar K]\times[0,\bar T]\times[0,1]$ with values in $[0,\bar T]$; $h(\cdot,\cdot,\vartheta)$ is continuous on $[0,\bar K]\times[0,\bar T]$.
--
--   The definition also fixes the state box $[0,\bar K]\times[0,\bar T]\times\mathcal S$, the admissible actions $(C,\mu)\in[0,K]\times[0,1]$ at a state $(K,T,\vartheta)$, the risk parameter $k_t=k\beta^t$, and the successor state $(g_{K,t}(K,T,\vartheta,C,\mu),g_{T,t}(K,T,\mu),j)$ when the next disaster state is $j$.
--
--   Every result of the mission is stated for this model.
--
--   **Formalization Note** The paper assumes $C^1$ data and $\mathcal S=\{1,2,3,4\}$; here the data are continuous and $\mathcal S$ is any finite nonempty type. The paper's hypotheses that $U_t$ is strictly increasing, nonnegative and vanishes at $0$ are not assumed. The terminal value $h$ is a function of the whole terminal state; the paper's $h:[0,\bar K]\to\mathbb R$ is the case $h(K,T,\vartheta)=h(K)$. The requirement that $g_{K,t}$ and $g_{T,t}$ map into $[0,\bar K]$ and $[0,\bar T]$ encodes §3.1's $K_t\in[0,\bar K]$, $T_t\in[0,\bar T]$ at every $t$.
-- source:
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, §3.1, p.7591 (definitions before (7), (7), (8)); §2, p.7587 ($0<\beta<1$)

import Mathlib

namespace FullPathSCC

/-- A state `(K, T, ϑ)` of the climate–economy model: world capital stock `K`, temperature rise
`T` and disaster state `ϑ` (Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We
Wish for Full-Path Robustness, Management Science 69(12) (2023), §3.1, p.7591). -/
abbrev State (S : Type*) := ℝ × ℝ × S

/-- The data of the general climate–economy model with risk-sensitive preferences
(Management Science 69(12) (2023), §3.1, p.7591, and the discount factor of §2, p.7587):

* `Kbar`, `Tbar` — the bounds `K̄`, `T̄` of the capital and temperature intervals;
* `k` — the robustness parameter; `β` — the per-period discount factor; `N` — the horizon;
* `p ϑ ϑ̂ T` — the transition probability `p_{ϑ,ϑ̂}(T)` of the disaster state at temperature `T`;
* `U t C` — the utility `U_t(C)` of consumption `C` at time `t`;
* `gK t K T ϑ C μ` — the capital accumulation model `g_{K,t}`;
* `gT t K T μ` — the climate model `g_{T,t}`;
* `h K T ϑ` — the terminal value `V_N = h`.

The standing assumptions of §3.1 are the separate predicate `Model.Standing`.

**Formalization Note** The disaster states form a type `S` (paper: `𝒮 = {1,2,3,4}`); theorems
take it finite and nonempty. The terminal value `h` is a function of the whole terminal state
`(K, T, ϑ)`; the paper's `h : [0,K̄] → ℝ` is the instance `h K T ϑ = h K`. All maps are total
functions on `ℝ`; only their values on the domains of §3.1 enter any statement. -/
structure Model (S : Type*) where
  /-- The capital bound `K̄`. -/
  Kbar : ℝ
  /-- The temperature bound `T̄`. -/
  Tbar : ℝ
  /-- The robustness parameter `k`. -/
  k : ℝ
  /-- The discount factor `β`. -/
  β : ℝ
  /-- The horizon `N`. -/
  N : ℕ
  /-- The transition probabilities `p_{ϑ,ϑ̂}(T)`. -/
  p : S → S → ℝ → ℝ
  /-- The utilities `U_t(C)`. -/
  U : ℕ → ℝ → ℝ
  /-- The capital accumulation model `g_{K,t}(K, T, ϑ, C, μ)`. -/
  gK : ℕ → ℝ → ℝ → S → ℝ → ℝ → ℝ
  /-- The climate model `g_{T,t}(K, T, μ)`. -/
  gT : ℕ → ℝ → ℝ → ℝ → ℝ
  /-- The terminal value `h(K, T, ϑ)`. -/
  h : ℝ → ℝ → S → ℝ

/-- An action `a = (C, μ)` is admissible at the state `x = (K, T, ϑ)` when `C ∈ [0, K]` and
`μ ∈ [0, 1]` (Management Science 69(12) (2023), §3.1, p.7591: "C_t ∈ [0, K_t] is world
consumption … and μ_t ∈ [0, 1] is the abatement rate"). -/
def AdmissibleAction {S : Type*} (x : State S) (a : ℝ × ℝ) : Prop :=
  a.1 ∈ Set.Icc 0 x.1 ∧ a.2 ∈ Set.Icc 0 1

namespace Model

variable {S : Type*}

/-- The state lies in the box `[0, K̄] × [0, T̄] × 𝒮` of §3.1 (Management Science 69(12) (2023),
p.7591: `K_t ∈ [0, K̄]`, `T_t ∈ [0, T̄]`). -/
def InBox (M : Model S) (x : State S) : Prop :=
  x.1 ∈ Set.Icc 0 M.Kbar ∧ x.2.1 ∈ Set.Icc 0 M.Tbar

/-- The time-`t` risk parameter `k_t = k β^t` (Management Science 69(12) (2023), §3.1, p.7591:
"we denote k_t ≡ kβ^t, and hence, k_0 = k"). -/
def kt (M : Model S) (t : ℕ) : ℝ := M.k * M.β ^ t

/-- The successor state of (8) when the disaster state moves to `j`:
`(g_{K,t}(K, T, ϑ, C, μ), g_{T,t}(K, T, μ), j)` (Management Science 69(12) (2023), (7) and (8),
p.7591). -/
def next (M : Model S) (t : ℕ) (x : State S) (a : ℝ × ℝ) (j : S) : State S :=
  (M.gK t x.1 x.2.1 x.2.2 a.1 a.2, M.gT t x.1 x.2.1 a.2, j)

/-- The standing assumptions of §3.1 (Management Science 69(12) (2023), p.7591; `0 < β < 1` from
§2, p.7587):

* `K̄ > 0`, `T̄ > 0`, `k > 0`, `0 < β < 1`;
* `p_{ϑ,·}(T)` is a probability vector for every `T ∈ [0, T̄]`, and each `p_{ϑ,ϑ̂}` is continuous
  on `[0, T̄]`;
* for `t < N`, `U_t` is continuous on `[0, K̄]`;
* for `t < N` and each `ϑ`, `g_{K,t}(·, ·, ϑ, ·, ·)` is continuous on
  `D_{K,t} = {(K, T, C, μ) : K ∈ [0, K̄], T ∈ [0, T̄], C ∈ [0, K], μ ∈ [0, 1]}` and maps it into
  `[0, K̄]`;
* for `t < N`, `g_{T,t}` is continuous on `D_{T,t} = [0, K̄] × [0, T̄] × [0, 1]` and maps it into
  `[0, T̄]`;
* for each `ϑ`, `h(·, ·, ϑ)` is continuous on `[0, K̄] × [0, T̄]`.

**Formalization Note** The paper assumes `C¹` data; continuity is assumed instead. The
paper's hypotheses that `U_t` is strictly increasing, nonnegative and `U_t(0) = 0` are not
assumed. "Transition probability" is encoded as nonnegative entries with row sums `1`. The
paper places `K_t ∈ [0, K̄]` and `T_t ∈ [0, T̄]` at every time; this is encoded by asking `g_{K,t}`
and `g_{T,t}` to map their domains into these intervals (the reading under which `V_{t+1}` in (8)
and `V_N = h` are evaluated on their domain). -/
structure Standing [Fintype S] (M : Model S) : Prop where
  Kbar_pos : 0 < M.Kbar
  Tbar_pos : 0 < M.Tbar
  k_pos : 0 < M.k
  β_pos : 0 < M.β
  β_lt_one : M.β < 1
  p_nonneg : ∀ i j : S, ∀ T ∈ Set.Icc 0 M.Tbar, 0 ≤ M.p i j T
  p_sum : ∀ i : S, ∀ T ∈ Set.Icc 0 M.Tbar, ∑ j : S, M.p i j T = 1
  p_cont : ∀ i j : S, ContinuousOn (M.p i j) (Set.Icc 0 M.Tbar)
  U_cont : ∀ t < M.N, ContinuousOn (M.U t) (Set.Icc 0 M.Kbar)
  gK_cont : ∀ t < M.N, ∀ ϑ : S,
    ContinuousOn (fun z : ℝ × ℝ × ℝ × ℝ => M.gK t z.1 z.2.1 ϑ z.2.2.1 z.2.2.2)
      {z | z.1 ∈ Set.Icc 0 M.Kbar ∧ z.2.1 ∈ Set.Icc 0 M.Tbar ∧ z.2.2.1 ∈ Set.Icc 0 z.1 ∧
        z.2.2.2 ∈ Set.Icc (0 : ℝ) 1}
  gK_mem : ∀ t < M.N, ∀ (K T : ℝ) (ϑ : S) (C μ : ℝ), K ∈ Set.Icc 0 M.Kbar →
    T ∈ Set.Icc 0 M.Tbar → C ∈ Set.Icc 0 K → μ ∈ Set.Icc (0 : ℝ) 1 →
    M.gK t K T ϑ C μ ∈ Set.Icc 0 M.Kbar
  gT_cont : ∀ t < M.N,
    ContinuousOn (fun z : ℝ × ℝ × ℝ => M.gT t z.1 z.2.1 z.2.2)
      (Set.Icc 0 M.Kbar ×ˢ Set.Icc 0 M.Tbar ×ˢ Set.Icc (0 : ℝ) 1)
  gT_mem : ∀ t < M.N, ∀ K T μ : ℝ, K ∈ Set.Icc 0 M.Kbar → T ∈ Set.Icc 0 M.Tbar →
    μ ∈ Set.Icc (0 : ℝ) 1 → M.gT t K T μ ∈ Set.Icc 0 M.Tbar
  h_cont : ∀ ϑ : S,
    ContinuousOn (fun z : ℝ × ℝ => M.h z.1 z.2 ϑ) (Set.Icc 0 M.Kbar ×ˢ Set.Icc 0 M.Tbar)

end Model

end FullPathSCC


