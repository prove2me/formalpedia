-- Prove2me | Definitions.Def_GSCoord_Model
-- name    : GSCoord_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:16.729023+00:00
-- url     : https://prove2.me/theorems/c8a91fe3-6737-4d68-b42e-e8f042978c87
-- title:
--   The serial guaranteed-service programs $\mathbf P$, $\mathbf P_1(S_B)$, $\mathbf P_2(S_B)$ and the merged programs of Appendix II
-- statement:
--   A **serial supply chain** has stages $k=1,\dots,N$, stage $1$ facing the customer and stage $N$ the most upstream. Stage $k$ has a lead time $T_k\in\{0,1,2,\dots\}$ and a holding cost $h_k$ per period per unit; the average demand per period is $\mu$ and the demand bound is a function $D$. Each stage $k$ quotes a guaranteed **service time** $S_k$, an integer, with the exogenous boundary values $S_1=s_1$ (to the customer) and $S_{N+1}=s_{N+1}$ (for the inputs into stage $N$). The **net replenishment time** of stage $k$ is
--
--   $$
--   \tau_k=S_{k+1}+T_k-S_k ,
--   $$
--
--   and stage $k$ costs $h_k\bigl(D(\tau_k)-\tau_k\mu\bigr)$.
--
--   1. The **global program** $\mathbf P$ (6) minimizes $\sum_{k=1}^{N}h_k\bigl(D(\tau_k)-\tau_k\mu\bigr)$ over $S_2,\dots,S_N$ subject to $S_k-S_{k+1}\le T_k$ for $k\in\{1,\dots,N\}$, $S_1=s_1$, $S_{N+1}=s_{N+1}$, and $S_k\ge0$ for $k\in\{2,\dots,N\}$.
--   2. Given a split $N_1$ and a service time $S_B$ between the players, **player 1's program** $\mathbf P_1(S_B)$ (7) minimizes $\sum_{k=1}^{N_1}$ of the same stage costs over $S_2,\dots,S_{N_1}$ subject to $S_k-S_{k+1}\le T_k$ for $k\in\{1,\dots,N_1\}$, $S_1=s_1$, $S_{N_1+1}=S_B$, and $S_k\ge0$ for $k\in\{2,\dots,N_1\}$.
--   3. **Player 2's program** $\mathbf P_2(S_B)$ minimizes $\sum_{k=N_1+1}^{N}$ over $S_{N_1+2},\dots,S_N$ subject to $S_k-S_{k+1}\le T_k$ for $k\in\{N_1+1,\dots,N\}$, $S_{N_1+1}=S_B$, $S_{N+1}=s_{N+1}$, and $S_k\ge0$ for $k\in\{N_1+2,\dots,N\}$.
--   4. The **merged program with fixed split** (second display of Appendix II) minimizes the objective of $\mathbf P$ over $S_2,\dots,S_N$ with the three boundary conditions $S_1=s_1$, $S_{N_1+1}=S_B$, $S_{N+1}=s_{N+1}$, the rows $S_k-S_{k+1}\le T_k$ for $k\in\{1,\dots,N\}$, and $S_k\ge0$ for $k\in\{2,\dots,N_1\}\cup\{N_1+2,\dots,N\}$.
--   5. The **joint program** (third display of Appendix II) minimizes the same objective over $S_2,\dots,S_N$ and $S_B$ together, with the constraints of item 4 and the extra row $S_B\ge0$.
--
--   The optimal value of each program is its infimum, $+\infty$ when it is infeasible. These are the objects of the separation result (8) and of its proof in Appendix II.
--
--   **Formalization Note** Service times are integers, lead times natural numbers cast to integers, and $D:\mathbb Z\to\mathbb R$ is an arbitrary function; the paper's demand bound $D(\tau)=\max_t\sum_{j=t+1}^{t+\tau}d(j)$ of (2) is one instance, and no sign of $h,\mu,s_1,s_{N+1}$ is assumed. Decision vectors are functions $\mathbb N\to\mathbb Z$ read only at $1,\dots,N+1$. Optimal values are infima in `EReal`. $\mathbf P_2(S_B)$ is defined on p.7 in words only; its rows are read by analogy with (7). The non-negativity rows of items 4 and 5 follow the index sets of §2 (free variables only), where the displays of Appendix II print $\{1,\dots,N+1\}$.
-- source:
--   Schoenmeyr, Graves, Coordination of multi-echelon supply chains using the guaranteed service framework, SSRN 3243806, §2, (1) p.5, (5)–(6) p.6, (7) and the definition of P2(S_B) p.7; Appendix II, second and third displays, p.28

import Mathlib

namespace GSCoord

open Finset

/-- A serial guaranteed-service supply chain (Schoenmeyr, Graves, Coordination of multi-echelon
supply chains using the guaranteed service framework, SSRN 3243806, §2 "The global problem",
pp.5–6, (1), (2), (5), (6)).

The stages are `k = 1, …, N`, with stage `1` facing the customer and stage `N` the most upstream.
Stage `k` has the lead time `T k` (a non-negative integer), the holding cost `h k` per period per
unit, the average demand per period is `μ`, the demand bound is `D`, and the exogenous boundary
service times are `S₁ = s₁` (to the customer) and `S_{N+1} = sNplus1` (for the inputs into node `N`).

**Formalization Note.** Stage data are functions on `ℕ` that are only read at `k = 1, …, N`. The
lead times are `ℕ`-valued (p.5: "a non-negative integer denoted as `T_k`") and are cast to `ℤ` in
the arithmetic. The boundary service times are integers (the paper's discrete-time model, p.5).
The demand bound `D : ℤ → ℝ` is an arbitrary function: the paper's `D` of (2),
`D(τ) = max_t Σ_{j=t+1}^{t+τ} d(j)`, is one instance, and no property of `D` (concavity,
monotonicity) and no sign of `h`, `μ`, `s₁`, `s_{N+1}` is assumed. -/
structure SerialSystem where
  /-- The number of stages `N`. -/
  N : ℕ
  /-- The lead time `T_k` of stage `k`. -/
  T : ℕ → ℕ
  /-- The holding cost `h_k` per period per unit at stage `k`. -/
  h : ℕ → ℝ
  /-- The average demand per period `μ`. -/
  μ : ℝ
  /-- The demand bound `D(τ)`. -/
  D : ℤ → ℝ
  /-- The service time `s₁` guaranteed to the customer. -/
  s₁ : ℤ
  /-- The service time `s_{N+1}` for the inputs into node `N`. -/
  sNplus1 : ℤ

/-- The net replenishment time (1) of stage `k` under the service-time vector `S`
(SSRN 3243806, (1), p.5): `τ_k = T_k + S_{k+1} − S_k`, an integer. -/
def netRepl (sys : SerialSystem) (S : ℕ → ℤ) (k : ℕ) : ℤ :=
  S (k + 1) + (sys.T k : ℤ) - S k

/-- The safety-stock holding cost of stage `k` (SSRN 3243806, (5)–(6), p.6):
`h_k (D(S_{k+1} + T_k − S_k) − (S_{k+1} + T_k − S_k) μ)`. -/
noncomputable def stageCost (sys : SerialSystem) (S : ℕ → ℤ) (k : ℕ) : ℝ :=
  sys.h k * (sys.D (netRepl sys S k) - ((netRepl sys S k : ℤ) : ℝ) * sys.μ)

/-- The objective of program **P** (6) (SSRN 3243806, (6), p.6):
`Σ_{k=1}^{N} h_k (D(S_{k+1} + T_k − S_k) − (S_{k+1} + T_k − S_k) μ)`. -/
noncomputable def costP (sys : SerialSystem) (S : ℕ → ℤ) : ℝ :=
  ∑ k ∈ Icc 1 sys.N, stageCost sys S k

/-- The constraints of program **P** (6) (SSRN 3243806, (6), p.6):
`S_k − S_{k+1} ≤ T_k` for `k ∈ {1, …, N}`, `S₁ = s₁`, `S_{N+1} = s_{N+1}`, and `S_k ≥ 0` for
`k ∈ {2, …, N}`. -/
def FeasibleP (sys : SerialSystem) (S : ℕ → ℤ) : Prop :=
  S 1 = sys.s₁ ∧ S (sys.N + 1) = sys.sNplus1 ∧
    (∀ k ∈ Icc 1 sys.N, S k - S (k + 1) ≤ (sys.T k : ℤ)) ∧
    (∀ k ∈ Icc 2 sys.N, 0 ≤ S k)

/-- The optimal value of the global program **P** (6) (SSRN 3243806, (6), p.6), the minimum over
the service times `S₂, …, S_N` of `costP` subject to `FeasibleP`.

**Formalization Note.** The value is an infimum in `EReal`, equal to `⊤` when the program is
infeasible. The decision vector is a function `ℕ → ℤ`; its values off `1, …, N+1` are read by
neither the objective nor the constraints. -/
noncomputable def valP (sys : SerialSystem) : EReal :=
  ⨅ (S : ℕ → ℤ) (_ : FeasibleP sys S), ((costP sys S : ℝ) : EReal)

/-- The objective of player 1's program **P₁(S_B)** (7) (SSRN 3243806, (7), p.7):
`Σ_{k=1}^{N₁} h_k (D(S_{k+1} + T_k − S_k) − (S_{k+1} + T_k − S_k) μ)`. -/
noncomputable def costP1 (sys : SerialSystem) (N₁ : ℕ) (S : ℕ → ℤ) : ℝ :=
  ∑ k ∈ Icc 1 N₁, stageCost sys S k

/-- The constraints of player 1's program **P₁(S_B)** (7) (SSRN 3243806, (7), p.7):
`S_k − S_{k+1} ≤ T_k` for `k ∈ {1, …, N₁}`, `S₁ = s₁`, `S_{N₁+1} = S_B`, and `S_k ≥ 0` for
`k ∈ {2, …, N₁}`. -/
def FeasibleP1 (sys : SerialSystem) (N₁ : ℕ) (SB : ℤ) (S : ℕ → ℤ) : Prop :=
  S 1 = sys.s₁ ∧ S (N₁ + 1) = SB ∧
    (∀ k ∈ Icc 1 N₁, S k - S (k + 1) ≤ (sys.T k : ℤ)) ∧
    (∀ k ∈ Icc 2 N₁, 0 ≤ S k)

/-- The optimal value of player 1's program **P₁(S_B)** (7) (SSRN 3243806, (7), p.7), for a given
service time `S_B` between the players: the minimum over `S₂, …, S_{N₁}`.

**Formalization Note.** `S_B` is a parameter, not a decision variable. The value is an infimum in
`EReal`, `⊤` when the program is infeasible. -/
noncomputable def valP1 (sys : SerialSystem) (N₁ : ℕ) (SB : ℤ) : EReal :=
  ⨅ (S : ℕ → ℤ) (_ : FeasibleP1 sys N₁ SB S), ((costP1 sys N₁ S : ℝ) : EReal)

/-- The objective of player 2's program **P₂(S_B)** (SSRN 3243806, p.7):
`Σ_{k=N₁+1}^{N} h_k (D(S_{k+1} + T_k − S_k) − (S_{k+1} + T_k − S_k) μ)`. -/
noncomputable def costP2 (sys : SerialSystem) (N₁ : ℕ) (S : ℕ → ℤ) : ℝ :=
  ∑ k ∈ Icc (N₁ + 1) sys.N, stageCost sys S k

/-- The constraints of player 2's program **P₂(S_B)** (SSRN 3243806, p.7: "a similar optimization
problem `P₂(S_B)` but defined for stages `N₁+1, N₁+2, …, N`, and with boundary conditions
`S_{N₁+1} = S_B, S_{N+1} = s_{N+1}`"): `S_k − S_{k+1} ≤ T_k` for `k ∈ {N₁+1, …, N}`,
`S_{N₁+1} = S_B`, `S_{N+1} = s_{N+1}`, and `S_k ≥ 0` for `k ∈ {N₁+2, …, N}`.

**Formalization Note.** The page defines `P₂(S_B)` in words only; the constraint rows and the
non-negativity of the free variables `S_{N₁+2}, …, S_N` are read by analogy with (7). -/
def FeasibleP2 (sys : SerialSystem) (N₁ : ℕ) (SB : ℤ) (S : ℕ → ℤ) : Prop :=
  S (N₁ + 1) = SB ∧ S (sys.N + 1) = sys.sNplus1 ∧
    (∀ k ∈ Icc (N₁ + 1) sys.N, S k - S (k + 1) ≤ (sys.T k : ℤ)) ∧
    (∀ k ∈ Icc (N₁ + 2) sys.N, 0 ≤ S k)

/-- The optimal value of player 2's program **P₂(S_B)** (SSRN 3243806, p.7), for a given service
time `S_B` between the players: the minimum over `S_{N₁+2}, …, S_N`.

**Formalization Note.** `S_B` is a parameter, not a decision variable. The value is an infimum in
`EReal`, `⊤` when the program is infeasible. -/
noncomputable def valP2 (sys : SerialSystem) (N₁ : ℕ) (SB : ℤ) : EReal :=
  ⨅ (S : ℕ → ℤ) (_ : FeasibleP2 sys N₁ SB S), ((costP2 sys N₁ S : ℝ) : EReal)

/-- The constraints of the merged program with a fixed split, the second display of Appendix II
(SSRN 3243806, Appendix II, p.28, between steps (A) and (B)): `S_k − S_{k+1} ≤ T_k` for
`k ∈ {1, …, N}`, `S₁ = s₁`, `S_{N₁+1} = S_B`, `S_{N+1} = s_{N+1}`, and non-negativity.

**Formalization Note.** Non-negativity is imposed on `k ∈ {2, …, N₁} ∪ {N₁+2, …, N}`, the union of
the free variables of `P₁(S_B)` (7) and `P₂(S_B)` as defined in §2. The display on p.28 prints
`k ∈ {1, …, N+1}`, which would also constrain the fixed values `s₁`, `S_B`, `s_{N+1}`; the §2
index sets are used so that this program is exactly the one obtained by joining `P₁(S_B)` and
`P₂(S_B)`. -/
def FeasibleFix (sys : SerialSystem) (N₁ : ℕ) (SB : ℤ) (S : ℕ → ℤ) : Prop :=
  S 1 = sys.s₁ ∧ S (N₁ + 1) = SB ∧ S (sys.N + 1) = sys.sNplus1 ∧
    (∀ k ∈ Icc 1 sys.N, S k - S (k + 1) ≤ (sys.T k : ℤ)) ∧
    (∀ k ∈ Icc 2 N₁, 0 ≤ S k) ∧ (∀ k ∈ Icc (N₁ + 2) sys.N, 0 ≤ S k)

/-- The optimal value of the merged program with a fixed split `S_B`, the second display of
Appendix II (SSRN 3243806, Appendix II, p.28): the minimum over `S₂, …, S_N` of the objective
`Σ_{k=1}^{N}` of **P** subject to `FeasibleFix`. `⊤` when infeasible. -/
noncomputable def valFix (sys : SerialSystem) (N₁ : ℕ) (SB : ℤ) : EReal :=
  ⨅ (S : ℕ → ℤ) (_ : FeasibleFix sys N₁ SB S), ((costP sys S : ℝ) : EReal)

/-- The optimal value of the single joint program, the third display of Appendix II
(SSRN 3243806, Appendix II, p.28, between steps (B) and (C)): the minimum over the decision
variables `S₂, …, S_N; S_B` jointly of the objective of **P**, subject to `FeasibleFix` with the
split value `S_B` and the additional row `S_B ≥ 0`. `⊤` when infeasible.

**Formalization Note.** The pair `(S, S_B)` is one decision variable of a single infimum, as on the
page; non-negativity follows the §2 index sets as in `FeasibleFix`. -/
noncomputable def valJoint (sys : SerialSystem) (N₁ : ℕ) : EReal :=
  ⨅ (p : (ℕ → ℤ) × ℤ) (_ : FeasibleFix sys N₁ p.2 p.1 ∧ 0 ≤ p.2),
    ((costP sys p.1 : ℝ) : EReal)

end GSCoord


