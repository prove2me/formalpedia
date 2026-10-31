-- Prove2me | Definitions.Def_CapacityGames_Model
-- name    : CapacityGames_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:49.476276+00:00
-- url     : https://prove2.me/theorems/0e8b2373-7141-49eb-83fa-b586df5563a9
-- title:
--   The general capacity game: bids, buyer choices, profits (1)–(4), Assumptions 1–2, consistency (8), the bids $\bar{\mathcal B}$ and Nash equilibrium
-- statement:
--   This module defines the general capacity game of §3 and the objects of §4 used by Theorem 2.
--
--   1. **Game data** (§3, p.7). A finite set $N$ of suppliers; for each $i$ a capacity set $T_i\subseteq\mathbb R_+$, compact, containing $0$, and $\mathbf T=T_1\times\cdots\times T_n$; a demand $D$ with a known probability distribution on a demand set $\mathcal D$; for each $t\in\mathbf T$ a compact set $X(t)\subseteq\mathbf T$ of execution vectors such that $s_i=0$ whenever $t_i=0$; a revenue $V(D,s)$; and costs $E_i(t)$, $C_i(s)$ of supplier $i$, which may depend on the whole vectors and vanish when $t_i=0$, resp. $s_i=0$.
--   2. **Bids** (p.7). A bid of supplier $i$ is a pair $(P_i,R_i)$ of execution and reservation payment functions; it is *allowed* if $P_i(s)=0$ whenever $s_i=0$ and $R_i(t)=0$ whenever $t_i=0$.
--   3. **Choices** (p.8). A buyer choice is $(t,s(\cdot))$ with $t\in\mathbf T$ and $s(D)\in X(t)$ for every demand $D$. Its support is $I(t)=\{i: t_i>0\}$.
--   4. **Profits** (p.8). For bids $\mathcal B$,
--   $$\Pi_{\mathcal B}(t,s)=\mathbb E\Big[V(D,s(D))-\sum_{i\in N}\big(P_i(s(D))+R_i(t)\big)\Big],\quad(1)$$
--   $$\pi_i(t,s)=\mathbb E\big[R_i(t)-E_i(t)+P_i(s(D))-C_i(s(D))\big],\quad(2)$$
--   $$\Pi_{\mathcal C}(t,s)=\mathbb E\Big[V(D,s(D))-\sum_{i\in N}\big(C_i(s(D))+E_i(t)\big)\Big],\quad(3)$$
--   and the optimal values $\Pi^*_{\mathcal C}(S)=\max\{\Pi_{\mathcal C}(t,s): I(t)\subseteq S\}$ (4) and $\Pi^*_{\mathcal B}(S)=\max\{\Pi_{\mathcal B}(t,s): I(t)\subseteq S\}$.
--   5. **The buyer's response** (Assumption 1, p.9). The buyer chooses a maximizer of $\Pi_{\mathcal B}$; among several, one with the largest supply chain profit $\Pi_{\mathcal C}$.
--   6. **Contributing suppliers** (p.10). $N^*(\mathcal C)=\{j:\Pi^*_{\mathcal C}(N)>\Pi^*_{\mathcal C}(N\setminus\{j\})\}$.
--   7. **Assumption 2** (Uniqueness of Support, p.10). All supply chain optimal choices for $N$ have the same support.
--   8. **Consistency** (8), p.11. A family $\{\Delta_i\}$ is consistent with the costs if for every $S\subseteq N$, $\max\{\Pi_{\mathcal C}(t,s)+\sum_{j\in S}\Delta_j(t): I(t)\subseteq S\}=\Pi^*_{\mathcal C}(S)$, attained at a supply chain optimal choice $t^*_S$ for $S$.
--   9. **The bids of Theorem 2** (p.11). $\bar{\mathcal B}$: every supplier bids $\bar P_i=C_i$; supplier $i\in N^*(\mathcal C)$ bids $\bar R_i(t)=E_i(t)+\Pi^*_{\mathcal C}(N)-\Pi^*_{\mathcal C}(N\setminus\{i\})-\Delta_i(t)$ if $t_i>0$ and $0$ if $t_i=0$; every other supplier bids $\bar R_i=E_i$.
--   10. **Nash equilibrium.** A bid set $\mathcal B$ of allowed bids is a Nash equilibrium if the buyer has a tie-broken optimal choice under $\mathcal B$ and no supplier $i$ can raise its profit by replacing its bid with another allowed bid: for every allowed bid $b$ of $i$, every buyer choice $p$ under $\mathcal B$ and every buyer choice $q$ under the deviated bids, $\pi_i(q)\le\pi_i(p)$.
--
--   **Formalization Note** Suppliers form a finite type and vectors are real functions on it. The demand set is a measurable space with a probability measure $\mu$, and $\mathbb E$ is the integral against $\mu$. A choice is feasible for the supply chain when, in addition to $t\in\mathbf T$ and $s(D)\in X(t)$ for all $D$, the functions $D\mapsto V(D,s(D))$ and $D\mapsto C_i(s(D))$ are integrable; it is feasible for bids $\mathcal B$ when moreover every $D\mapsto P_i(s(D))$ is integrable (the paper takes these expectations without stating it). $I(t)$ is $\{i: t_i\ne0\}$, equal to $\{i:t_i>0\}$ on $\mathbf T$. $\Pi^*_{\mathcal C}(S)$ and $\Pi^*_{\mathcal B}(S)$ are suprema. Attainment of every $\Pi^*_{\mathcal C}(S)$, which is what the paper's assumptions (a)–(c) on p.8 are made for, is assumed in (5) and follows from consistency (8) with $\Delta\ge0$ in the other theorems. Allowed bids are all bids vanishing at zero capacity, resp. execution (the paper's lower semicontinuity (c) is not imposed). In (8), "attained at $t^*_S$" is read as "attained at some supply chain optimal choice for $S$". "Nash equilibrium" has no formal definition in the paper; the one above uses the tie-broken buyer response of Assumption 1, and its deviation clause is vacuous for a deviation under which the buyer has no optimal choice.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, §3, pp.6–8 (model, (1)–(4)); §4, p.9 (Assumption 1), p.10 (Assumption 2, N*(C)), p.11 ((8), Theorem 2's bids)

import Mathlib
import Definitions.Def_CapacityGames_SetFunction

open MeasureTheory

namespace CapacityGames

/-- **The data of a general capacity game**, Anderson–Chen–Shao, *Capacity Games with Supply
Function Competition*, arXiv:1905.11084v1, §3, pp.6–8.

* `N` is the (finite) set of suppliers; capacity and execution vectors are `N → ℝ`.
* `Ω` is the demand set `𝒟`, carrying the demand distribution `μ` ("a random demand, with a
  known distribution", p.3); `E[·]` is `∫ · ∂μ`.
* `T i` is the capacity set `T_i` of supplier `i` (p.7).
* `X t` is the set `X(t)` of admissible execution vectors for the capacity vector `t` (p.7).
* `V D s` is the revenue `V(D, s)` of the buyer at demand `D` and execution vector `s` (p.7).
* `E i t` and `C i s` are the capacity (reservation) cost `E_i(t)` and the execution cost
  `C_i(s)` of supplier `i`; both may depend on the whole vector (p.7).

The standing conditions of §3 are collected in `CapacityGame.IsValid`.

**Formalization Note.** The supplier set is a type `N` (later with `Fintype`), standing for
`{1, …, n}`. -/
structure CapacityGame (N : Type*) (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  T : N → Set ℝ
  X : (N → ℝ) → Set (N → ℝ)
  V : Ω → (N → ℝ) → ℝ
  E : N → (N → ℝ) → ℝ
  C : N → (N → ℝ) → ℝ

variable {N : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- The product capacity set `𝐓 = T₁ × ⋯ × Tₙ`, arXiv:1905.11084v1, §3, p.7. -/
def CapacityGame.capSet (G : CapacityGame N Ω) : Set (N → ℝ) := Set.pi Set.univ G.T

/-- **Standing conditions of the capacity game**, arXiv:1905.11084v1, §3, p.7:
1. the demand distribution `μ` is a probability measure;
2. every `T_i ⊆ ℝ₊` is compact and contains `0`;
3. for every `t ∈ 𝐓`, `X(t) ⊆ 𝐓`, `X(t)` is compact, and every `s ∈ X(t)` has `s_i = 0`
   whenever `t_i = 0` ("We require that if t_i = 0 then s_i = 0");
4. `E_i(t) = 0` when `t_i = 0` and `C_i(s) = 0` when `s_i = 0`.

**Formalization Note.** The paper defines `X(t)` only for `t ∈ 𝐓`, so the conditions on `X` are
required only there. -/
structure CapacityGame.IsValid (G : CapacityGame N Ω) : Prop where
  prob : IsProbabilityMeasure G.μ
  T_nonneg : ∀ i, G.T i ⊆ Set.Ici 0
  T_compact : ∀ i, IsCompact (G.T i)
  zero_mem_T : ∀ i, (0 : ℝ) ∈ G.T i
  X_subset : ∀ t ∈ G.capSet, G.X t ⊆ G.capSet
  X_compact : ∀ t ∈ G.capSet, IsCompact (G.X t)
  X_zero : ∀ t ∈ G.capSet, ∀ s ∈ G.X t, ∀ i, t i = 0 → s i = 0
  E_zero : ∀ i t, t i = 0 → G.E i t = 0
  C_zero : ∀ i s, s i = 0 → G.C i s = 0

/-- **A bid** `(P_i(·), R_i(·))` of a supplier, arXiv:1905.11084v1, §3, p.7: `R t` is the
reservation payment for the capacity vector `t`, `P s` the execution payment for the execution
vector `s`. -/
structure Bid (N : Type*) where
  P : (N → ℝ) → ℝ
  R : (N → ℝ) → ℝ

/-- **Allowed bids of supplier `i`**, arXiv:1905.11084v1, §3, p.7: "the feasible bids `A_i` have
the property that for all `R_i(·) ∈ A_i`, `R_i(t) = 0` whenever `t_i = 0` (similarly for
`P_i(·)`)".

**Formalization Note.** `A_i` is taken to be the set of **all** bids with this property; the
paper's further lower-semicontinuity requirement (c), p.8, which only serves the existence of
maxima, is not imposed. -/
def Bid.Allowed (i : N) (b : Bid N) : Prop :=
  (∀ s : N → ℝ, s i = 0 → b.P s = 0) ∧ (∀ t : N → ℝ, t i = 0 → b.R t = 0)

/-- **A buyer choice (policy)** `(t, s(·))`, arXiv:1905.11084v1, §3, p.8: a capacity vector `t`
and an execution rule `s : 𝒟 → (N → ℝ)` giving the execution vector `s(D)` at demand `D`. -/
structure Choice (N : Type*) (Ω : Type*) where
  t : N → ℝ
  s : Ω → N → ℝ

/-- The support `I(t) = {i : t_i > 0}` of a capacity vector, arXiv:1905.11084v1, §3, p.8.

**Formalization Note.** Written `{i : t_i ≠ 0}`; it equals the paper's set on `𝐓`, because
`T_i ⊆ ℝ₊`. -/
noncomputable def support [Fintype N] (t : N → ℝ) : Finset N :=
  Finset.univ.filter fun i => t i ≠ 0

/-- **Feasibility for the supply chain**, arXiv:1905.11084v1, §3, (3)–(4), p.8: `t ∈ 𝐓`,
`s(D) ∈ X(t)` for every demand `D`, and the expectations in (3) exist.

**Formalization Note.** The integrability of `D ↦ V(D, s(D))` and of every `D ↦ C_i(s(D))` is part
of feasibility: the paper takes these expectations without stating it, and a Lean integral of a
non-integrable function is `0`. -/
def SCFeasible (G : CapacityGame N Ω) (p : Choice N Ω) : Prop :=
  p.t ∈ G.capSet ∧ (∀ D, p.s D ∈ G.X p.t) ∧
    Integrable (fun D => G.V D (p.s D)) G.μ ∧ ∀ i, Integrable (fun D => G.C i (p.s D)) G.μ

/-- **Feasibility for the buyer facing bids `B`**, arXiv:1905.11084v1, §3, (1), p.8: feasibility
for the supply chain plus integrability of every execution payment `D ↦ P_i(s(D))`, so that the
expectation in (1) exists. For at-cost execution bids (`P_i = C_i`) it coincides with
`SCFeasible`. -/
def BidFeasible (G : CapacityGame N Ω) (B : N → Bid N) (p : Choice N Ω) : Prop :=
  SCFeasible G p ∧ ∀ i, Integrable (fun D => (B i).P (p.s D)) G.μ

/-- **Buyer profit** (1), arXiv:1905.11084v1, §3, p.8:
`Π_B(t, s) = E[V(D, s(D)) − Σ_{i∈N} (P_i(s(D)) + R_i(t))]`. -/
noncomputable def buyerProfit [Fintype N] (G : CapacityGame N Ω) (B : N → Bid N)
    (p : Choice N Ω) : ℝ :=
  ∫ D, (G.V D (p.s D) - ∑ i, ((B i).P (p.s D) + (B i).R p.t)) ∂G.μ

/-- **Supplier profit** (2), arXiv:1905.11084v1, §3, p.8:
`π_i(t, s) = E[R_i(t) − E_i(t) + P_i(s(D)) − C_i(s(D))]`. -/
noncomputable def supplierProfit (G : CapacityGame N Ω) (B : N → Bid N) (i : N)
    (p : Choice N Ω) : ℝ :=
  ∫ D, ((B i).R p.t - G.E i p.t + (B i).P (p.s D) - G.C i (p.s D)) ∂G.μ

/-- **Supply chain profit** (3), arXiv:1905.11084v1, §3, p.8 (second line):
`Π_C(t, s) = E[V(D, s(D)) − Σ_{i∈N} (C_i(s(D)) + E_i(t))]`; it involves no bids. -/
noncomputable def scProfit [Fintype N] (G : CapacityGame N Ω) (p : Choice N Ω) : ℝ :=
  ∫ D, (G.V D (p.s D) - ∑ i, (G.C i (p.s D) + G.E i p.t)) ∂G.μ

/-- The values `{Π_C(t, s)}` over choices feasible for the supply chain with `I(t) ⊆ S`. -/
def scValues [Fintype N] (G : CapacityGame N Ω) (S : Finset N) : Set ℝ :=
  scProfit G '' {p | SCFeasible G p ∧ support p.t ⊆ S}

/-- **Optimal supply chain profit** (4), arXiv:1905.11084v1, §3, p.8:
`Π*_C(S) = max {Π_C(t, s) : t ∈ 𝐓, s(D) ∈ X(t) for all D ∈ 𝒟, I(t) ⊆ S}`.

**Formalization Note.** Defined as `sSup`. Attainment (`SCAttained`), which is what the paper's
assumptions (a)–(c), p.8, are made for, is assumed in (5) and follows from consistency (8) with
`Δ ≥ 0` in the other theorems. -/
noncomputable def scOptValue [Fintype N] (G : CapacityGame N Ω) (S : Finset N) : ℝ :=
  sSup (scValues G S)

/-- **Attainment of `Π*_C(S)`**, arXiv:1905.11084v1, p.8 ("To ensure that the maxima exist and
are attained, …"): the maximization (4) over `I(t) ⊆ S` has a maximum. -/
def SCAttained [Fintype N] (G : CapacityGame N Ω) (S : Finset N) : Prop :=
  ∃ x, IsGreatest (scValues G S) x

/-- The values `{Π_B(t, s)}` over choices feasible for the buyer facing bids `B` with
`I(t) ⊆ S`. -/
def buyerValues [Fintype N] (G : CapacityGame N Ω) (B : N → Bid N) (S : Finset N) : Set ℝ :=
  buyerProfit G B '' {p | BidFeasible G B p ∧ support p.t ⊆ S}

/-- **Optimal buyer profit** `Π*_B(S)`, arXiv:1905.11084v1, §3, p.8:
`Π*_B(S) = max {Π_B(t, s) : t ∈ 𝐓, s(D) ∈ X(t) for all D ∈ 𝒟, I(t) ⊆ S}`.

**Formalization Note.** Defined as `sSup`; it is not assumed to be attained. -/
noncomputable def buyerOptValue [Fintype N] (G : CapacityGame N Ω) (B : N → Bid N)
    (S : Finset N) : ℝ :=
  sSup (buyerValues G B S)

/-- **The buyer's optimal choices** for (1), arXiv:1905.11084v1, §3, p.8: the choices feasible for
`B` that maximize `Π_B` over all choices feasible for `B`. -/
def BuyerOpt [Fintype N] (G : CapacityGame N Ω) (B : N → Bid N) : Set (Choice N Ω) :=
  {p | BidFeasible G B p ∧ ∀ q, BidFeasible G B q → buyerProfit G B q ≤ buyerProfit G B p}

/-- **The buyer's choice under the tie-breaking rule**, Assumption 1, arXiv:1905.11084v1, §4,
p.9: "In case of multiple optimal solutions, the buyer will select the one that gives the largest
supply chain profit." The optimal choices of `BuyerOpt G B` whose `Π_C` is maximal within
`BuyerOpt G B`. -/
def BuyerChoice [Fintype N] (G : CapacityGame N Ω) (B : N → Bid N) : Set (Choice N Ω) :=
  {p | p ∈ BuyerOpt G B ∧ ∀ q ∈ BuyerOpt G B, scProfit G q ≤ scProfit G p}

/-- **Contributing suppliers** `N*(𝒞) = {j ∈ N : Π*_C(N) > Π*_C(N ∖ {j})}`,
arXiv:1905.11084v1, §4, p.10. -/
noncomputable def contributors [Fintype N] [DecidableEq N] (G : CapacityGame N Ω) : Finset N :=
  contribSet (scOptValue G)

/-- **Assumption 2 (Uniqueness of Support)**, arXiv:1905.11084v1, §4, p.10: "All the supply chain
optimal capacity choices use the same set of suppliers": any two choices feasible for the supply
chain that attain `Π*_C(N)` have the same support. -/
def UniqueSupport [Fintype N] (G : CapacityGame N Ω) : Prop :=
  ∀ p q : Choice N Ω, SCFeasible G p → SCFeasible G q →
    scProfit G p = scOptValue G Finset.univ → scProfit G q = scOptValue G Finset.univ →
      support p.t = support q.t

/-- **Consistency with the costs** (8), arXiv:1905.11084v1, §4, p.11: for every `S ⊆ N`,
`max {Π_C(t, s) + Σ_{j∈S} Δ_j(t) : t ∈ 𝐓, s(D) ∈ X(t) ∀ D, I(t) ⊆ S} = Π*_C(S)` and the
maximization is attained at a supply chain optimal solution `t*_S` of (4). In other words:
1. every choice feasible for the supply chain with `I(t) ⊆ S` has
   `Π_C(t, s) + Σ_{j∈S} Δ_j(t) ≤ Π*_C(S)`;
2. some choice feasible for the supply chain with `I(t) ⊆ S` has `Π_C(t, s) = Π*_C(S)` and
   `Π_C(t, s) + Σ_{j∈S} Δ_j(t) = Π*_C(S)`.

**Formalization Note.** "attained at `t*_S`" is read as "attained at some optimal solution
`t*_S` of (4)". The family `Δ` is indexed by all of `N`, and `Δ_j` is a function on all capacity
vectors (only its values on `𝐓` matter). -/
def Consistent [Fintype N] (G : CapacityGame N Ω) (Δ : N → (N → ℝ) → ℝ) : Prop :=
  ∀ S : Finset N,
    (∀ p : Choice N Ω, SCFeasible G p → support p.t ⊆ S →
        scProfit G p + ∑ j ∈ S, Δ j p.t ≤ scOptValue G S) ∧
    (∃ p : Choice N Ω, SCFeasible G p ∧ support p.t ⊆ S ∧ scProfit G p = scOptValue G S ∧
        scProfit G p + ∑ j ∈ S, Δ j p.t = scOptValue G S)

/-- **The equilibrium bids `B̄` of Theorem 2**, arXiv:1905.11084v1, §4, p.11:
`B̄ = {(C_i(·), R̄_i(·)) : i ∈ N*(𝒞)} ∪ {(C_i(·), E_i(·)) : i ∉ N*(𝒞)}` with
`R̄_i(t) = E_i(t) + Π*_C(N) − Π*_C(N ∖ {i}) − Δ_i(t)` if `t_i > 0` and `R̄_i(t) = 0` if `t_i = 0`.

**Formalization Note.** The case split is on `t_i ≠ 0` (equal to `t_i > 0` on `𝐓`). -/
noncomputable def barBids [Fintype N] [DecidableEq N] (G : CapacityGame N Ω)
    (Δ : N → (N → ℝ) → ℝ) : N → Bid N := fun i =>
  { P := G.C i
    R := fun t =>
      if i ∈ contributors G then
        (if t i ≠ 0 then
          G.E i t + (scOptValue G Finset.univ - scOptValue G (Finset.univ.erase i)) - Δ i t
        else 0)
      else G.E i t }

/-- **Nash equilibrium of the capacity game**, arXiv:1905.11084v1, §4, pp.9–11 (used in
Theorem 2; the paper gives no formal definition). The suppliers are Stackelberg leaders and the
buyer responds with a tie-broken optimal choice (Assumption 1). A bid set `B` is a Nash
equilibrium if
1. every bid `B i` is allowed for supplier `i`;
2. the buyer has a tie-broken optimal choice under `B`;
3. no supplier `i` gains by a unilateral deviation: for every allowed bid `b` of `i`, every
   buyer choice `p` under `B` and every buyer choice `q` under the deviated bids
   `B[i ↦ b]`, `π_i(B[i ↦ b], q) ≤ π_i(B, p)`.

**Formalization Note.** Clause 3 ranges over all buyer choices on both sides. It is vacuous for a
deviation under which the buyer has no optimal choice. -/
def IsNashEquilibrium [Fintype N] [DecidableEq N] (G : CapacityGame N Ω) (B : N → Bid N) :
    Prop :=
  (∀ i, (B i).Allowed i) ∧ (BuyerChoice G B).Nonempty ∧
    ∀ i (b : Bid N), b.Allowed i → ∀ p ∈ BuyerChoice G B,
      ∀ q ∈ BuyerChoice G (Function.update B i b),
        supplierProfit G (Function.update B i b) i q ≤ supplierProfit G B i p

end CapacityGames


