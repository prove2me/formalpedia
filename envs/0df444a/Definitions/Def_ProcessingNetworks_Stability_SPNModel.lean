-- Prove2me | Definitions.Def_ProcessingNetworks_Stability_SPNModel
-- name    : ProcessingNetworks_Stability_SPNModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:16:05.181627+00:00
-- url     : https://prove2.me/theorems/3dd959c7-ef57-4b62-9f26-90d3a9ea2d82
-- title:
--   Chapter 2 — the stochastic processing network model (system relations (2.7)-(2.12), (2.31)-(2.34), (6.51); basic and relaxed formulations)
-- statement:
--   This item records the **stochastic processing network model of Chapter 2** — the object every
--   later theorem of the book ("if the SPN is stable, then …") is about — as the sample-path system
--   relations of Sections 2.1–2.5.
--
--   **Model data (Section 2.1).** `SPNData` bundles the $K \times J$ server requirements matrix $A$
--   and the $I \times J$ material requirements matrix $B$, both **binary**, with no column of either
--   consisting entirely of zeros, and the strictly positive server-pool capacities $b \in \mathbb{R}^K$.
--
--   **Processing variables in the order of $\mathcal{L}_j$ (Eqs. (2.1)–(2.3)).** For activity $j$
--   the index set $\mathcal{L}_j = \mathcal{L}_j^0 \cup \{1, 2, \dots\}$ lists the $N_j(0)$ initial
--   processing variables (IP pairs: residual service time and output vector of a service already open
--   at time $0$, `Psi j k` for $k < N_j(0)$) before the post-time-zero pairs $(v_j(\ell), \varphi_j(\ell))$.
--   `delayedTerm` is the $k$-th pair in that order; `delayedWalk` is the delayed random walk
--   $V_j(n)$ of Section 2.5 / Eq. (6.47), the sum of the first $n$ service times in that order;
--   `cumulativeOutput` is $\Phi^j(n)$ of Eq. (2.8), the sum of the first $n$ output vectors in that
--   order; `delayedMax` is $\max_{-N_j(0) < \ell \le n - N_j(0)} v_j(\ell)$, the largest of the first
--   $n$ service times (the maximum appearing in (6.51)).
--
--   **System relations shared by both formulations (Section 2.5).** `SPNRelations` states, for the
--   network processes of Section 2.1 — cumulative service starts $S$ (right-continuous, nondecreasing,
--   $S(0) = 0$, Eq. (2.4)), completions $F$, open services $N$, departures $D$, buffer contents $Z$,
--   cumulative service effort $T$ — the equations
--   $$
--   N(t) = N(0) + S(t) - F(t) \ (2.7), \qquad D(t) = B F(t) \ (2.9), \qquad
--   Z(t) = Z(0) + E(t) + \sum_j \Phi^j(F_j(t)) - D(t) \ (2.10),
--   $$
--   the item availability constraint $B N(t) \le Z(t)$ (2.12), $T$ nondecreasing with $T(0) = 0$
--   (2.31), the capacity bound $A(T(t) - T(s)) \le b(t-s)$ (2.32), the bound $N(t) \le \kappa e$ on
--   service counts (2.34), and the key relationship (6.51) between effort, completions and the delayed
--   random walk,
--   $$
--   V_j(F_j(t)) - N_j(t) \max_{-N_j(0) < \ell \le F_j(t) + N_j(t)} v_j(\ell) \;\le\; T_j(t) \;\le\; V_j(F_j(t) + N_j(t)),
--   $$
--   which the book establishes for both formulations.
--
--   **Basic model (Section 2.3).** `IsBasicSPN` adds $T_j(t) = \int_0^t N_j(u)\,du$ (2.22), the
--   capacity constraint $A N(t) \le b$ (2.11), and the completion rule: the $\ell$-th type-$j$
--   service initiated after time zero, started at $\tau_j(\ell) = \inf\{s \ge 0 : S_j(s) \ge \ell\}$
--   (2.6), completes at $\tau_j(\ell) + v_j(\ell)$, and an initial service with residual time $r$
--   completes at time $r$; $F_j(t)$ counts these completions.
--
--   **Relaxed model (Section 2.4).** `IsRelaxedSPN` adds a nonnegative service-rate vector
--   $\beta(t)$ with $A\beta(t) \le b$ (2.27), effort directed only to an open service, at most one
--   open service per type, $T_j(t) = \int_0^t \beta_j(u)\,du$ (2.28), and the completion rule
--   $F_j(t) = \sup\{\ell \ge 1 : V_j(\ell) \le T_j(t)\}$ (2.30), with the supremum of the empty
--   set equal to $0$ by the book's convention.
--
--   **Formalization note.** $\Phi^j$ and $V_j$ are taken over $\mathcal{L}_j$ in its natural order
--   (initial services first), which is the reading under which (2.10) accounts for the outputs of
--   services open at time zero and matches the delayed random walk of (6.47). $D$, $F$, $N$, $S$,
--   $Z$ are integer-valued as in the book; the equations (2.9)–(2.10) are stated after casting to
--   $\mathbb{R}$ (they involve the real matrix $B$). The relaxed model's $\beta$ is only required to
--   be a function of time and the sample point here; theorems that need the simply structured
--   policy's Markov property (Remark 5.3) state it separately.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, pp. 27-38, Sections 2.1-2.5 (Eqs. (2.1)-(2.12), (2.22)-(2.34)) and p. 119, Eq. (6.51)

import Mathlib

namespace ProcessingNetworks.Stability

open MeasureTheory

/-- Model data of a stochastic processing network (Section 2.1): the `K × J` server requirements
matrix `A` and the `I × J` material requirements matrix `B`, both binary, with no column of either
consisting entirely of zeros ("to avoid trivialities"), and the `K`-vector `b` of server-pool
capacities, strictly positive. -/
structure SPNData (I J K : ℕ) where
  A : Matrix (Fin K) (Fin J) ℝ
  B : Matrix (Fin I) (Fin J) ℝ
  b : Fin K → ℝ
  A_binary : ∀ k j, A k j = 0 ∨ A k j = 1
  B_binary : ∀ i j, B i j = 0 ∨ B i j = 1
  A_col_nonzero : ∀ j, ∃ k, A k j = 1
  B_col_nonzero : ∀ j, ∃ i, B i j = 1
  b_pos : ∀ k, 0 < b k

/-- The `k`-th term of the type-`j` processing-variable sequence in the order of the index set
`L_j = L_j^0 ∪ {1, 2, …}` of (2.1)–(2.2): the `N0 j` initial processing variables (IP pairs, the
residual service time and output vector of the services already open at time `0`, indexed by
`k < N0 j`) come first, followed by the post-time-zero pairs `(v j ℓ, φ j ℓ)` (`ℓ = 0, 1, …`
standing for the book's `ℓ = 1, 2, …`). -/
def delayedTerm {Ω : Type*} {I J : ℕ} (N0 : Fin J → ℕ)
    (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) (v : Fin J → ℕ → Ω → ℝ)
    (φ : Fin J → ℕ → Ω → Fin I → ℕ) (j : Fin J) (k : ℕ) (ω : Ω) : ℝ × (Fin I → ℕ) :=
  if k < N0 j then Psi j k ω else (v j (k - N0 j) ω, φ j (k - N0 j) ω)

/-- The delayed random walk `V_j(n)` of Section 2.5 / Eq. (6.47): the sum of the first `n` type-`j`
service times in the order of `L_j` (residual times of the initial services first). -/
noncomputable def delayedWalk {Ω : Type*} {I J : ℕ} (N0 : Fin J → ℕ)
    (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) (v : Fin J → ℕ → Ω → ℝ)
    (φ : Fin J → ℕ → Ω → Fin I → ℕ) (j : Fin J) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (delayedTerm N0 Psi v φ j k ω).1

/-- The cumulative output flow `Φ^j(n)` of Eq. (2.8), taken over the index set `L_j` in its
natural order (initial services first, as for `delayedWalk`): the sum of the output vectors of
the first `n` type-`j` services in that order. -/
def cumulativeOutput {Ω : Type*} {I J : ℕ} (N0 : Fin J → ℕ)
    (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) (v : Fin J → ℕ → Ω → ℝ)
    (φ : Fin J → ℕ → Ω → Fin I → ℕ) (j : Fin J) (n : ℕ) (ω : Ω) (i : Fin I) : ℕ :=
  ∑ k ∈ Finset.range n, (delayedTerm N0 Psi v φ j k ω).2 i

/-- The largest of the first `n` type-`j` service times in the order of `L_j` (the maximum
`max_{-N_j(0) < ℓ ≤ n - N_j(0)} v_j(ℓ)` appearing in (6.51)); `0` when `n = 0`. -/
noncomputable def delayedMax {Ω : Type*} {I J : ℕ} (N0 : Fin J → ℕ)
    (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) (v : Fin J → ℕ → Ω → ℝ)
    (φ : Fin J → ℕ → Ω → Fin I → ℕ) (j : Fin J) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ k ∈ Finset.range n, (delayedTerm N0 Psi v φ j k ω).1

/-- The system relations shared by the basic (Section 2.3) and relaxed (Section 2.4) SPN
formulations, as recapitulated in Section 2.5, for the network processes of Section 2.1 built
from the primitive stochastic elements: the external arrival process `E`, the post-time-zero
processing variables `(v, φ)`, the `N0 j` initial processing variables `Psi j k` (`k < N0 j`) of
Eq. (2.3), and the initial buffer contents `Z0`. `S` counts cumulative service starts, `F`
completions, `N` open services, `D` departures, `Z` buffer contents, `T` cumulative service
effort. Fields: (2.4)–(2.7) (`S` right-continuous, nondecreasing, `S(0) = 0`, and
`N(t) = N(0) + S(t) - F(t)`), (2.9), (2.10) (with `Φ^j` taken over `L_j` in its natural order),
(2.12), (2.31), (2.32), the bound (2.34) on service counts, and the key relationship (6.51)
between cumulative effort, completions and the delayed random walk, which holds for both
formulations. -/
structure SPNRelations {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ} (dat : SPNData I J K)
    (E : Fin I → ℝ → Ω → ℕ) (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ)
    (N0 : Fin J → ℕ) (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) (Z0 : Fin I → ℕ)
    (S F N : ℝ → Ω → Fin J → ℕ) (T : ℝ → Ω → Fin J → ℝ) (D Z : ℝ → Ω → Fin I → ℕ) :
    Prop where
  N_init : ∀ ω, N 0 ω = N0
  Z_init : ∀ ω, Z 0 ω = Z0
  S_init : ∀ ω, S 0 ω = 0
  S_mono : ∀ ω j, Monotone fun t => S t ω j
  S_rightCont : ∀ ω j (t : ℝ), 0 ≤ t → ∃ ε > 0, ∀ s ∈ Set.Ico t (t + ε), S s ω j = S t ω j
  F_init : ∀ ω, F 0 ω = 0
  F_mono : ∀ ω j, Monotone fun t => F t ω j
  service_counts : ∀ (t : ℝ) ω j, 0 ≤ t → N t ω j + F t ω j = N0 j + S t ω j
  departures : ∀ (t : ℝ) ω i, 0 ≤ t → (D t ω i : ℝ) = ∑ j, dat.B i j * F t ω j
  buffer_contents : ∀ (t : ℝ) ω i, 0 ≤ t →
    (Z t ω i : ℝ) = Z0 i + E i t ω +
      ∑ j, (cumulativeOutput N0 Psi v φ j (F t ω j) ω i : ℝ) - D t ω i
  availability : ∀ (t : ℝ) ω i, 0 ≤ t → ∑ j, dat.B i j * (N t ω j : ℝ) ≤ Z t ω i
  T_init : ∀ ω, T 0 ω = 0
  T_mono : ∀ ω j, Monotone fun t => T t ω j
  T_capacity : ∀ ω (s t : ℝ) k, 0 ≤ s → s < t →
    ∑ j, dat.A k j * (T t ω j - T s ω j) ≤ dat.b k * (t - s)
  service_bound : ∃ κ : ℕ, ∀ (t : ℝ) ω j, N t ω j ≤ κ
  effort_completions : ∀ (t : ℝ) ω j, 0 ≤ t →
    delayedWalk N0 Psi v φ j (F t ω j) ω -
        N t ω j * delayedMax N0 Psi v φ j (F t ω j + N t ω j) ω ≤ T t ω j ∧
      T t ω j ≤ delayedWalk N0 Psi v φ j (F t ω j + N t ω j) ω

/-- The basic SPN model of Section 2.3, on top of the shared relations: every open service
proceeds at full speed, so cumulative effort is `T_j(t) = ∫₀ᵗ N_j(u) du` (2.22); the capacity
constraint is `A N(t) ≤ b` (2.11); and the `ℓ`-th type-`j` service initiated after time zero
(`ℓ = 0, 1, …`), started at `τ_j(ℓ+1) = inf{s ≥ 0 : S_j(s) ≥ ℓ+1}` (2.6), is completed at
`τ_j(ℓ+1) + v_j(ℓ)`, while an initial service with residual time `r` is completed at `r`; `F`
counts these completions. -/
structure IsBasicSPN {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ} (dat : SPNData I J K)
    (E : Fin I → ℝ → Ω → ℕ) (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ)
    (N0 : Fin J → ℕ) (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) (Z0 : Fin I → ℕ)
    (S F N : ℝ → Ω → Fin J → ℕ) (T : ℝ → Ω → Fin J → ℝ) (D Z : ℝ → Ω → Fin I → ℕ) :
    Prop extends SPNRelations dat E v φ N0 Psi Z0 S F N T D Z where
  effort : ∀ (t : ℝ) ω j, 0 ≤ t → T t ω j = ∫ u in (0 : ℝ)..t, (N u ω j : ℝ)
  capacity : ∀ (t : ℝ) ω k, 0 ≤ t → ∑ j, dat.A k j * (N t ω j : ℝ) ≤ dat.b k
  completions : ∀ (t : ℝ) ω j, 0 ≤ t →
    F t ω j = ((Finset.range (N0 j)).filter fun k => (Psi j k ω).1 ≤ t).card +
      ((Finset.range (S t ω j)).filter fun ℓ =>
        sInf {s : ℝ | 0 ≤ s ∧ ℓ + 1 ≤ S s ω j} + v j ℓ ω ≤ t).card

/-- The relaxed SPN model of Section 2.4 under a simply structured control policy, on top of the
shared relations: at most one service of each type is open at any time; a nonnegative service
rate (effort level) vector `β(t)` with `A β(t) ≤ b` (2.27) is applied, effort is directed only to
an open service, `T_j(t) = ∫₀ᵗ β_j(u) du` (2.28), and the `ℓ`-th type-`j` service concludes when
`T_j` first reaches `V_j(ℓ)`, so `F_j(t) = sup{ℓ ≥ 1 : V_j(ℓ) ≤ T_j(t)}` (2.30), with the
supremum of an empty set equal to `0`. -/
structure IsRelaxedSPN {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ} (dat : SPNData I J K)
    (E : Fin I → ℝ → Ω → ℕ) (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ)
    (N0 : Fin J → ℕ) (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) (Z0 : Fin I → ℕ)
    (S F N : ℝ → Ω → Fin J → ℕ) (T : ℝ → Ω → Fin J → ℝ) (D Z : ℝ → Ω → Fin I → ℕ)
    (β : ℝ → Ω → Fin J → ℝ) : Prop extends SPNRelations dat E v φ N0 Psi Z0 S F N T D Z where
  at_most_one : ∀ (t : ℝ) ω j, N t ω j ≤ 1
  rate_nonneg : ∀ (t : ℝ) ω j, 0 ≤ β t ω j
  rate_capacity : ∀ (t : ℝ) ω k, 0 ≤ t → ∑ j, dat.A k j * β t ω j ≤ dat.b k
  rate_open : ∀ (t : ℝ) ω j, 0 ≤ t → 0 < β t ω j → N t ω j = 1
  effort : ∀ (t : ℝ) ω j, 0 ≤ t → T t ω j = ∫ u in (0 : ℝ)..t, β u ω j
  completions : ∀ (t : ℝ) ω j, 0 ≤ t →
    F t ω j = sSup {ℓ : ℕ | 1 ≤ ℓ ∧ delayedWalk N0 Psi v φ j ℓ ω ≤ T t ω j}

end ProcessingNetworks.Stability


