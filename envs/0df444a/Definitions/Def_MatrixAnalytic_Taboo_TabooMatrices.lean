-- Prove2me | Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices
-- name    : MatrixAnalytic_Taboo_TabooMatrices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:55.702205+00:00
-- url     : https://prove2.me/theorems/e83fcdf2-74f3-446f-b4f0-83a971d1cfad
-- title:
--   Taboo probabilities and expected-visit matrices — $N_D$, ${}_TP_{ij}(k)$, ${}_TR$, ${}_TF$, $F$ and the series $(I - M_D)^{-1}$
-- statement:
--   Let $P$ be a transition matrix on a countable state space $S$, and let $T, D \subseteq S$. All quantities below are probabilities of events of the chain $\{X_n\}$ or expected numbers of visits, computed as sums over finite trajectories $\omega_0, \omega_1, \dots, \omega_n$ of their weights $P_{\omega_0\omega_1}\cdots P_{\omega_{n-1}\omega_n}$, and they take values in $[0, \infty]$.
--
--   1. **Powers of a submatrix and the series convention.** For a nonnegative matrix $M$ and $D \subseteq S$, $M_D = \{M_{ij} : i, j \in D\}$, $M_D^0 = I$ and $[M_D^{\nu+1}]_{ij} = \sum_{k \in D} [M_D^\nu]_{ik} M_{kj}$. Following the book's convention (p. 109), $(I - M_D)^{-1}$ denotes the series $\sum_{\nu \ge 0} M_D^\nu$, entrywise.
--   2. **Expected sojourn times** (p. 108). $[N_D]_{ij} = \sum_{n \ge 0} \mathrm P[X_n = j \;\&\; S_D \ge n \mid X_0 = i]$, where $S_D \ge n$ means $X_0, \dots, X_n \in D$: the expected time spent in $j$ before the first visit to a state outside $D$.
--   3. **Taboo transition probabilities** (p. 110). With $\tau = \inf\{n \ge 1 : X_n \in T\}$,
--   $${}_TP_{ij}(k) = \mathrm P[X_1 \notin T, \dots, X_{k-1} \notin T, X_k = j \mid X_0 = i],$$
--   so ${}_TP_{ij}(0) = \delta_{ij}$.
--   4. **Expected visits under taboo** (5.5). ${}_TR_{ij} = \sum_{n \ge 0} {}_TP_{ij}(n)$, the expected number of visits to $j$, starting from $i$, before the first visit to $T$. For $i \in T$, $j \in D$ these form the matrix ${}_TR_{TD}$, which records the expected numbers of visits to $D$ between two visits to $T$.
--   5. **First passage to $D$ under taboo of $T$** (5.18). With $\theta = \inf\{n \ge 1 : X_n \in D\}$,
--   $${}_TF_{ij} = \mathrm P[\theta = \delta_j \;\&\; \theta < \infty \;\&\; \theta < \tau \mid X_0 = i],$$
--   the probability of reaching $D$, after time $0$ and before the first passage to $T$, in state $j$. The same object with the two sets exchanged (taboo $D$, target $T$) is ${}_DF$.
--   6. **First passage probabilities** (p. 117). $F_{ij} = \mathrm P[\tau < \infty \;\&\; X_\tau = j \mid X_0 = i]$; for $i \in D$, $j \in T$ these form $F_{DT}$.
--
--   These are the objects related by Lemma 5.1.2, Theorems 5.2.1 and 5.2.3, Lemma 5.2.4 and Eqs. (5.11), (5.23).
--
--   **Formalization Note** Every quantity is an extended nonnegative real (`ℝ≥0∞`), so every series exists and an infinite expectation is $\infty$ rather than a junk value; the transition probabilities enter through `ENNReal.ofReal`. A matrix "on a subset" is a function on $S \times S$ of which only the entries indexed by that subset are meant; matrix products over a subset are sums over the subtype. $(I - M_D)^{-1}$ is always the series, never a matrix inverse. In the Lean, `tabooF P T D` is ${}_TF$ with taboo set $T$ and target $D$, so ${}_DF_{DT}$ is `tabooF P D T`; `firstPassageF P T` is $F$ for first passage to $T$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 108–117 (N_D p. 108; convention p. 109; ₜP_ij(k) p. 110; Eq. (5.5) p. 111; ₜf, ₜF and Eq. (5.18) p. 115; F_ij p. 117)

import Mathlib

namespace MatrixAnalytic.Taboo

noncomputable section

open scoped BigOperators ENNReal

/-!
The taboo quantities of Chapter 5, §§5.1–5.2 of Latouche & Ramaswami, for a Markov chain with
transition matrix `P` on a countable state space `S`. Every probability is a sum, over finite
trajectories, of products of one-step transition probabilities, and every expected number of
visits is a sum over time of such probabilities. All of them take values in `ℝ≥0∞`, so every sum
exists and an infinite expectation is `⊤`, never a junk value.

A matrix "on a subset `D`" is a function `S → S → ℝ≥0∞` of which only the entries with both
indices in `D` are meant; products of such matrices sum over the states of `D`.
-/

variable {S : Type*} [Countable S] [DecidableEq S]

/-- The transition matrix `P` with entries read in `ℝ≥0∞`. -/
def ennP (P : S → S → ℝ) : S → S → ℝ≥0∞ :=
  fun i j => ENNReal.ofReal (P i j)

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{n-1}ω_n}` of a trajectory of length `n`, in `ℝ≥0∞`: the
probability, starting from `ω₀`, that `X₁ = ω₁, …, X_n = ω_n`. -/
def pathWeightE (P : S → S → ℝ) {n : ℕ} (ω : Fin (n + 1) → S) : ℝ≥0∞ :=
  ∏ m : Fin n, ennP P (ω m.castSucc) (ω m.succ)

/-- Powers of the submatrix `M_D = {M_{ij} : i, j ∈ D}`: `[M_D^0]_{ij} = δ_{ij}` and
`[M_D^{ν+1}]_{ij} = Σ_{k ∈ D} [M_D^ν]_{ik} M_{kj}`. Only entries with `i, j ∈ D` are meant. -/
def subPow (M : S → S → ℝ≥0∞) (D : Set S) : ℕ → S → S → ℝ≥0∞
  | 0 => fun i j => if i = j then 1 else 0
  | ν + 1 => fun i j => ∑' k : D, subPow M D ν i (k : S) * M k j

/-- The book's convention of p. 109: `(I − M_D)⁻¹ := Σ_{ν ≥ 0} M_D^ν`, the series of powers of
the submatrix on `D`, entrywise in `ℝ≥0∞` (an entry is `⊤` exactly when its series diverges). -/
def seriesInv (M : S → S → ℝ≥0∞) (D : Set S) : S → S → ℝ≥0∞ :=
  fun i j => ∑' ν : ℕ, subPow M D ν i j

open Classical in
/-- `[N_D]_{ij}` (p. 108): the expected number of epochs `n ≥ 0` at which `X_n = j` while the
chain, started at `X_0 = i`, has stayed in `D` at all times `0, …, n` (i.e. `S_D ≥ n`), so
`[N_D]_{ij} = Σ_{n ≥ 0} P[X_n = j & S_D ≥ n | X_0 = i]`: the expected sojourn time in `j` before
the first visit to a state outside `D`. -/
def sojournN (P : S → S → ℝ) (D : Set S) (i j : S) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑' ω : Fin (n + 1) → S,
    if ω 0 = i ∧ ω (Fin.last n) = j ∧ ∀ m : Fin (n + 1), ω m ∈ D then pathWeightE P ω else 0

open Classical in
/-- The `k`-step taboo transition probability (p. 110)
`ₜP_{ij}(k) = P[X_1 ∉ T, …, X_{k-1} ∉ T, X_k = j | X_0 = i]`; for `k = 0` it is `δ_{ij}`. -/
def tabooP (P : S → S → ℝ) (T : Set S) (k : ℕ) (i j : S) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → S,
    if ω 0 = i ∧ ω (Fin.last k) = j ∧
        ∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → ω m ∉ T
    then pathWeightE P ω else 0

/-- `ₜR_{ij} = Σ_{n ≥ 0} ₜP_{ij}(n)` (5.5): the expected number of visits to `j`, starting from
`i`, before the first visit to `T` after time `0`. For `i ∈ T` and `j ∈ D` these are the entries of
the matrix `ₜR_{TD}`, which records the expected numbers of visits to `D` between two visits to
`T`. -/
def tabooR (P : S → S → ℝ) (T : Set S) (i j : S) : ℝ≥0∞ :=
  ∑' n : ℕ, tabooP P T n i j

open Classical in
/-- `ₜF_{ij} = P[θ = δ_j & θ < ∞ & θ < τ | X_0 = i]` (5.18), where `θ = inf{n ≥ 1 : X_n ∈ D}`
and `τ = inf{n ≥ 1 : X_n ∈ T}`: the probability, starting from `i`, of reaching `D` at some time
`θ ≥ 1` before the first passage to `T`, and of doing so in state `j`. It is the sum over
`n ≥ 1` of `ₜf_{ij}(n) = P[θ = n & θ < τ & X_θ = j | X_0 = i]` (p. 115). For `i, j ∈ D` these are
the entries of `ₜF_{DD}`; for `i ∈ T, j ∈ D` those of `ₜF_{TD}`. The roles of the two sets are
`tabooF P T D` = `ₜF` with taboo set `T` and target set `D`, so the book's `_DF_{DT}` is
`tabooF P D T`. -/
def tabooF (P : S → S → ℝ) (T D : Set S) (i j : S) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑' ω : Fin (n + 2) → S,
    if ω 0 = i ∧ ω (Fin.last (n + 1)) = j ∧ j ∈ D ∧ j ∉ T ∧
        ∀ m : Fin (n + 2), m ≠ 0 → m ≠ Fin.last (n + 1) → ω m ∉ D ∧ ω m ∉ T
    then pathWeightE P ω else 0

open Classical in
/-- The first passage probabilities to `T` (p. 117), `F_{ij} = P[τ < ∞ & X_τ = j | X_0 = i]`
with `τ = inf{n ≥ 1 : X_n ∈ T}`: the sum over `n ≥ 1` of the probabilities of the trajectories
`i = ω_0, ω_1, …, ω_n = j` with `ω_1, …, ω_{n-1} ∉ T` and `j ∈ T`. For `i ∈ D, j ∈ T` these are
the entries of `F_{DT}`. -/
def firstPassageF (P : S → S → ℝ) (T : Set S) (i j : S) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑' ω : Fin (n + 2) → S,
    if ω 0 = i ∧ ω (Fin.last (n + 1)) = j ∧ j ∈ T ∧
        ∀ m : Fin (n + 2), m ≠ 0 → m ≠ Fin.last (n + 1) → ω m ∉ T
    then pathWeightE P ω else 0

end

end MatrixAnalytic.Taboo


