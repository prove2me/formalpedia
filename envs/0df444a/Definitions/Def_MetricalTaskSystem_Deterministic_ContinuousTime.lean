-- Prove2me | Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime
-- name    : MetricalTaskSystem_Deterministic_ContinuousTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:10:15.175099+00:00
-- url     : https://prove2.me/theorems/e50d1480-5dcd-4aa5-b14e-ed1ed463cf87
-- title:
--   Continuous-time schedules, on-line CTSAs and the off-line cost function $\varphi_t$
-- statement:
--   Task $T^i$ arrives at time $i$ and is processed during $[i,i+1)$. A **continuous-time schedule** for $T^1\cdots T^m$ is a map $\sigma:[1,m+1)\to S$ that changes state finitely often; the cost of processing $T^i$ is $\int_i^{i+1}T^i(\sigma(t))\,dt=\sum_s\lambda_sT^i(s)$, where $\lambda_s$ is the fraction of $[i,i+1)$ spent in state $s$, and the total cost is
--   $$\sum_{j=1}^k d(s_{j-1},s_j)+\sum_{i=1}^m\int_i^{i+1}T^i(\sigma(t))\,dt,$$
--   where $s_0,s_1,\dots,s_k$ are the states visited in order.
--
--   An **on-line continuous-time scheduling algorithm** (CTSA) schedules the interval $[i,i+1)$ upon receipt of $T^i$, as a function of $s_0$ and $T^1,\dots,T^i$.
--
--   For a time $t\ge1$ and a state $s$, the **off-line cost function** $\varphi_t(s)$ is the minimum cost of processing the tasks up to time $t$ with a continuous-time schedule started in $s_0$ at time $1$, subject to being in state $s$ at time $t$.
--
--   **Formalization Note** A CTSA is given in list form: on each unit interval it outputs a finite list of consecutive pieces $(\text{state},\text{length})$ with nonnegative lengths summing to $1$. Pieces of length $0$ (instantaneous visits) are allowed; by the triangle inequality they never lower a cost. The processing integral of the piecewise-constant task function is computed exactly as $\sum_i T^i(s)\cdot|[a,b]\cap[i,i+1]|$. The off-line cost function $\varphi_t(s)$ is a real infimum over piece lists covering $[1,t]$ and ending in $s$; for $t\ge1$ this set is nonempty and bounded below by $0$ (nonnegative tasks and costs).
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 751, Section 3 (continuous-time schedules, CTSA); p. 754, Section 6 (off-line cost function φ_t)

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model

namespace MetricalTaskSystem.Deterministic

/-- The total transition cost `Σ_j d(v_{j−1}, v_j)` along a finite walk `v₀, v₁, …, v_k`
(`0` for walks of length `0`). -/
def pathCost {S : Type} (d : S → S → ℝ) (l : List S) : ℝ :=
  (List.zipWith d l l.tail).sum

/-- Continuous-time processing cost (Section 3, p. 751) of staying in state `s` during the
time interval `[a, b]`, for the tasks `T¹ ⋯ Tᵐ` (index `i : Fin m` is `T^{i+1}`), where task
`T^{i+1}` is processed during `[i+1, i+2)`:
`∫_a^b T^{⌊t⌋}(s) dt = Σ_{i} T^{i+1}(s) · |[a, b] ∩ [i+1, i+2]|`.
It is `0` when `b ≤ a` and after time `m + 1`. -/
def proc {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (s : S) (a b : ℝ) : ℝ :=
  ∑ i : Fin m, T i s * max 0 (min b ((i : ℝ) + 2) - max a ((i : ℝ) + 1))

/-- An **on-line continuous-time scheduling algorithm** (CTSA, p. 751), in list form: upon
receipt of `Tⁱ`, it schedules the unit interval `[i, i+1)` as a finite list of consecutive
pieces `(state, length)`, as a function of `s₀` and `[T¹, …, Tⁱ]` only. -/
abbrev CTSA (S : Type) : Type := S → List (S → ℝ) → List (S × ℝ)

/-- Well-formedness of a CTSA: on every nonempty task prefix, the piece lengths are
nonnegative and sum to `1` (the pieces tile the unit interval). Pieces of length `0`
(instantaneous visits) are allowed. -/
def IsCTSA {S : Type} (A' : CTSA S) : Prop :=
  ∀ (s₀ : S) (l : List (S → ℝ)), l ≠ [] →
    (∀ p ∈ A' s₀ l, 0 ≤ p.2) ∧ ((A' s₀ l).map Prod.snd).sum = 1

/-- The pieces the CTSA `A'` produces on the unit interval `[i+1, i+2)`, i.e. upon receipt of
task `T^{i+1}` (index `i : Fin m`). -/
def ctsaPiecesAt {S : Type} (A' : CTSA S) (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) (i : Fin m) :
    List (S × ℝ) :=
  A' s₀ ((List.ofFn T).take ((i : ℕ) + 1))

/-- The total cost of the continuous-time schedule produced by the CTSA `A'` on `T¹ ⋯ Tᵐ`
from `s₀` (p. 751): the transition costs along the visited states (starting at `s₀`),
plus, for each task `Tⁱ`, the convex combination `Σ λ_s Tⁱ(s)` of its costs weighted by the
time spent in each state during `[i, i+1)`. -/
def ctsaCost {S : Type} (d : S → S → ℝ) (A' : CTSA S) (s₀ : S) {m : ℕ}
    (T : Fin m → S → ℝ) : ℝ :=
  pathCost d (s₀ :: (List.ofFn (fun i => ctsaPiecesAt A' s₀ T i)).flatten.map Prod.fst) +
    ∑ i : Fin m, ((ctsaPiecesAt A' s₀ T i).map (fun p => p.2 * T i p.1)).sum

/-- Processing cost of a list of consecutive pieces `(state, length)` started at time `a`:
the `j`-th piece occupies `[a_j, a_j + ℓ_j]` with `a_j = a + Σ_{j' < j} ℓ_{j'}`. -/
def piecesProc {S : Type} {m : ℕ} (T : Fin m → S → ℝ) : ℝ → List (S × ℝ) → ℝ
  | _, [] => 0
  | a, p :: P => proc T p.1 a (a + p.2) + piecesProc T (a + p.2) P

/-- A continuous-time off-line schedule of the time interval `[1, t]`, given as consecutive
pieces `(state, length)` with nonnegative lengths summing to `t − 1`, started from `s₀`,
and ending in state `s` (the last piece's state, or `s₀` if there is none). -/
def IsOfflinePieces {S : Type} (s₀ : S) (t : ℝ) (s : S) (P : List (S × ℝ)) : Prop :=
  (∀ p ∈ P, 0 ≤ p.2) ∧ (P.map Prod.snd).sum = t - 1 ∧ (P.map Prod.fst).getLastD s₀ = s

/-- The **off-line cost function** `φ_t(s)` (p. 754): the minimum cost of processing the task
sequence up to time `t`, given that the system is in state `s` at time `t` (continuous-time
schedules, starting in `s₀` at time `1`). For `t ≥ 1`, nonnegative tasks and nonnegative `d`,
the index set is nonempty (one piece `(s, t − 1)`) and the costs are bounded below by `0`,
so the real infimum is the true infimum. (For `t < 1` the index set is empty and the value
is `0`; it is used only for `t ≥ 1`.) -/
noncomputable def offlineCostTo {S : Type} (d : S → S → ℝ) (s₀ : S) {m : ℕ}
    (T : Fin m → S → ℝ) (t : ℝ) (s : S) : ℝ :=
  ⨅ P : {P : List (S × ℝ) // IsOfflinePieces s₀ t s P},
    pathCost d (s₀ :: P.1.map Prod.fst) + piecesProc T 1 P.1

end MetricalTaskSystem.Deterministic


