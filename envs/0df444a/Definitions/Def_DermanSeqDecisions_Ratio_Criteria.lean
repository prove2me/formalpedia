-- Prove2me | Definitions.Def_DermanSeqDecisions_Ratio_Criteria
-- name    : DermanSeqDecisions_Ratio_Criteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:22:46.645355+00:00
-- url     : https://prove2.me/theorems/1314c93d-98bd-4078-ad70-7704dca271a1
-- title:
--   Signed expected costs $W_t$, average cost $Q_R(i)$, ratio criterion $\psi_R(i)$, Assumption A and the class $C'$
-- statement:
--   This file sets up the cost criteria of Derman (1962) on top of the Markov decision chain of Sennott's model: a finite set $S$ of states (Derman's $0, \dots, L$), a finite set of decisions (Derman's $d_1, \dots, d_K$), all available in every state, and transition probabilities $q_{ij}(k)$. A **procedure** $\theta$ (Derman's class $C$) chooses the decision at time $t$ at random, with probabilities that may depend on the whole history $X_0, \Delta_0, \dots, X_t$.
--
--   1. **Expected cost at time $t$.** For a real cost function $c = (c_{ik})$ of either sign, a procedure $\theta$ and an initial state $i$ (so $X_0 = i$ with probability one),
--   $$W_t = E_\theta\big[c(X_t, \Delta_t) \mid X_0 = i\big] = \sum_{h} P_\theta(h \mid X_0 = i)\, c(i_t, a_t),$$
--   the sum running over all state-decision histories $h = ((i_0,a_0), \dots, (i_t,a_t))$ of length $t+1$.
--   2. **Average expected cost per unit time** (Problem 1, p. 17):
--   $$Q_\theta(i) = \limsup_{T\to\infty} \frac1T \sum_{t=0}^{T} W_t .$$
--   3. **Ratio criterion** (§4, p. 23). For two cost sets $w'$ and $w''$ with expected costs $W'_t$ and $W''_t$ under the same procedure,
--   $$\psi_\theta(i) = \limsup_{T\to\infty} \frac{\sum_{t=0}^{T} W'_t}{\sum_{t=0}^{T} W''_t}.$$
--   4. **Induced transition matrix.** For a stationary randomized rule $D = (D_{ik})$, $p_{ij} = \sum_k q_{ij}(k) D_{ik}$.
--   5. **Assumption A** (§3, p. 20): for every stationary randomized rule $D$ ($D_{ik} \ge 0$, $\sum_k D_{ik} = 1$) the matrix $(p_{ij})$ is irreducible, i.e. all states belong to the same class.
--   6. **The class $C'$** (p. 17): a procedure is stationary randomized with probabilities $D$ if it picks decision $k$ in state $s$ with probability $D_{sk}$, whatever the past and the time.
--
--   These are the objects of Derman's Theorem 3 and of the steps of its proof.
--
--   **Formalization Note** The cost functions are explicit real arguments; the nonnegative cost field of Sennott's model plays no role. $W_t$ is a finite sum over length-$(t+1)$ histories, so no infinite-sum default value arises. $Q$ keeps Derman's normalization ($T+1$ terms divided by $T$); the sequences are bounded, so the real limit superior is the genuine one. Every theorem using $\psi$ assumes $w' > 0$ and $w'' > 0$, which makes its denominator positive. Irreducibility is Mathlib's `Matrix.IsIrreducible` (a path of positive length between every ordered pair of states).
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 17 (classes C′, C″, costs, Problem 1), p. 20 (Assumption A), p. 23 (§4, ψ_R(i))

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- Derman's expected cost `W_t` at time `t` for a real cost function `c = (w_ik)`
(Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962),
DOI 10.1287/mnsc.9.1.16, §1, p. 17).

Under the procedure `θ` started at `X₀ = i`, `W_t = E_θ[c(X_t, Δ_t) | X₀ = i]`. A history up to
time `t` is a map `h : Fin (t+1) → S × Act`, read **most recent first** as in Sennott's model:
`h 0 = (X_t, Δ_t)`, …, `h t = (X₀, Δ₀)`; so `List.ofFn h` is the history list of `histProb`, and
`c (h 0)` is the cost of the last pair.

**Formalization Note.** The sum is a finite `Finset` sum over all length-`(t+1)` histories, so no
`tsum` junk value can occur. `histProb θ i (List.ofFn h)` is a product of numbers in `[0, 1]`, hence
finite, and `.toReal` is exact. The cost `c` is an explicit real argument of either sign; the cost
field `M.C` of Sennott's `MDC` plays no role. For `c = fun s a => (M.C s a : ℝ)` this is
`(expCost θ i t).toReal`. -/
noncomputable def expCostR {S Act : Type*} [Fintype S] [Fintype Act] {M : MDC S Act}
    (θ : Policy M) (i : S) (c : S → Act → ℝ) (t : ℕ) : ℝ :=
  ∑ h : Fin (t + 1) → S × Act, (histProb θ i (List.ofFn h)).toReal * c (h 0).1 (h 0).2

/-- Derman's long-run average expected cost per unit time for the cost `c`
(§1, p. 17, Problem 1):
`Q_θ(i) = lim sup_{T → ∞} (1/T) ∑_{t=0}^{T} W_t`.

**Formalization Note.** Derman's own normalization (`T + 1` terms divided by `T`) is kept; the
term at `T = 0` (where Lean's `1/0 = 0`) does not affect the `limsup`. The sequence is bounded
(`|W_t| ≤ max |c|` on the finite set `S × Act`), so the real `limsup` is the genuine one. -/
noncomputable def avgCostR {S Act : Type*} [Fintype S] [Fintype Act] {M : MDC S Act}
    (θ : Policy M) (i : S) (c : S → Act → ℝ) : ℝ :=
  Filter.limsup (fun T : ℕ => (1 / (T : ℝ)) * ∑ t ∈ Finset.range (T + 1), expCostR θ i c t)
    Filter.atTop

/-- Derman's ratio-of-costs criterion (§4, p. 23):
`ψ_θ(i) = lim sup_{T → ∞} (∑_{t=0}^{T} W′_t) / (∑_{t=0}^{T} W″_t)`, where `W′_t`, `W″_t` are the
expected costs at time `t` for the cost sets `w′`, `w″` under the same procedure `θ` from
`X₀ = i`. It is the `limsup` of the ratio, not the ratio of the `limsup`s.

**Formalization Note.** Every theorem using `ratioCost` assumes `w′ > 0` and `w″ > 0`, as §4
does; then the denominator is at least `(T + 1) · min w″ > 0` and the ratio lies in
`[min w′ / max w″, max w′ / min w″]`, so the real `limsup` is genuine. -/
noncomputable def ratioCost {S Act : Type*} [Fintype S] [Fintype Act] {M : MDC S Act}
    (θ : Policy M) (i : S) (w' w'' : S → Act → ℝ) : ℝ :=
  Filter.limsup (fun T : ℕ => (∑ t ∈ Finset.range (T + 1), expCostR θ i w' t) /
    (∑ t ∈ Finset.range (T + 1), expCostR θ i w'' t)) Filter.atTop

/-- The transition matrix `p_ij = ∑_k q_ij(k) D_ik` of the Markov chain induced by a
stationary randomized decision rule `D` (§1, p. 17), with `q_ij(k) = M.P i k j`. -/
noncomputable def inducedMatrix {S Act : Type*} [Fintype S] [Fintype Act] (M : MDC S Act)
    (D : S → Act → ℝ) : Matrix S S ℝ :=
  fun s j => ∑ a, (M.P s a j).toReal * D s a

/-- Derman's **Assumption A** (§3, p. 20): "for every `R ∈ C′` the states `0, ⋯, L` belong to
the same class". For every stationary randomized rule `D` (`D_ik ≥ 0`, `∑_k D_ik = 1`), the
induced transition matrix is irreducible (one communicating class).

**Formalization Note.** All decisions are available in every state, so every such `D` is a
procedure of `C′`. `Matrix.IsIrreducible` asks for a positive-length path between every ordered
pair of states; for a stochastic matrix this is exactly "all states communicate" (a one-state
chain has `p_00 = 1`). -/
def AssumptionA {S Act : Type*} [Fintype S] [Fintype Act] (M : MDC S Act) : Prop :=
  ∀ D : S → Act → ℝ, (∀ s a, 0 ≤ D s a) → (∀ s, ∑ a, D s a = 1) →
    (inducedMatrix M D).IsIrreducible

/-- A procedure `θ` belongs to Derman's class `C′` with decision probabilities `D`
(§1, p. 17): `P(Δ_t = d_k | X₀, Δ₀, ⋯, X_t = s) = D_sk`, independent of the past and of `t`. -/
def IsStationaryRandomized {S Act : Type*} [Fintype S] {M : MDC S Act} (θ : Policy M)
    (D : S → Act → ℝ) : Prop :=
  ∀ past s a, θ.prob past s a = ENNReal.ofReal (D s a)

end DermanSeqDecisions.Ratio


