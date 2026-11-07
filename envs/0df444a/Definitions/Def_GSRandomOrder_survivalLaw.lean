-- Prove2me | Definitions.Def_GSRandomOrder_survivalLaw
-- name    : GSRandomOrder_survivalLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:00:42.140205+00:00
-- url     : https://prove2.me/theorems/97f01452-daf3-4422-9466-1da825afd730
-- title:
--   Survival law $\mu^u_{S,t}$: the law of the retained set of the thought experiment
-- statement:
--   Fix a valuation $u$, a set $S$ of items and a time $t\in[1/e,1]$, thought of as the set of items that have arrived by real time $t$. The **survival law** $\mu^u_{S,t}$ is the law of a random set $R\subseteq S$ produced by the following thought experiment.
--
--   1. *Reshuffle.* Give each $g\in S$ an independent timestamp $\tau_g$, uniform on $[0,t]$, and let $S_\tau=\{g\in S:\tau_g\le\tau\}$ be the set present at time $\tau\in[0,t]$. An item with $\tau_g\le 1/e$ is **early**.
--   2. *Replay.* The **death time** of an early item $g$ is the first time after $1/e$ at which it leaves the canonical demand of the items present, or $t$ if it never does:
--   $$
--   \sigma_g=\min\bigl(\{\tau\in[1/e,t]: g\notin D_u(S_\tau)\}\cup\{t\}\bigr).
--   $$
--   3. *Retain.* Given the timestamps, each early item $g$ is independently added to $R$ with probability $\ln(e\,\sigma_g)\in[0,1]$.
--
--   For $A\subseteq S$, $\mu^u_{S,t}(A)$ is the probability that $R=A$:
--   $$
--   \mu^u_{S,t}(A)=\mathbb E_\tau\Bigl[\prod_{g\in A}\theta_g\prod_{g\in S\setminus A}(1-\theta_g)\Bigr],\qquad \theta_g=\mathbf 1\{\tau_g\le 1/e\}\ln(e\,\sigma_g).
--   $$
--   The survival algorithm uses these laws for $u=v$ and for the contractions $u=v/x$.
--
--   **Formalization Note** The timestamps are $\tau_g=t\,r_g$ for $r$ uniform on $[0,1]^n$ (`volume` on `Fin n → unitInterval`), which gives i.i.d. $\mathrm{Unif}[0,t]$ timestamps; only the coordinates in $S$ are read. The minimum is `sInf` of a nonempty set bounded below; since present sets are right-continuous step functions of $\tau$, the infimum is attained. The expectation is a Bochner integral of a bounded measurable function. The value is $0$ when $A\not\subseteq S$. Helper definitions: the present set, the death time, the retention probability $\theta_g$, and the conditional probability of $R=A$ given the timestamps.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §3.2, p.10 (the thought experiment and the survival law)

import Mathlib
import Definitions.Def_GSRandomOrder_canonicalDemand

set_option autoImplicit false

open MeasureTheory

namespace GSRandomOrder

/-- The items of `S` whose timestamp is at most `s`: `S_s = {g ∈ S : τ_g ≤ s}`. -/
noncomputable def presentAt {n : ℕ} (S : Finset (Fin n)) (τ : Fin n → ℝ) (s : ℝ) :
    Finset (Fin n) :=
  S.filter fun g => τ g ≤ s

/-- The **death time** of an item `g` when the set of items present at time `s` is `P s`
(Paes Leme, Pál, Patel, STOC 2027 submission, manuscript sha256 69787f50…, §3.2 step 2, p.10;
§B.1 step 2, p.22): `σ_g = min({s ∈ [1/e, t] : g ∉ D_u(P s)} ∪ {t})`.

**Formalization Note.** The minimum is `sInf` of a set of reals that contains `t` and is bounded
below by `min(1/e, t)`, so the infimum is that of a nonempty bounded set. Present sets only grow
and change only at timestamps (they are right-continuous step functions of `s`), so the set
`{s ∈ [1/e, t] : g ∉ D_u(P s)}` is a finite union of intervals closed on the left and the
infimum is attained: it is the paper's minimum. `1/e` is `Real.exp (-1)`. -/
noncomputable def deathTime {n : ℕ} (u : Finset (Fin n) → WithBot ℝ)
    (P : ℝ → Finset (Fin n)) (t : ℝ) (g : Fin n) : ℝ :=
  sInf ({s ∈ Set.Icc (Real.exp (-1)) t | g ∉ canonicalDemand u (P s)} ∪ {t})

/-- The **retention probability** of an item `g` (§3.2 step 3, p.10; §B.1, p.22): `ln(e σ_g)`
if `g` is early (`τ_g ≤ 1/e`), and `0` otherwise. -/
noncomputable def retention {n : ℕ} (u : Finset (Fin n) → WithBot ℝ)
    (P : ℝ → Finset (Fin n)) (t : ℝ) (τ : Fin n → ℝ) (g : Fin n) : ℝ :=
  if τ g ≤ Real.exp (-1) then Real.log (Real.exp 1 * deathTime u P t g) else 0

/-- Given the timestamps, the probability that the retained set equals `A`:
`Π_{g ∈ A} θ_g · Π_{g ∈ S \ A} (1 − θ_g)` (the items are retained independently; cf. (18),
p.22). -/
noncomputable def retainProb {n : ℕ} (u : Finset (Fin n) → WithBot ℝ)
    (P : ℝ → Finset (Fin n)) (t : ℝ) (τ : Fin n → ℝ) (S A : Finset (Fin n)) : ℝ :=
  (∏ g ∈ A, retention u P t τ g) * ∏ g ∈ S \ A, (1 - retention u P t τ g)

/-- **Survival law** `μ^u_{S,t}` (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §3.2, p.10): the law of the retained
set `R ⊆ S` of the thought experiment.

1. *Reshuffle.* Each `g ∈ S` gets an independent timestamp `τ_g`, uniform on `[0, t]`;
   `S_τ = {g ∈ S : τ_g ≤ τ}`; an item with `τ_g ≤ 1/e` is *early*.
2. *Replay.* The death time of an early item is `σ_g = min({τ ∈ [1/e, t] : g ∉ D_u(S_τ)} ∪ {t})`.
3. *Retain.* Each early item is independently added to `R` with probability `ln(e σ_g)`.

`survivalLaw u S t A` is `μ^u_{S,t}(A) = P[R = A]`.

**Formalization Note.** The timestamps are rescaled uniforms: `τ_g = t · r_g` with
`r : Fin n → [0, 1]` distributed by the product of uniform laws (`volume` on
`Fin n → unitInterval`), which gives i.i.d. `Unif[0, t]` timestamps (only the coordinates in `S`
are read). The probability `P[R = A]` is the expectation over the timestamps of the conditional
probability `retainProb`, a finite product of bounded measurable functions of `r`, so the Bochner
integral is the genuine expectation. The value is `0` when `A ⊄ S`. The law is used for
`t ∈ [1/e, 1]`, for `u = v` and for the contractions `u = v/x`, with the same labels. -/
noncomputable def survivalLaw {n : ℕ} (u : Finset (Fin n) → WithBot ℝ) (S : Finset (Fin n))
    (t : ℝ) (A : Finset (Fin n)) : ℝ :=
  if A ⊆ S then
    ∫ r : Fin n → unitInterval,
      retainProb u (presentAt S fun g => t * (r g : ℝ)) t (fun g => t * (r g : ℝ)) S A
  else 0

end GSRandomOrder


