-- Prove2me | Definitions.Def_TTTSampling_alg3
-- name    : TTTSampling_alg3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:02.00431+00:00
-- url     : https://prove2.me/theorems/3d093780-c034-4372-bb8f-700c1feaa5e3
-- title:
--   Algorithm 3 (Particle Filtering with Learning): output law and number of oracle calls
-- statement:
--   **Algorithm 3** takes the constant $C_{\mathsf N}$, $R\ge1$, $\delta\in(0,1)$, the known finite class $\mathcal F$, the oracle $\hat\mu$, and a fixed string $x_0\in\Sigma^n$. With $\bar R,N,K$ as in Line 1:
--
--   1. for $k=1,\dots,K$: run the inner loop from $N$ copies of the empty sequence and $\mathcal F^1$ (Lines 3–10), set $\mathcal S^{\mathrm{term}}=\mathcal S^J$ (Lines 11–12), and with probability $\min\{1,|\mathcal S^{\mathrm{term}}|/(2RN)\}$ return a uniformly random element of the multiset $\mathcal S^{\mathrm{term}}$ (Line 13);
--   2. if no round returns, return $x_0$ (Line 14, "an arbitrary fixed element of $\Sigma^n$").
--
--   The definition gives the joint law of the returned string and of the **number of oracle calls**: the number of distinct nodes whose value $\hat\mu$ is obtained during the whole run, values being cached across all calls of Algorithms 2 and 3, the empty sequence excepted (its value is fixed to $1$ by convention).
--
--   **Formalization Note** The count follows the caching paragraph of p.18 and the proof of Lemma 3.15 ("the empty sequence, whose value $\hat\mu(\emptyset)=1$ is fixed by convention"). The uniform element of a multiset is drawn with multiplicity.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Algorithm 3, p.12 (PDF p.14); caching, p.18 (PDF p.20); proof of Lemma 3.15, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_TTTSampling_alg3Path

open Classical

namespace TTTSampling

/-- **One outer round `k` of Algorithm 3** (Lines 3–13) with incoming cache `Q`: run the inner
loop from the initial state, let `𝒮^term = 𝒮^J` (Lines 11–12), and with probability
`min{1, |𝒮^term|/(2RN)}` return a uniformly random element of `𝒮^term` (Line 13; uniform over the
multiset, i.e. with multiplicity). Output: the returned particle (`none` if the round returns
nothing) and the cache after the round. -/
noncomputable def alg3Round {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (C_N : ℕ) (R δ : ℝ)
    (F : Finset (PMF (Fin n → α))) (μh : List α → NNReal) (Q : Finset (List α)) :
    PMF (Option (List α) × Finset (List α)) :=
  (chain (alg3Step R μh) (pathLen C_N F.card R δ) (alg3Init C_N R δ F μh Q)).bind fun p =>
    (bern ((Multiset.card (sAt p (stopIdx p)) : ℝ) / (2 * R * (Npart C_N F.card R δ : ℝ)))).bind
      fun ξ =>
        if h : ξ = true ∧ sAt p (stopIdx p) ≠ 0 then
          (PMF.ofMultiset (sAt p (stopIdx p)) h.2).map (fun x => (some x, (stAt p (stopIdx p)).Q))
        else PMF.pure (none, (stAt p (stopIdx p)).Q)

/-- The outer loop `for 1 ≤ k ≤ K` of Algorithm 3 (Line 2): run rounds until one returns a
particle, carrying the cache across rounds (queries are cached across all calls, p.18). -/
noncomputable def alg3Rounds {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (C_N : ℕ) (R δ : ℝ)
    (F : Finset (PMF (Fin n → α))) (μh : List α → NNReal) :
    ℕ → Finset (List α) → PMF (Option (List α) × Finset (List α))
  | 0, Q => PMF.pure (none, Q)
  | k + 1, Q => (alg3Round C_N R δ F μh Q).bind fun r =>
      match r.1 with
      | some x => PMF.pure (some x, r.2)
      | none => alg3Rounds C_N R δ F μh k r.2

/-- A list of length `n` read as a string `Fin n → Σ` (any other list gives the default `x₀`). -/
def toStr {α : Type} {n : ℕ} (x₀ : Fin n → α) (x : List α) : Fin n → α :=
  if h : x.length = n then fun i => x.get ⟨i.1, h ▸ i.2⟩ else x₀

/-- **Algorithm 3 (Particle Filtering with Learning).**

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Algorithm 3, printed
p.12 (PDF p.14). Inputs: the constant `C_N`, the parameter `R ≥ 1`, the failure tolerance
`δ ∈ (0,1)`, the known class `ℱ`, the oracle `µ̂`, and the "arbitrary fixed element of Σⁿ" `x₀`
returned on Line 14 when no round returns a particle.

Output: the joint law of the returned string and of the **number of oracle calls**, counted as
the number of distinct nodes whose `µ̂`-value is obtained over the whole run, the empty sequence
excepted (its value `µ̂(∅) = 1` is fixed by convention, p.18 and p.30).

**Formalization Note**
* Queries are cached across all calls of Algorithms 2 and 3 (p.18), so the count is the size of
  the final cache, which starts as `{∅}`.
* The inner loop is `L = pathLen` iterations of `alg3Step` (see `alg3Path`), the outer loop `K`
  rounds (`Kreps`). -/
noncomputable def alg3 {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (C_N : ℕ) (R δ : ℝ)
    (F : Finset (PMF (Fin n → α))) (μh : List α → NNReal) (x₀ : Fin n → α) :
    PMF ((Fin n → α) × ℕ) :=
  (alg3Rounds C_N R δ F μh (Kreps R δ) {[]}).map fun r =>
    ((r.1.map (toStr x₀)).getD x₀, (r.2 \ {[]}).card)

end TTTSampling


