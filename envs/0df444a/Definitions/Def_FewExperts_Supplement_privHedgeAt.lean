-- Prove2me | Definitions.Def_FewExperts_Supplement_privHedgeAt
-- name    : FewExperts_Supplement_privHedgeAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:52:32.53147+00:00
-- url     : https://prove2.me/theorems/13415f0a-7aca-43e7-a691-d89267dcd793
-- title:
--   Laplace noise, tree-based aggregation, private Hedge (Lemmas 3–4) and the sparse-vector test (Lemma 5)
-- statement:
--   Write $\mathrm{Lap}(b)$ for the mean-zero Laplace distribution with density $e^{-|x|/b}/(2b)$. The paper uses three standard private mechanisms, which it cites without restating them. This item fixes one standard instance of each.
--
--   1. **Tree-based aggregation** (Lemma 3). Let $H$ be a horizon and $\varepsilon_0>0$, and put $K=\lceil\log_2 H\rceil$ and $b=4\log H/\varepsilon_0$. Every dyadic block of rounds $[j2^k+1,(j+1)2^k]$ with $k<K$ carries an independent $\mathrm{Lap}(b)$ variable. At time $t$ the prefix $[1,t-1]$ is the disjoint union of the dyadic blocks given by the binary digits of $t-1$. The released estimate is
--   $$\widehat S_t=\sum_{s=1}^{t-1}x_s+\sum_{k<K}Z_{t,k},$$
--   where $Z_{t,k}$ is the variable of the level-$k$ block when bit $k$ of $t-1$ is set, and a fresh $\mathrm{Lap}(b)$ variable otherwise. The errors of all times are therefore identically distributed, each a sum of exactly $K\le 4\log H$ independent $\mathrm{Lap}(b)$ variables.
--   2. **Private Hedge** (Lemma 4). Given $n$ gain streams $x_1,\dots,x_n$, take one independent tree per stream. The prediction at round $t$ is the exponential-weights vector with learning rate $\eta=\sqrt{\ln n/H}$ (the rate of Lemma 2), computed on the noisy prefix sums:
--   $$w_t(j)=\frac{\exp(\eta\,\widehat S_{j,t})}{\sum_k\exp(\eta\,\widehat S_{k,t})}.$$
--   3. **Sparse vector** (Lemma 5). This is AboveThreshold [DR14, Algorithm 1] applied to the queries $(f_j-\tau_j)/c$ with threshold $0$. The instance draws $\rho\sim\mathrm{Lap}(2/\varepsilon_{\mathrm{sv}})$ once, and each query draws a fresh $\nu_j\sim\mathrm{Lap}(4/\varepsilon_{\mathrm{sv}})$. Query $j$ is answered true iff $(f_j-\tau_j)/c+\nu_j\ge\rho$, and the instance stops at its first true answer.
--
--   These are the noise sources of the private algorithm of Theorem 5.
--
--   **Formalization Note** Laplace variables are inverse-CDF transforms `lapInv b u` of uniform variables $u\in[0,1]$. `treeNoise` adds the noise of the $K$ levels, using the block's variable or a padding variable. `privHedgeAt` reuses the published `hedgeWeights` and `hedgeRate`. `svFires` is the test of one query; the callers stop at the first true answer.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §3.3, Lemmas 3–5, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_FewExperts_alpha
import Definitions.Def_FewExperts_hedgeWeights

namespace FewExperts.Supplement

/-- The inverse CDF of the mean-zero Laplace law `Lap(b)` (density `e^{−|x|/b}/(2b)`), §3.3, p.14:
`lapInv b u = b ln(2u)` for `u < 1/2` and `−b ln(2(1 − u))` for `u ≥ 1/2`. If `u` is uniform on
`[0, 1]` and `b > 0`, then `lapInv b u` has law `Lap(b)`.

**Formalization Note** At `u = 0` and `u = 1` (a null event) Lean's `Real.log 0 = 0` gives `0`. -/
noncomputable def lapInv (b u : ℝ) : ℝ :=
  if u < 1 / 2 then b * Real.log (2 * u) else -(b * Real.log (2 * (1 - u)))

/-- The number of dyadic levels of a binary tree over the horizon `H`: `K = ⌈log₂ H⌉`, so that
`2^K ≥ H` and every prefix `[1, n]` with `n < H` is a disjoint union of dyadic blocks of levels
`< K`. -/
def treeLevels (H : ℕ) : ℕ := Nat.clog 2 H

/-- The noise scale `4 log H / ε₀` of the tree-based aggregation of Lemma 3 (p.14), logs base 2. -/
noncomputable def treeScale (H : ℕ) (ε₀ : ℝ) : ℝ := 4 * lg H / ε₀

/-- The noise of the tree-based aggregation at time `t` (Lemma 3, p.14, [AS17]).
The node `(k, j)` of the binary tree is the dyadic block of rounds `[j 2^k + 1, (j + 1) 2^k]` and
carries the Laplace variable `lapInv b (node k j)`. For `n = t − 1`, the prefix `[1, n]` is the
disjoint union, over the bits `k` set in `n`, of the blocks `(k, ⌊n/2^k⌋ − 1)`. The noise at time
`t` adds, for each level `k < ⌈log₂ H⌉`, the Laplace variable of that block if bit `k` of `n` is
set, and a fresh Laplace variable `lapInv b (pad t k)` otherwise.

**Formalization Note** The padding makes the errors of all times identically distributed, each the
sum of exactly `⌈log₂ H⌉ ≤ 4 log H` independent `Lap(4 log H/ε₀)` variables, as Lemma 3 states;
each round lies in exactly `⌈log₂ H⌉` blocks, so the released sums are `ε₀`-differentially private
(for `H ≥ 2`). This is the instance of Lemma 3 the formalization pins (the paper only cites it). -/
noncomputable def treeNoise (H : ℕ) (ε₀ : ℝ) (node : ℕ → ℕ → unitInterval)
    (pad : ℕ → ℕ → unitInterval) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (treeLevels H),
    lapInv (treeScale H ε₀)
      (if (t - 1).testBit k then (node k ((t - 1) / 2 ^ k - 1) : ℝ) else (pad t k : ℝ))

/-- **Private Hedge (Lemma 4, p.14)**: its prediction at round `t ≥ 1` on the gain streams `x j u`
(`j` a stream, `u ≥ 1` a round), horizon `H` and privacy parameter `ε₀`.
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Lemma 3 and Lemma 4, p.14 (PDF 15), [AS17, Theorem 3.4 and Corollary 3.2].

Each stream `j` has its own independent tree (`node j`, `pad j`): the released estimate of the
prefix sum `∑_{u=1}^{t−1} x_j(u)` is that sum plus `treeNoise`, and the prediction is the Hedge
weights `hedgeWeights η` with the rate `η = √(ln n / H)` of Lemma 2 on these estimates.

**Formalization Note** The paper only cites Lemmas 3–4; this pins a standard instance (binary tree
with padding, Hedge on the noisy prefix sums). The algorithm reads the gains only through the
released noisy prefix sums, one tree per stream. -/
noncomputable def privHedgeAt {n : ℕ} (H : ℕ) (ε₀ : ℝ) (x : Fin n → ℕ → ℝ)
    (node : Fin n → ℕ → ℕ → unitInterval) (pad : Fin n → ℕ → ℕ → unitInterval) (t : ℕ) :
    Fin n → ℝ :=
  hedgeWeights (hedgeRate n H)
    (fun j => ∑ u ∈ Finset.Ico 1 t, x j u + treeNoise H ε₀ (node j) (pad j) t)

/-- **The sparse vector mechanism's test (Lemma 5, p.14–15)**: AboveThreshold [DR14, Algorithm 1]
applied to the query `(f − τ)/c` with threshold `0` and privacy parameter `ε_sv`. With
`ρ ~ Lap(2/ε_sv)` drawn once per instance (`rho`) and fresh `ν ~ Lap(4/ε_sv)` per query (`nu`), the
query answers true iff `(f − τ)/c + ν ≥ ρ`; the instance stops at its first true answer (the
callers stop querying it). -/
def svFires (εsv c : ℝ) (rho nu : unitInterval) (f τ : ℝ) : Prop :=
  lapInv (2 / εsv) rho ≤ (f - τ) / c + lapInv (4 / εsv) nu

end FewExperts.Supplement


