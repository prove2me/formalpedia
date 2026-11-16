-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_LowerBound
-- name    : MLAMaxDelay_RandomizedTimer_Supplement_LowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:52:11.022674+00:00
-- url     : https://prove2.me/theorems/fe243032-cd16-41c5-a9cd-8ef8a8d250e5
-- title:
--   Root-path cost and the (m, K) input distribution of Appendix A.2
-- statement:
--   For a vertex $v$ of a weighted rooted tree, $c=w(P(\rho,v))$ is the weight of its root path.
--
--   Fix integers $m,K\ge 2$, put $\delta=1/m$ and
--
--   $$g_j=\frac{jc}{m},\qquad p_j=\delta(1-\delta)^{j-1}\ (j=1,\dots,m),\qquad s_m=(1-\delta)^m,\qquad q_m=1-s_m .$$
--
--   The **(m, K) distribution** generates requests at $v$: the first at time $0$; after each of the first $K-1$ requests the next gap is $g_j$ with probability $p_j$, independently, or the input terminates with probability $s_m$; request $K$, if generated, terminates. A realisation with $L\le K-1$ gaps of indices $j_1,\dots,j_L$ has probability $\prod_i p_{j_i}$, times $s_m$ when $L<K-1$. Expectations are the corresponding finite weighted sums of $[0,\infty]$-valued functions of the realised input. Also
--
--   $$A_{m,K}=\sum_{i=0}^{K-1}q_m^i,\qquad B_{m,K}=q_m\sum_{i=0}^{K-2}q_m^i+q_m^{K-1}.$$
--
--   **Formalization Note** Gap indices are zero-based ($j:\mathrm{Fin}\,m$ is the source's $j+1$). The total mass of the distribution is a conclusion of Lemma A.3's item, not an assumption.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 18, Lemma A.1; p. 19, Section A.2, equations (31)–(32); p. 20, equations (35)–(36); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Timer

namespace MLAMaxDelay.RandomizedTimer.Supplement

open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `c = w(P(ρ, v))`: the weight of the root path of `v` (the rooted footprint of a single
request at `v`). -/
noncomputable def pathCost (T : WeightedTree V) (v : V) : ℝ := by
  classical
  exact spatialWeight T ({T.root} ∪ Finset.univ.filter
    (fun u => HarelTarjan.Compressed.IsAncestor T.toRootedTree u v))

/-- Structural: path costs are nonnegative (edge weights are). -/
theorem pathCost_nonneg (T : WeightedTree V) (v : V) : 0 ≤ pathCost T v := by
  classical
  unfold pathCost spatialWeight
  exact Finset.sum_nonneg (fun u hu => T.nonneg u (Finset.ne_of_mem_erase hu))

/-! Appendix A.2, p. 19, equation (31): the `(m, K)` input distribution at a node `v` of path
cost `c`. Gap indices are zero-based: `j : Fin m` is the source's index `j + 1`. -/

/-- `g_{j+1} = (j+1)c/m`. -/
noncomputable def gapLen (c : ℝ) (m : ℕ) (j : Fin m) : ℝ := ((j : ℕ) + 1) * c / m

/-- `p_{j+1} = δ(1−δ)^j` with `δ = 1/m`. -/
noncomputable def gapProb (m : ℕ) (j : Fin m) : ℝ := (1 / (m : ℝ)) * (1 - 1 / (m : ℝ)) ^ (j : ℕ)

/-- `s_m = (1−δ)^m`, the termination probability. -/
noncomputable def survival (m : ℕ) : ℝ := (1 - 1 / (m : ℝ)) ^ m

/-- `q_m = 1 − s_m`, equation (32). -/
noncomputable def qm (m : ℕ) : ℝ := 1 - survival m

/-- `A_{m,K} = Σ_{i=0}^{K−1} q_m^i`, equation (35). -/
noncomputable def gameA (m K : ℕ) : ℝ := ∑ i ∈ Finset.range K, qm m ^ i

/-- `B_{m,K} = q_m Σ_{i=0}^{K−2} q_m^i + q_m^{K−1}`, equation (36). -/
noncomputable def gameB (m K : ℕ) : ℝ := qm m * (∑ i ∈ Finset.range (K - 1), qm m ^ i) + qm m ^ (K - 1)

/-- The realized input after `L` gaps with indices `s`: requests `0, …, L` at `v`, request `k`
arriving at the sum of the first `k` gaps (request `0` at time `0`). -/
noncomputable def gameInput (T : WeightedTree V) (v : V) (m L : ℕ) (s : Fin L → Fin m) :
    Input V where
  requests := Finset.range (L + 1)
  arrival := fun k => ∑ i : Fin L, if (i : ℕ) < k then gapLen (pathCost T v) m (s i) else 0
  location := fun _ => v
  nonneg := by
    intro k _
    refine Finset.sum_nonneg (fun i _ => ?_)
    split_ifs
    · have := pathCost_nonneg T v
      unfold gapLen
      positivity
    · exact le_refl 0

/-- Probability of the realization `(L, s)`: independent gap choices `∏ p`, times the
termination probability `s_m` unless request `K` was generated (`L = K − 1`), which
terminates surely. -/
noncomputable def gameWeight (m K L : ℕ) (s : Fin L → Fin m) : ℝ :=
  (∏ i, gapProb m (s i)) * (if L + 1 < K then survival m else 1)

/-- Expectation over the finite-support `(m, K)` distribution of a `[0, ∞]`-valued function
of the realized input. -/
noncomputable def gameExpect (T : WeightedTree V) (v : V) (m K : ℕ)
    (f : Input V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ L ∈ Finset.range K, ∑ s : Fin L → Fin m,
    ENNReal.ofReal (gameWeight m K L s) * f (gameInput T v m L s)

/-- Total mass of the `(m, K)` distribution. -/
noncomputable def gameMass (m K : ℕ) : ℝ :=
  ∑ L ∈ Finset.range K, ∑ s : Fin L → Fin m, gameWeight m K L s

end MLAMaxDelay.RandomizedTimer.Supplement


