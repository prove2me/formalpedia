-- Prove2me | Definitions.Def_LostSalesConstantOrder_LargeLeadTime_RandomWalk
-- name    : LostSalesConstantOrder_LargeLeadTime_RandomWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:42.37477+00:00
-- url     : https://prove2.me/theorems/b234fb0e-89cb-4891-810d-0abc2cddb4f6
-- title:
--   The walk $kr-\sum_{i\le k}D_i$, its supremum $I^r_\infty$, its last maximizer $i^r_\infty$, the maxima $W^r_k$, $V_k$, the index $i^r_k$, and $\Theta_r$
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. demands with law $\mathcal D$ and $r\ge0$. The random walk
--   $$
--   S_k=kr-\sum_{i=1}^kD_i,\qquad k\ge0,
--   $$
--   has supremum $I^r_\infty=\sup_{k\ge0}S_k\in[0,\infty]$, the steady-state waiting time of the GI/D/1 queue with interarrival law $\mathcal D$ and constant service time $r$. Its law on $[0,\infty)$ is the image of the demand law (meaningful when $r<\mathbb E[D]$, where $I^r_\infty$ is finite almost surely).
--
--   The index $i^r_\infty$ is the largest index at which the walk attains its supremum: $i^r_\infty=j$ exactly when $S_\ell\le S_j$ for all $\ell\le j$ and $S_\ell<S_j$ for all $\ell>j$.
--
--   For $k\ge0$ and a value $I^r_{1,\infty}$ (a copy of $I^r_\infty$ independent of the demands),
--   $$
--   W^r_k=\max_{j=0,\dots,k}\Big(jr-\sum_{i=1}^jD_i+\delta_{j,k}I^r_{1,\infty}\Big),
--   $$
--   with $\delta_{j,k}=1$ if $j=k$ and $0$ otherwise, and $i^r_k$ is the largest $j\in[0,k]$ attaining $W^r_k$. For a pipeline $\mathbf x^*$ and an inventory $\mathcal I^*$,
--   $$
--   V_k=\max_{j=0,\dots,k}\Big(\sum_{i=k+1-j}^kx^*_i-\sum_{i=1}^jD_i+\delta_{j,k}\mathcal I^*\Big).
--   $$
--   Finally
--   $$
--   \Theta_r=\frac{(\mathbb E[D]-r)^2}{4(\mathbb E^2[D]+\mathbb E[D^2])}.
--   $$
--
--   These are the random-walk objects through which the cost of the constant-order policy (Lemma 4) and the lower bound on an optimal policy (Lemmas 6–7) are compared.
--
--   **Formalization Note** A demand path is $d:\mathbb N\to[0,\infty)$ with $d(i-1)=D_i$; sums keep the paper's indices. $I^r_\infty$ is valued in $[0,\infty]$, so the value $\infty$ is kept. Its law (`lawSupWalk`) sends $\infty$ to $0$, which affects nothing when $r<\mathbb E[D]$ (a null event) and is never used otherwise. When no last maximizer exists (a null event when $r<\mathbb E[D]$) `argmaxWalk` is $0$. $W^r_k$, $V_k$ and $i^r_k$ are functions of the value of $I^r_{1,\infty}$ (or $\mathcal I^*$) and the demand path; the independence of $I^r_{1,\infty}$ and the demands is imposed in the statements by integrating against the product of their laws. The measurability of the walk and its supremum is proved in the file.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 5 (§3.1, I^r_∞), p. 7 (§4.2, I^r_{1,∞}, W^r_k, i^r_k), p. 8 (V_k), p. 9 ((6), Θ_r), p. 16 (§9.1, i^r_∞)

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-!
Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, arXiv:1211.4063v2, §3.1 (p. 5), §4.2 (p. 7),
§5 (p. 8), (6) (p. 9), §9.1 (p. 16): the random walk `S_k = kr − Σ_{i=1}^k D_i`, its supremum
`I^r_∞`, its last maximizer `i^r_∞`, the finite maxima `W^r_k` and `V_k`, the last maximizer
`i^r_k` of `W^r_k`, and the constant `Θ_r`.

A demand path is `d : ℕ → ℝ≥0` and `d (i - 1)` is the paper's `D_i`; sums are written with the
paper's indices.
-/

/-- `S_k = k r − Σ_{i=1}^k D_i`. -/
def walk (r : ℝ≥0) (d : CappedBaseStock.DemandPath) (k : ℕ) : ℝ :=
  (k : ℝ) * r - ∑ i ∈ Finset.Icc 1 k, (d (i - 1) : ℝ)

/-- `I^r_∞ = sup_{k ≥ 0} (k r − Σ_{i=1}^k D_i)` (p. 5) in `[0, ∞]`: the value `∞` is kept (it is
the almost sure value when `r > E[D]`). `S_0 = 0`, so the supremum is nonnegative. -/
def supWalk (r : ℝ≥0) (d : CappedBaseStock.DemandPath) : ℝ≥0∞ :=
  ⨆ k : ℕ, ENNReal.ofReal (walk r d k)

/-- `j` is the last index at which the walk attains its supremum: `S_ℓ ≤ S_j` for `ℓ ≤ j` and
`S_ℓ < S_j` for `ℓ > j` (the events `𝓘₁ ∩ 𝓘₂ ∩ 𝓘′₃` of p. 16). At most one `j` qualifies. -/
def IsLastArgmax (r : ℝ≥0) (d : CappedBaseStock.DemandPath) (j : ℕ) : Prop :=
  (∀ ℓ ≤ j, walk r d ℓ ≤ walk r d j) ∧ ∀ ℓ, j < ℓ → walk r d ℓ < walk r d j

open Classical in
/-- `i^r_∞`, the (largest) index at which `sup_k S_k` is attained. When no such index exists
(the walk does not attain its supremum: a null event when `r < E[D]`) the value is `0`. -/
def argmaxWalk (r : ℝ≥0) (d : CappedBaseStock.DemandPath) : ℕ :=
  if h : ∃ j, IsLastArgmax r d j then Nat.find h else 0

/-- The law of `I^r_∞` on `ℝ≥0`, the pushforward of the i.i.d. demand law. The value `∞` is sent
to `0`; this matters only when `r ≥ E[D]`, where `I^r_∞` is not a finite random variable. -/
def lawSupWalk (P : CappedBaseStock.DemandLaw) (r : ℝ≥0) : Measure ℝ≥0 :=
  (CappedBaseStock.demandPathLaw P).map (fun d => (supWalk r d).toNNReal)

/-- The `j`-th term of `W^r_k`: `j r − Σ_{i=1}^j D_i + δ_{j,k} I^r_{1,∞}`. -/
def wTerm (r : ℝ≥0) (k : ℕ) (I₁ : ℝ≥0) (d : CappedBaseStock.DemandPath) (j : ℕ) : ℝ :=
  walk r d j + if j = k then (I₁ : ℝ) else 0

/-- `W^r_k = max_{j=0,…,k} (j r − Σ_{i=1}^j D_i + δ_{j,k} I^r_{1,∞})` (p. 7), as a function of the
value `I₁` of `I^r_{1,∞}` and the demand path. -/
def Wk (r : ℝ≥0) (k : ℕ) (I₁ : ℝ≥0) (d : CappedBaseStock.DemandPath) : ℝ :=
  (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one (wTerm r k I₁ d)

open Classical in
/-- `i^r_k = max{j* ∈ [0, k] : j* r − Σ_{i=1}^{j*} D_i + δ_{j*,k} I^r_{1,∞} = W^r_k}` (p. 7). -/
def ik (r : ℝ≥0) (k : ℕ) (I₁ : ℝ≥0) (d : CappedBaseStock.DemandPath) : ℕ :=
  ((Finset.range (k + 1)).filter (fun j => wTerm r k I₁ d j = Wk r k I₁ d)).sup id

/-- The `j`-th term of `V_k`: `Σ_{i=k+1−j}^k x*_i − Σ_{i=1}^j D_i + δ_{j,k} 𝓘*` (p. 8). -/
def vTerm {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) (d : CappedBaseStock.DemandPath)
    (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.Icc (k + 1 - j) k, (slot x (i - 1) : ℝ)) -
    (∑ i ∈ Finset.Icc 1 j, (d (i - 1) : ℝ)) + if j = k then (I : ℝ) else 0

/-- `V_k = max_{j=0,…,k} (Σ_{i=k+1−j}^k x*_i − Σ_{i=1}^j D_i + δ_{j,k} 𝓘*)` (p. 8). -/
def Vk {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) (d : CappedBaseStock.DemandPath) : ℝ :=
  (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one (vTerm x I k d)

/-- `Θ_r = (E[D] − r)² / (4(E²[D] + E[D²]))` (6), p. 9. -/
def theta (P : CappedBaseStock.DemandLaw) (r : ℝ) : ℝ :=
  (CappedBaseStock.mean P - r) ^ 2 / (4 * (CappedBaseStock.mean P ^ 2 + secondMoment P))

lemma measurable_walk (r : ℝ≥0) (k : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => walk r d k) := by
  unfold walk
  fun_prop

lemma measurable_supWalk (r : ℝ≥0) :
    Measurable (fun d : CappedBaseStock.DemandPath => supWalk r d) := by
  unfold supWalk
  exact Measurable.iSup (fun k => ENNReal.measurable_ofReal.comp (measurable_walk r k))

end LostSalesConstantOrder.LargeLeadTime


