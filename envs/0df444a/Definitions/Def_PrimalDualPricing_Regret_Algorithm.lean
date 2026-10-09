-- Prove2me | Definitions.Def_PrimalDualPricing_Regret_Algorithm
-- name    : PrimalDualPricing_Regret_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:21:49.439767+00:00
-- url     : https://prove2.me/theorems/9ae59e8e-fa33-4217-bd3d-572afdb78ebb
-- title:
--   Algorithm 1, pp. 9–12 — the primal-dual learning algorithm as a map from the Poisson paths to a price path
-- statement:
--   This file defines the primal-dual learning algorithm (Algorithm 1) as a deterministic map from the realized arrival paths to a piecewise-constant price path.
--
--   **Decision rules: only known data and observed counts.** The firm knows $T$, $c$, $n$, $\epsilon$ and the intervals $[\underline p,\overline p]$, $[0,\overline z]$ of Assumption 2. It starts with $[\underline p^{(1)}_m,\overline p^{(1)}_m]=[\underline p,\overline p]$ and $[\underline z^{(1)},\overline z^{(1)}]=[0,\overline z]$. In each phase $k\le K-1$ it proceeds as follows.
--
--   1. It charges the grid prices $p^{(k)}_{m,j}=\underline p^{(k)}_m+j\delta^{(k)}_m$, $j=0,\dots,N^{(k)}$, with $\delta^{(k)}_m=(\overline p^{(k)}_m-\underline p^{(k)}_m)/N^{(k)}$, each for a period of length $\tau^{(k)}/(N^{(k)}+1)$.
--   2. It records the counts $D^{(k)}_{m,j}$ and forms $\hat d^{(k)}_{m,j}=\frac{N^{(k)}+1}{n\tau^{(k)}}D^{(k)}_{m,j}$.
--   3. It computes
--   $$z^{(k)*}=\operatorname*{argmin}_{z\in\{\underline z^{(k)}+i\delta^{(k)}_z\}_{i=0}^{N^{(k)}_z}}\Big\{cz+T\sum_{m=1}^M\max_{j}\hat d^{(k)}_{m,j}\big(p^{(k)}_{m,j}-z\big)\Big\},\qquad \delta^{(k)}_z=\frac{\overline z^{(k)}-\underline z^{(k)}}{N^{(k)}_z+1},$$
--   and $p^{(k)*}_m=p^{(k)}_{m,j^*_m}$ with $j^*_m=\operatorname{argmax}_j\hat d^{(k)}_{m,j}(p^{(k)}_{m,j}-z^{(k)*})$. These are (8) and (9).
--   4. It sets the next intervals by (10): $\underline p^{(k+1)}_m=\max\{\underline p,p^{(k)*}_m-\bar\Delta^{(k+1)}/2\}$, $\overline p^{(k+1)}_m=\min\{\overline p,p^{(k)*}_m+\bar\Delta^{(k+1)}/2\}$, $\underline z^{(k+1)}=\max\{0,z^{(k)*}-\bar\Delta^{(k+1)}_z/2\}$, $\overline z^{(k+1)}=\min\{\overline z,z^{(k)*}+\bar\Delta^{(k+1)}_z/2\}$.
--
--   In the last phase $K$, starting at $t_K$, the firm acts as follows.
--   1. If $0\in[\underline z^{(K)},\overline z^{(K)}]$, it charges $\overline p^{(K)}_m+\alpha$ until $T$.
--   2. Otherwise, with $p^l_m=\underline p^{(K)}_m-\alpha$, $p^u_m=\overline p^{(K)}_m+\alpha$ and $L=(\log n)^{-\epsilon}$, it charges $p^l$ on $(t_K,t_K+L]$ and $p^u$ on $(t_K+L,t_K+2L]$. It records the aggregate sales rates $D^{(K)}_l$, $D^{(K)}_u$ of (12)–(13), which are the sales of those periods times $(\log n)^\epsilon$. It takes $\theta$ as the projection onto $[0,1]$ of the solution of (14),
--   $$(T-t_K)\big(\theta D^{(K)}_l+(1-\theta)D^{(K)}_u\big)=nc-S(t_K).$$
--   It then charges $p^l$ up to $t_K+\theta(T-t_K)+L$ and $p^u$ up to $T$ (lines 36–41).
--
--   **The closed loop.** Nature produces the counts by a time change of unit-rate Poisson paths $N_m$. If type $m$ has been charged the prices $P_m(s)$, its cumulative arrival intensity is $\Lambda_m(t)=n\int_0^t d_m(P_m(s))\,ds$, and its cumulative sales are $N_m(\Lambda_m(t))$. Only this step uses the demand functions.
--
--   **Formalization Note** The firm's rules (`nextIntervals`, `thetaRule`, `lastPhasePlan`) take no demand function, $\mathcal P_m$ or $z^*$ as argument. The price path is a list of segments $(a,b]$ with a constant price vector each, computed without truncation; the revenue ignores everything after $T$. The pages disagree on two grid spacings. The text (p. 9) and Table 1 give $\delta_m=\Delta_m/N$, while Algorithm 1 line 7 prints $\Delta_m/(N+1)$; $\Delta_m/N$ is used, so the price grid covers the interval. The text (p. 9) and line 15 give $\delta_z=\Delta_z/(N_z+1)$, while Table 1 prints $\Delta_z/N_z$; $\Delta_z/(N_z+1)$ is used. Ties in (8) and (9) go to the smallest grid index. In (14), when $D_l=D_u$ or $t_K=T$, Lean's $x/0=0$ gives $\theta=0$. When $\theta(T-t_K)<L$ the $p^l$ period of step 4 is empty, following the pseudo-code. Phases are 1-based; `stateAt k` is the state at the beginning of phase $k$.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, pp. 9–12, §3.2, Eqs. (8)–(14), Algorithm 1 (lines 1–42), Table 1 (p. 24)

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_Params

namespace PrimalDualPricing.Regret

/-! Algorithm 1 (the primal-dual learning algorithm) of Chen–Gallego (arXiv:1812.09234v3, §3.2,
pp. 9–12, with the parameters of §3.3, p. 13).

The file has two layers.

* **The firm's decision rules** (`Known`, `Intervals`, `nextIntervals`, `thetaRule`, `lastPhasePlan`):
  functions of the data the firm knows (`n`, `c`, `T`, `p̲`, `p̄`, `z̄`, `ε`; Algorithm 1 lines 1–3,
  Assumption 2) and of the **observed sales counts** only. None of them takes the demand functions,
  `𝒫_m` or `z*` as an argument.
* **The closed loop** (`stateAt`, `schedule`): the counts are produced by nature. Type `m` arrives as a
  unit-rate Poisson path `N m` run on the clock `Λ_m(t) = n ∫_0^t d_m(P_m(s)) ds` (time change), so the
  sales of type `m` in `(a, b]` are `N m (Λ_m(b)) − N m (Λ_m(a))`. Only this layer uses `d`.

The price path is a finite list of segments `(start, stop]` with a constant price vector on each.
Phases are 1-based (`k = 1, …, K`, `K = numPhases ε n`). The schedule is computed without truncation;
everything after `T` is ignored by the revenue (the season ends at `T`). -/

/-- The data the firm knows (p. 8, Algorithm 1 lines 1–2): the horizon `T`, the inventory `c`, and the
intervals `[p̲, p̄]`, `[0, z̄]` of Assumption 2. (`n`, `M` and `ε` are passed separately.) -/
structure Known where
  T : ℝ
  c : ℝ
  pLow : ℝ
  pHigh : ℝ
  zHigh : ℝ

/-- Interval estimators at the beginning of a phase: `[p̲_m^{(k)}, p̄_m^{(k)}]` for every type and
`[z̲^{(k)}, z̄^{(k)}]`. -/
structure Intervals (M : ℕ) where
  pLo : Fin M → ℝ
  pHi : Fin M → ℝ
  zLo : ℝ
  zHi : ℝ

/-- Initialization, Algorithm 1 line 4: `p̲_m^{(1)} = p̲`, `p̄_m^{(1)} = p̄`, `z̲^{(1)} = 0`, `z̄^{(1)} = z̄`. -/
def initIntervals {M : ℕ} (kn : Known) : Intervals M :=
  ⟨fun _ => kn.pLow, fun _ => kn.pHigh, 0, kn.zHigh⟩

/-- The price grid of phase `k` (p. 9): `p_{m,j}^{(k)} = p̲_m^{(k)} + j δ_m^{(k)}` with
`δ_m^{(k)} = Δ_m^{(k)} / N^{(k)}`, `Δ_m^{(k)} = p̄_m^{(k)} − p̲_m^{(k)}`, `j = 0, …, N^{(k)}` (text p. 9
and Table 1; Algorithm 1 line 7 prints `Δ/(N+1)`). -/
noncomputable def gridPrice {M : ℕ} (eps : ℝ) (n k : ℕ) (I : Intervals M) (m : Fin M) (j : ℕ) : ℝ :=
  I.pLo m + (j : ℝ) * ((I.pHi m - I.pLo m) / (gridN eps n k : ℝ))

/-- The dual grid of phase `k` (p. 9): `z̲^{(k)} + i δ_z^{(k)}` with `δ_z^{(k)} = Δ_z^{(k)}/(N_z^{(k)} + 1)`,
`Δ_z^{(k)} = z̄^{(k)} − z̲^{(k)}`, `i = 0, …, N_z^{(k)}` (text p. 9 and line 15; Table 1 prints `Δ_z/N_z`). -/
noncomputable def gridDual {M : ℕ} (eps : ℝ) (n k : ℕ) (I : Intervals M) (i : ℕ) : ℝ :=
  I.zLo + (i : ℝ) * ((I.zHi - I.zLo) / ((gridNz eps n k : ℝ) + 1))

/-- The demand estimate (p. 9, line 13): `d̂_{m,j}^{(k)} = (N^{(k)} + 1)/(n τ^{(k)}) · D_{m,j}^{(k)}`, where
`D m j` is the observed number of sales of type `m` while price `p_{m,j}^{(k)}` was charged. -/
noncomputable def demandEst {M : ℕ} (eps : ℝ) (n k : ℕ) (D : Fin M → ℕ → ℕ) (m : Fin M) (j : ℕ) : ℝ :=
  ((gridN eps n k : ℝ) + 1) / ((n : ℝ) * tau eps n k) * (D m j : ℝ)

/-- The empirical dual function of (8):
`c z + T ∑_m max_{j = 0, …, N^{(k)}} d̂_{m,j}^{(k)} (p_{m,j}^{(k)} − z)`. -/
noncomputable def empDual {M : ℕ} (kn : Known) (eps : ℝ) (n k : ℕ) (I : Intervals M)
    (D : Fin M → ℕ → ℕ) (z : ℝ) : ℝ :=
  kn.c * z + kn.T * ∑ m, (Finset.range (gridN eps n k + 1)).sup' ⟨0, by simp⟩
    (fun j => demandEst eps n k D m j * (gridPrice eps n k I m j - z))

open Classical in
/-- Tie-breaking for the grid argmin: the smallest index `j ∈ {0, …, N}` at which `f` attains its
minimum over `{0, …, N}` (the set is finite, so such an index exists). -/
noncomputable def firstArgmin (N : ℕ) (f : ℕ → ℝ) : ℕ :=
  if h : ∃ j, j ≤ N ∧ ∀ i, i ≤ N → f j ≤ f i then Nat.find h else 0

/-- Tie-breaking for the grid argmax: the smallest index in `{0, …, N}` maximizing `f`. -/
noncomputable def firstArgmax (N : ℕ) (f : ℕ → ℝ) : ℕ :=
  firstArgmin N (fun j => -f j)

/-- The point estimator `z^{(k)*}` of (8): the dual grid point minimizing the empirical dual function
(smallest index on ties). -/
noncomputable def dualEst {M : ℕ} (kn : Known) (eps : ℝ) (n k : ℕ) (I : Intervals M)
    (D : Fin M → ℕ → ℕ) : ℝ :=
  gridDual eps n k I
    (firstArgmin (gridNz eps n k) (fun i => empDual kn eps n k I D (gridDual eps n k I i)))

/-- The point estimators `p_m^{(k)*} = p_{m,j*_m}^{(k)}` of (9), with
`j*_m = argmax_j d̂_{m,j}^{(k)} (p_{m,j}^{(k)} − z^{(k)*})` (smallest index on ties). -/
noncomputable def priceEst {M : ℕ} (kn : Known) (eps : ℝ) (n k : ℕ) (I : Intervals M)
    (D : Fin M → ℕ → ℕ) (m : Fin M) : ℝ :=
  gridPrice eps n k I m
    (firstArgmax (gridN eps n k)
      (fun j => demandEst eps n k D m j * (gridPrice eps n k I m j - dualEst kn eps n k I D)))

/-- The interval estimators of phase `k + 1`, (10) (p. 10), from the counts `D` observed in phase `k`:
`p̲_m^{(k+1)} = max{p̲, p_m^{(k)*} − Δ̄^{(k+1)}/2}`, `p̄_m^{(k+1)} = min{p̄, p_m^{(k)*} + Δ̄^{(k+1)}/2}`,
`z̲^{(k+1)} = max{0, z^{(k)*} − Δ̄_z^{(k+1)}/2}`, `z̄^{(k+1)} = min{z̄, z^{(k)*} + Δ̄_z^{(k+1)}/2}`. -/
noncomputable def nextIntervals {M : ℕ} (kn : Known) (eps : ℝ) (n k : ℕ) (I : Intervals M)
    (D : Fin M → ℕ → ℕ) : Intervals M :=
  ⟨fun m => max kn.pLow (priceEst kn eps n k I D m - widthP n (k + 1) / 2),
   fun m => min kn.pHigh (priceEst kn eps n k I D m + widthP n (k + 1) / 2),
   max 0 (dualEst kn eps n k I D - widthZ eps n (k + 1) / 2),
   min kn.zHigh (dualEst kn eps n k I D + widthZ eps n (k + 1) / 2)⟩

/-- Step 3 of phase `K`, (14) (p. 11, line 35): `θ` is the projection onto `[0, 1]` of the solution of
`(T − t_K)(θ D_l + (1 − θ) D_u) = n c − S(t_K)`, i.e. of
`(n c − S(t_K) − (T − t_K) D_u) / ((T − t_K)(D_l − D_u))`. When the equation is degenerate
(`D_l = D_u` or `t_K = T`) Lean's `x / 0 = 0` gives `θ = 0`. -/
noncomputable def thetaRule (kn : Known) (n : ℕ) (tK Dl Du : ℝ) (S : ℕ) : ℝ :=
  max 0 (min 1 (((n : ℝ) * kn.c - (S : ℝ) - (kn.T - tK) * Du) / ((kn.T - tK) * (Dl - Du))))

/-- A segment of the price path: the price vector `price` is charged on the time interval
`(start, stop]`. -/
structure Segment (M : ℕ) where
  start : ℝ
  stop : ℝ
  price : Fin M → ℝ

/-- The length of `(s.start, s.stop] ∩ (−∞, t]` (zero if empty). -/
noncomputable def Segment.overlap {M : ℕ} (s : Segment M) (t : ℝ) : ℝ :=
  max 0 (min s.stop t - s.start)

/-- The segments of a learning phase `k ≤ K − 1` (lines 8–12): for `j = 0, …, N^{(k)}`, the price
`p_{m,j}^{(k)}` is charged to type `m` on `(t_k + j τ^{(k)}/(N^{(k)}+1), t_k + (j+1) τ^{(k)}/(N^{(k)}+1)]`. -/
noncomputable def phaseSegs {M : ℕ} (eps : ℝ) (n k : ℕ) (I : Intervals M) : List (Segment M) :=
  (List.range (gridN eps n k + 1)).map fun (j : ℕ) =>
    ⟨startTime eps n k + (j : ℝ) * tau eps n k / ((gridN eps n k : ℝ) + 1),
     startTime eps n k + ((j : ℝ) + 1) * tau eps n k / ((gridN eps n k : ℝ) + 1),
     fun m => gridPrice eps n k I m j⟩

/-- The cumulative intensity (clock) of type `m` at time `t` under the price segments `segs`:
`Λ_m(t) = n ∑_{segments} d_m(price_m) · |segment ∩ (0, t]| = n ∫_0^t d_m(P_m(s)) ds`. -/
noncomputable def clock {M : ℕ} (d : Fin M → ℝ → ℝ) (n : ℕ) (segs : List (Segment M)) (m : Fin M)
    (t : ℝ) : ℝ :=
  (segs.map fun s => (n : ℝ) * d m (s.price m) * s.overlap t).sum

/-- Cumulative (uncapped) sales of type `m` up to time `t`, `N_m(Λ_m(t))`, for one realization
`N : Fin M → ℝ → ℕ` of the `M` unit-rate Poisson paths. -/
noncomputable def salesOf {M : ℕ} (d : Fin M → ℝ → ℝ) (n : ℕ) (N : Fin M → ℝ → ℕ)
    (segs : List (Segment M)) (m : Fin M) (t : ℝ) : ℕ :=
  N m (clock d n segs m t)

/-- The algorithm's state at the beginning of a phase: the interval estimators and the price segments
charged so far. -/
structure AlgState (M : ℕ) where
  I : Intervals M
  segs : List (Segment M)

/-- The counts observed in phase `k`, started from state `st`: `D m j` is the number of type-`m` sales
during the `j`-th sub-interval of the phase (line 11). (Natural subtraction is exact here because sales
paths are nondecreasing.) -/
noncomputable def phaseCounts {M : ℕ} (d : Fin M → ℝ → ℝ) (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → ℕ)
    (k : ℕ) (st : AlgState M) : Fin M → ℕ → ℕ :=
  fun m j =>
    salesOf d n N (st.segs ++ phaseSegs eps n k st.I) m
        (startTime eps n k + ((j : ℝ) + 1) * tau eps n k / ((gridN eps n k : ℝ) + 1))
      - salesOf d n N (st.segs ++ phaseSegs eps n k st.I) m
        (startTime eps n k + (j : ℝ) * tau eps n k / ((gridN eps n k : ℝ) + 1))

/-- The state at the beginning of phase `k` (1-based; index `0` repeats the initial state):
`stateAt 1` is line 4, and phase `k` runs lines 6–18 to produce `stateAt (k + 1)`. -/
noncomputable def stateAt {M : ℕ} (kn : Known) (d : Fin M → ℝ → ℝ) (eps : ℝ) (n : ℕ)
    (N : Fin M → ℝ → ℕ) : ℕ → AlgState M
  | 0 => ⟨initIntervals kn, []⟩
  | 1 => ⟨initIntervals kn, []⟩
  | (k + 2) =>
    let st := stateAt kn d eps n N (k + 1)
    ⟨nextIntervals kn eps n (k + 1) st.I (phaseCounts d eps n N (k + 1) st),
     st.segs ++ phaseSegs eps n (k + 1) st.I⟩

/-- The segments of the last phase `K` (lines 20–42), given the interval estimators `I` at its
beginning `t_K` and the observations of its two test periods.

* If `0 ∈ [z̲^{(K)}, z̄^{(K)}]` (lines 21–24): price `p̄_m^{(K)} + α` on `(t_K, T]`.
* Otherwise (lines 25–41), with `p_m^l = p̲_m^{(K)} − α`, `p_m^u = p̄_m^{(K)} + α`, `L = (log n)^{−ε}`:
  `p^l` on `(t_K, t_K + L]`, `p^u` on `(t_K + L, t_K + 2L]`, then `p^l` up to
  `t_K + θ(T − t_K) + L` (an empty period if this is before `t_K + 2L`), then `p^u` up to `T`.

`θ` is passed in (it is `thetaRule` applied to the observations, see `schedule`). -/
noncomputable def lastPhasePlan {M : ℕ} (kn : Known) (eps : ℝ) (n K : ℕ) (I : Intervals M)
    (θ : ℝ) : List (Segment M) :=
  let tK := startTime eps n K
  let L := testLen eps n
  let α := markup eps n
  if I.zLo ≤ 0 ∧ 0 ≤ I.zHi then
    [⟨tK, max tK kn.T, fun m => I.pHi m + α⟩]
  else
    let e := max (tK + 2 * L) (tK + θ * (kn.T - tK) + L)
    [⟨tK, tK + L, fun m => I.pLo m - α⟩,
     ⟨tK + L, tK + 2 * L, fun m => I.pHi m + α⟩,
     ⟨tK + 2 * L, e, fun m => I.pLo m - α⟩,
     ⟨e, max e kn.T, fun m => I.pHi m + α⟩]

/-- The complete price path of Algorithm 1 with parameter `ε` in the `n`-th system, for one
realization `N` of the Poisson paths: the learning phases `1, …, K − 1` followed by phase `K`. In the
insufficient-capacity branch the aggregate sales rates
`D_l^{(K)} = (log n)^ε ∑_m (sales of type m in (t_K, t_K + L])` (12),
`D_u^{(K)} = (log n)^ε ∑_m (sales of type m in (t_K + L, t_K + 2L])` (13) and the cumulative sales
`S(t_K)` enter `θ` through `thetaRule`. -/
noncomputable def schedule {M : ℕ} (kn : Known) (d : Fin M → ℝ → ℝ) (eps : ℝ) (n : ℕ)
    (N : Fin M → ℝ → ℕ) : List (Segment M) :=
  let K := numPhases eps n
  let st := stateAt kn d eps n N K
  let tK := startTime eps n K
  let L := testLen eps n
  -- the two test periods do not depend on θ
  let test := st.segs ++ (lastPhasePlan kn eps n K st.I 0).take 2
  let Dl := Real.log n ^ eps *
    ∑ m, ((salesOf d n N test m (tK + L) : ℝ) - (salesOf d n N test m tK : ℝ))
  let Du := Real.log n ^ eps *
    ∑ m, ((salesOf d n N test m (tK + 2 * L) : ℝ) - (salesOf d n N test m (tK + L) : ℝ))
  let S := ∑ m, salesOf d n N test m tK
  st.segs ++ lastPhasePlan kn eps n K st.I (thetaRule kn n tK Dl Du S)

end PrimalDualPricing.Regret


